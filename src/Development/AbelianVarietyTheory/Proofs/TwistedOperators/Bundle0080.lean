module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetSinhcAdjointUpperRightCoordEqPolJ
section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable def pCoord (p q : ℕ) : (Fin p → Fin q → ℂ) →+ (PIx p q → ℂ) where
  toFun C := fun ab => pY C ab.1.1 ab.1.2
  map_zero' := by
    funext ⟨⟨a, b⟩, h⟩
    cases a <;> cases b <;> simp [pY, pOf]
  map_add' B C := by funext ab; simp [pY_add]

theorem pCoord_apply {p q : ℕ} (C : Fin p → Fin q → ℂ) (ab : PIx p q) :
    pCoord p q C ab = pY C ab.1.1 ab.1.2 := rfl

private lemma pY_inl_inr {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inl i) (Sum.inr j) = C i j := by
  simp [pY, pOf]

private lemma pY_inr_inl {p q : ℕ} (C : Fin p → Fin q → ℂ) (i : Fin p) (j : Fin q) :
    pY C (Sum.inr j) (Sum.inl i) = star (C i j) := by
  simp [pY, pOf]

private lemma pY_eq_zero_of_sameBlock {p q : ℕ} (C : Fin p → Fin q → ℂ) (a b : Ix p q)
    (h : sameBlock a b) : pY C a b = 0 := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock, pY, pOf]

private lemma not_sameBlock_inl_inr {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inl i : Ix p q) (Sum.inr j) := by
  simp [sameBlock]

private lemma not_sameBlock_inr_inl {p q : ℕ} (i : Fin p) (j : Fin q) :
    ¬ sameBlock (Sum.inr j : Ix p q) (Sum.inl i) := by
  simp [sameBlock]

theorem det_sinhc_eq_polarJacobian (p q : ℕ) (Y : Mat p q)
    (hY : ∀ C : Fin p → Fin q → ℂ, sAd Y (pY C) = pY (sP Y C)) :
    LinearMap.det (sP Y) = polJ Y := by

  set M : Matrix (PIx p q) (PIx p q) ℂ :=
    (sinhcAd Y).submatrix (Subtype.val : PIx p q → Ix p q × Ix p q) Subtype.val with hM

  have hj : ∀ (t : ℝ) (x : Fin p → Fin q → ℂ), pCoord p q (t • x) = (t : ℂ) • pCoord p q x := by
    intro t x
    funext ab
    simp only [pCoord_apply, pY_smul, Pi.smul_apply, Matrix.smul_apply, Complex.real_smul,
      smul_eq_mul]

  have hspan : ∀ w : PIx p q → ℂ, ∃ a b : Fin p → Fin q → ℂ,
      w = pCoord p q a + Complex.I • pCoord p q b := by
    intro w
    let u : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
    let v : Fin p → Fin q → ℂ := fun i j => w ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
    refine ⟨fun i j => (u i j + star (v i j)) / 2,
      fun i j => -Complex.I * (u i j - star (v i j)) / 2, ?_⟩
    funext ⟨⟨a, b⟩, h⟩
    rcases a with i | j <;> rcases b with j' | i'
    · exact absurd (by simp [sameBlock]) h
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inl_inr]
      apply Complex.ext <;> simp [u] <;> ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pCoord_apply, pY_inr_inl]
      apply Complex.ext <;> simp [v] <;> ring
    · exact absurd (by simp [sameBlock]) h

  have hinj : ∀ a b : Fin p → Fin q → ℂ,
      pCoord p q a + Complex.I • pCoord p q b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h1 : ∀ i j, a i j + Complex.I * b i j = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inl i, Sum.inr j), not_sameBlock_inl_inr i j⟩
      simpa [pCoord_apply, pY_inl_inr] using this
    have h2 : ∀ i j, star (a i j) + Complex.I * star (b i j) = 0 := fun i j => by
      have := congrFun hab ⟨(Sum.inr j, Sum.inl i), not_sameBlock_inr_inl i j⟩
      simpa [pCoord_apply, pY_inr_inl] using this
    have hre : ∀ i j, a i j = 0 ∧ b i j = 0 := by
      intro i j
      have e1 := congrArg Complex.re (h1 i j)
      have e2 := congrArg Complex.im (h1 i j)
      have e3 := congrArg Complex.re (h2 i j)
      have e4 := congrArg Complex.im (h2 i j)
      simp at e1 e2 e3 e4
      constructor <;> apply Complex.ext <;> simp <;> linarith
    exact ⟨funext fun i => funext fun j => (hre i j).1,
      funext fun i => funext fun j => (hre i j).2⟩

  have hS : ∀ x, Matrix.toLin' M (pCoord p q x) = pCoord p q (sP Y x) := by
    intro x
    funext ab
    rw [Matrix.toLin'_apply, pCoord_apply, ← hY x]
    simp only [sAd, Matrix.of_apply, Matrix.mulVec, dotProduct, vecM, hM,
      Matrix.submatrix_apply, pCoord_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun cd : Ix p q × Ix p q => ¬ sameBlock cd.1 cd.2)]
    have hz : ∑ cd : {cd : Ix p q × Ix p q // ¬ ¬ sameBlock cd.1 cd.2},
        sinhcAd Y (ab.1.1, ab.1.2) cd.1 * pY x cd.1.1 cd.1.2 = 0 := by
      apply Finset.sum_eq_zero
      intro cd _
      rw [pY_eq_zero_of_sameBlock x _ _ (not_not.mp cd.2), mul_zero]
    rw [hz, add_zero]
  have key := det_complexification (Fin p → Fin q → ℂ) (PIx p q → ℂ) (pCoord p q) (sP Y)
    (Matrix.toLin' M) hj hspan hinj hS
  rw [LinearMap.det_toLin'] at key
  unfold polJ
  rw [← hM, key, Complex.ofReal_re]

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBiinvariantProbabilityOnCompactSubgroup
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory

theorem exists_biinvariant_probability_on_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (K : Subgroup G), IsCompact (K : Set G) → ∃ mK : Measure G, IsProbabilityMeasure mK ∧ mK (K : Set G)ᶜ = 0 ∧ (∀ k ∈ K, Measure.map (fun x => k * x) mK = mK) ∧ ∀ k ∈ K, Measure.map (fun x => x * k) mK = mK := by
  intro G _ _ _ _ _ _ _ K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : BorelSpace K := Subtype.borelSpace (fun x => x ∈ (K : Set G))
  let μ : Measure K := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨by
    have := Measure.haarMeasure_self (G := K) (K₀ := ⊤)
    simpa using this⟩
  have : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  have hv : Measurable (Subtype.val : K → G) := measurable_subtype_coe
  have hKm : MeasurableSet (K : Set G) := hK.isClosed.measurableSet
  refine ⟨μ.map Subtype.val, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hKm.compl]
    have : (Subtype.val : K → G) ⁻¹' (K : Set G)ᶜ = ∅ := by
      ext x; simp
    rw [this]; simp
  · intro k hk
    rw [Measure.map_map (measurable_const_mul k) hv]
    have h1 : μ.map (fun x : K => (⟨k, hk⟩ : K) * x) = μ := map_mul_left_eq_self μ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl
  · intro k hk
    rw [Measure.map_map (measurable_mul_const k) hv]
    have h1 : μ.map (fun x : K => x * (⟨k, hk⟩ : K)) = μ := by
      have : (μ.map (fun x : K => x * (⟨k, hk⟩ : K))).IsHaarMeasure :=
        Measure.isHaarMeasure_map_mul_right μ _
      exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
    conv_rhs => rw [← h1]
    rw [Measure.map_map hv (measurable_mul_const _)]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLog
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarLogCont

section
open scoped Matrix.Norms.L2Operator ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]

def halfLog (g : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℝ) • CFC.log (gᴴ * g)

theorem continuousOn_halfLog : ContinuousOn (halfLog (n := n)) {g | IsUnit g} := by
  have h : ContinuousOn (fun g : Matrix n n ℂ => CFC.log (gᴴ * g)) {g | IsUnit g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    have hu : IsUnit g := hg
    refine ⟨?_, ?_⟩
    · show star (gᴴ * g) = gᴴ * g
      rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    · exact (show IsUnit gᴴ from hu.star).mul hu
  exact h.const_smul (1 / 2 : ℝ)

theorem halfLog_mul_exp (c Y : Matrix n n ℂ) (hc : cᴴ * c = 1) (hY : Yᴴ = Y) :
    halfLog (c * NormedSpace.exp Y) = Y := by
  have he : (NormedSpace.exp Y)ᴴ = NormedSpace.exp Y := by
    rw [← Matrix.exp_conjTranspose, hY]
  have h2 : NormedSpace.exp (Y + Y) = NormedSpace.exp Y * NormedSpace.exp Y :=
    Matrix.exp_add_of_commute _ _ (Commute.refl Y)
  have sq : (c * NormedSpace.exp Y)ᴴ * (c * NormedSpace.exp Y) = NormedSpace.exp (Y + Y) := by
    rw [conjTranspose_mul, he, h2]
    calc NormedSpace.exp Y * cᴴ * (c * NormedSpace.exp Y)
        = NormedSpace.exp Y * (cᴴ * c) * NormedSpace.exp Y := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hc, Matrix.mul_one]
  have hsa : IsSelfAdjoint (Y + Y) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_add, hY]
  unfold halfLog
  rw [sq, CFC.log_exp _ hsa, ← two_smul ℝ Y, smul_smul]
  norm_num

end

theorem exists_continuousOn_polar_log : ∀ (p q : ℕ), ∃ L : Mat p q → (Fin p → Fin q → ℂ), ContinuousOn L {g | IsUnit g} ∧ ∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B := by
  intro p q
  refine ⟨fun g i j => halfLog g (Sum.inl i) (Sum.inr j), ?_, ?_⟩
  · have hc : Continuous fun (M : Mat p q) (i : Fin p) (j : Fin q) => M (Sum.inl i) (Sum.inr j) := by
      fun_prop
    exact hc.comp_continuousOn continuousOn_halfLog
  · intro k B hk
    funext i j
    show halfLog (k * NormedSpace.exp (pY B)) (Sum.inl i) (Sum.inr j) = B i j
    rw [halfLog_mul_exp k _ hk (pY_conjTranspose B)]
    simp [pY, pOf]

end GlobalTheory.PolarLogCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulMinorPoly
section
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem sum_Ici_sub_succ {n : ℕ} (α : ℕ → ℕ) (hα : Antitone α) (h0 : α n = 0) (a : Fin n) :
    ∑ i ∈ Finset.Ici a, (α (i : ℕ) - α ((i : ℕ) + 1)) = α a := by
  have key : ∀ k, ∑ i ∈ Finset.Ico (a : ℕ) (a + k), (α i - α (i + 1)) + α (a + k) = α a := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
      have := hα (Nat.le_succ (a + k))
      simp only [Nat.succ_eq_add_one] at this
      omega
  have h1 := key (n - a)
  rw [show (a : ℕ) + (n - a) = n by have := a.2; omega, h0, add_zero] at h1
  rw [← h1]
  refine Finset.sum_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Ici, Fin.le_def] at hi
    exact Finset.mem_Ico.2 ⟨hi, i.2⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro b hb
    rw [Finset.mem_Ico] at hb
    exact ⟨⟨b, hb.2⟩, Finset.mem_Ici.2 (Fin.le_def.2 hb.1), rfl⟩
  · intro _ _
    rfl

theorem exists_eq_mul_minorPoly (σ : Type) [DecidableEq σ] (p r : ℕ) (z : Fin p × Fin r → σ)
    (hz : Function.Injective z) (α : ℕ → ℕ) (hα : Antitone α) (h0 : ∀ i, min p r ≤ i → α i = 0)
    (P : MvPolynomial σ ℂ) (hP : BlockHW z α P) :
    ∃ Q : MvPolynomial σ ℂ, (∀ w, z w ∉ Q.vars) ∧ P = Q * minorPoly z α := by
  by_cases hP0 : P = 0
  · exact ⟨0, by simp, by simp [hP0]⟩
  obtain ⟨hru, hcu, hrw, hcw⟩ := hP
  have hrow : ∀ a : Fin p, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = α a := fun a m hm => by
    exact_mod_cast (rowOp_eq_smul_iff z a P _).1 (hrw a) m hm
  have hcol : ∀ k : Fin r, ∀ m ∈ P.support, ∑ a, m (z (a, k)) = α k := fun k m hm => by
    exact_mod_cast (colOp_eq_smul_iff z k P _).1 (hcw k) m hm
  let e : Fin (min p r) → Fin p := Fin.castLE (min_le_left p r)
  let f : Fin (min p r) → Fin r := Fin.castLE (min_le_right p r)
  have hei : Function.Injective e := Fin.castLE_injective _
  have hfi : Function.Injective f := Fin.castLE_injective _
  have hve : ∀ a k, a ∉ Set.range e → z (a, k) ∉ P.vars := by
    intro a k ha hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hrow a m hm
    rw [h0 a (not_lt.1 fun h' => ha ⟨⟨a, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 k (Finset.mem_univ _))
  have hvf : ∀ a k, k ∉ Set.range f → z (a, k) ∉ P.vars := by
    intro a k hk hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    have h1 := hcol k m hm
    rw [h0 k (not_lt.1 fun h' => hk ⟨⟨k, h'⟩, rfl⟩), Finset.sum_eq_zero_iff] at h1
    exact Finsupp.mem_support_iff.1 hv (h1 a (Finset.mem_univ _))
  obtain ⟨Q, hQ, hPQ⟩ := eq_mul_prod_minors (fun w : Fin (min p r) × Fin (min p r) =>
      z (e w.1, f w.2)) (hz.comp (hei.prodMap hfi)) P (fun i => α i - α (i + 1))
    (fun a m hm => by
      rw [sum_Ici_sub_succ α hα (h0 _ le_rfl)]
      refine Eq.trans ?_ (hrow (e a) m hm)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      by_contra h1
      exact hvf _ k hk ((mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h1⟩))
    (fun i j hij => by
      have h₁ := (rowOp_apply _ _ _ _).symm.trans (hru (e i) (e j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e i, f k)) (fun k => z (e j, f k))
        (fun k l h => hfi (by simpa using hz h))
        (fun k l h => hij.ne (hei (congrArg Prod.fst (hz h)))) P).out 3 2).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective f hfi _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hvf _ k hk), mul_zero])
    (fun i j hij => by
      have h₁ := (colOp_apply _ _ _ _).symm.trans (hcu (f i) (f j) hij)
      refine ((rowAdd_invariant_iff (fun k => z (e k, f i)) (fun k => z (e k, f j))
        (fun k l h => hei (by simpa using hz h))
        (fun k l h => hij.ne (hfi (congrArg Prod.snd (hz h)))) P).out 3 2).1 (Eq.trans ?_ h₁)
      refine Fintype.sum_of_injective e hei _ _ (fun k hk => ?_) fun _ => rfl
      rw [pderiv_eq_zero_of_notMem_vars (hve k _ hk), mul_zero])
  have hPQ' : P = Q * minorPoly z α := hPQ
  refine ⟨Q, ?_, hPQ'⟩
  have hsub : ∀ s ∈ Q.vars, s ∈ P.vars := by
    intro s hs
    rw [mem_vars_iff_degreeOf_ne_zero] at hs ⊢
    rw [hPQ'] at hP0 ⊢
    rw [degreeOf_mul_eq (left_ne_zero_of_mul hP0) (right_ne_zero_of_mul hP0)]
    omega
  rintro ⟨a, k⟩ hw
  by_cases ha : a ∈ Set.range e
  · by_cases hk : k ∈ Set.range f
    · obtain ⟨a, rfl⟩ := ha
      obtain ⟨k, rfl⟩ := hk
      exact hQ (a, k) hw
    · exact hvf a k hk (hsub _ hw)
  · exact hve a k ha (hsub _ hw)

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnP
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

private theorem jpq_eq_diagonal' (p q : ℕ) : Formalism.UG.Jpq p q =
    Matrix.diagonal (Sum.elim (fun _ : Fin p => (1 : ℂ)) (fun _ : Fin q => (-1 : ℂ))) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

private theorem mul_jpq_comm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) :
    X * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * X := by
  rw [jpq_eq_diagonal']
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · simp [hX (Sum.inl a) (Sum.inr b) (by simp [sameBlock])]
  · simp [hX (Sum.inr a) (Sum.inl b) (by simp [sameBlock])]
  · simp

private theorem Jpq_mul_Jpq_mul (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [jpq_eq_diagonal', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i <;> simp

private theorem exists_UJ_umat_eq_of_inUJ {p q : ℕ} (g : Mat p q) (hg : gᴴ * Formalism.UG.Jpq p q * g = Formalism.UG.Jpq p q)
    (hK : IsKC g) : gᴴ * g = 1 := by
  calc gᴴ * g = gᴴ * g * (Formalism.UG.Jpq p q * Formalism.UG.Jpq p q) := by rw [Jpq_mul_Jpq_mul, Matrix.mul_one]
    _ = gᴴ * (g * Formalism.UG.Jpq p q) * Formalism.UG.Jpq p q := by simp only [Matrix.mul_assoc]
    _ = gᴴ * Formalism.UG.Jpq p q * g * Formalism.UG.Jpq p q := by rw [mul_jpq_comm_of_isKC g hK]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jpq_mul_Jpq_mul]

private theorem unitary_inv_of_unitary {n : Type} [Fintype n] [DecidableEq n] (u : GL n ℂ)
    (hu : (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) = 1) :
    ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 := by
  have h1 : ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) = (u : Matrix n n ℂ)ᴴ := by
    calc ((u⁻¹ : GL n ℂ) : Matrix n n ℂ)
        = (u : Matrix n n ℂ)ᴴ * (u : Matrix n n ℂ) * ((u⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          rw [hu, Matrix.one_mul]
      _ = (u : Matrix n n ℂ)ᴴ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h1, Matrix.conjTranspose_conjTranspose, ← h1]
  exact Units.mul_inv u

private theorem conjTranspose_mul_self_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) : (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, Matrix.one_mul, hB]

private theorem pY_mem_upq {p q : ℕ} (B : Fin p → Fin q → ℂ) : pY B ∈ upq p q := by
  show (pY B)ᴴ * Jm p q + Jm p q * pY B = 0
  rw [show Jm p q = Formalism.UG.Jpq p q from rfl, jpq_eq_diagonal']
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [pY, pOf, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]

private theorem eq_pY_of_mem_pR {p q : ℕ} (Y : Mat p q) (hYm : Y ∈ pR p q) :
    Y = pY (fun i j => Y (Sum.inl i) (Sum.inr j)) := by
  have h2 : Y ∈ upq p q ∧ IsPC Y := hYm
  have hY : Yᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * Y = 0 := h2.1
  have hP : ∀ a b, sameBlock a b → Y a b = 0 := h2.2
  rw [jpq_eq_diagonal'] at hY
  ext a b
  rcases a with i | i <;> rcases b with j | j
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]
  · simp [pY, pOf]
  · have h := congrArg (fun M : Mat p q => M (Sum.inr i) (Sum.inl j)) hY
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply] at h
    simp only [pY, pOf, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply, Matrix.of_apply]
    linear_combination -h
  · rw [hP _ _ (by simp [sameBlock])]
    simp [pY, pOf]

theorem exists_action_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  intro p q T L hLc hL hdec g
  have hexp : ∀ X ∈ upq p q, ((T.cov (T.expt X) : GL _ ℂ) : Mat p q) = NormedSpace.exp X := T.16
  have hec : ContinuousOn T.expt (upq p q) := T.17
  have hcov : Continuous fun x : T.G => ((T.cov x : GL _ ℂ) : Mat p q) :=
    Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)
  have hKu : ∀ k ∈ T.Kset, ((T.cov k : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    exact exists_UJ_umat_eq_of_inUJ ((T.cov k : GL _ ℂ) : Mat p q) (T.cov_mem k) hk
  have hKinv : ∀ k ∈ T.Kset,
      ((T.cov k⁻¹ : GL _ ℂ) : Mat p q)ᴴ * ((T.cov k⁻¹ : GL _ ℂ) : Mat p q) = 1 := by
    intro k hk
    rw [map_inv]
    exact unitary_inv_of_unitary _ (hKu k hk)
  have hev : ∀ u : T.G, ((T.cov u : GL _ ℂ) : Mat p q)ᴴ * ((T.cov u : GL _ ℂ) : Mat p q) = 1 →
      ∀ C, L ((T.cov (u * T.expt (pY C)) : GL _ ℂ) : Mat p q) = C := by
    intro u hu C
    rw [map_mul, Units.val_mul, hexp _ (pY_mem_upq C)]
    exact hL _ C hu
  have hkey : ∀ h : T.G, ∃ k ∈ T.Kset,
      h = k * T.expt (pY (L ((T.cov h : GL _ ℂ) : Mat p q))) := by
    intro h
    obtain ⟨k, hk, Y, hY, rfl⟩ := hdec h
    obtain ⟨C, hC⟩ : ∃ C, Y = pY C := ⟨_, eq_pY_of_mem_pR Y hY⟩
    subst hC
    exact ⟨k, hk, by rw [hev k (hKu k hk) C]⟩
  refine ⟨fun B => L ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q), ?_, ?_, ?_⟩
  · have hof : Continuous fun B : Fin p → Fin q → ℂ => (Matrix.of B : Matrix (Fin p) (Fin q) ℂ) :=
      continuous_matrix fun i j => by simp only [Matrix.of_apply]; fun_prop
    have hpY : Continuous fun B : Fin p → Fin q → ℂ => pY B := by
      simp only [pY, pOf]
      exact Continuous.matrix_fromBlocks continuous_const hof hof.matrix_conjTranspose continuous_const
    have hE : Continuous fun B : Fin p → Fin q → ℂ => T.expt (pY B) :=
      hec.comp_continuous hpY pY_mem_upq
    have hM : Continuous fun B : Fin p → Fin q → ℂ =>
        ((T.cov (T.expt (pY B) * g) : GL _ ℂ) : Mat p q) :=
      hcov.comp (hE.mul continuous_const)
    exact hLc.comp_continuous hM (fun B => (T.cov _).isUnit)
  · constructor
    · intro B1 B2 h12
      dsimp only at h12
      obtain ⟨k1, hk1, e1⟩ := hkey (T.expt (pY B1) * g)
      obtain ⟨k2, hk2, e2⟩ := hkey (T.expt (pY B2) * g)
      rw [← h12] at e2
      generalize L ((T.cov (T.expt (pY B1) * g) : GL _ ℂ) : Mat p q) = C at e1 e2
      have f1 := eq_mul_inv_of_mul_eq e1
      have f2 := eq_mul_inv_of_mul_eq e2
      have e3 : T.expt (pY B1) = (k1 * k2⁻¹) * T.expt (pY B2) := by
        rw [f1, f2]
        group
      have hB1 : L ((T.cov (1 * T.expt (pY B1)) : GL _ ℂ) : Mat p q) = B1 := hev 1 (by simp) B1
      have hB2 : L ((T.cov ((k1 * k2⁻¹) * T.expt (pY B2)) : GL _ ℂ) : Mat p q) = B2 :=
        hev _ (by rw [map_mul, Units.val_mul]; exact conjTranspose_mul_self_mul_eq_one _ _ (hKu k1 hk1) (hKinv k2 hk2)) B2
      rw [one_mul, e3] at hB1
      exact hB1.symm.trans hB2
    · intro C
      obtain ⟨k, hk, e⟩ := hkey (T.expt (pY C) * g⁻¹)
      refine ⟨L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q), ?_⟩
      dsimp only
      generalize L ((T.cov (T.expt (pY C) * g⁻¹) : GL _ ℂ) : Mat p q) = B at e ⊢
      have f := eq_inv_mul_of_mul_eq e.symm
      have e' : T.expt (pY B) * g = k⁻¹ * T.expt (pY C) := by
        rw [f]
        group
      rw [e']
      exact hev _ (hKinv k hk) C
  · intro B
    exact hkey (T.expt (pY B) * g)

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryQuotientStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_module_quotient_of_invariant_inner : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∃ (A : UGKMod p q) (f : M.V →ₗ[ℂ] A.M.V) (Eb : A.M.V →ₗ[ℂ] H), Function.Surjective f ∧ Function.Injective Eb ∧ (∀ x, Eb (f x) = E x) ∧ ∀ Z x, f (M.act Z x) = A.M.act Z (f x) := by
  first | exact @GlobalTheory.GKQuot.exists_unitary_quotient | exact GlobalTheory.GKQuot.exists_unitary_quotient | (intros; apply GlobalTheory.GKQuot.exists_unitary_quotient <;> assumption)
end

