module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Step

section Blocks
variable {r : ℕ} {E : Type} [Field E]

theorem embHom_castSucc_castSucc (M : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.castSucc b) = M a b := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_castSucc_last (M : Matrix (Fin r) (Fin r) E) (a : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.last r) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_castSucc (M : Matrix (Fin r) (Fin r) E) (b : Fin r) :
    embHom r E M (Fin.last r) (Fin.castSucc b) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]

theorem embHom_last_last (M : Matrix (Fin r) (Fin r) E) :
    embHom r E M (Fin.last r) (Fin.last r) = 1 := by
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, hb]

theorem eq_embHom_of_last (h : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hc : ∀ i, h i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hr : ∀ j, h (Fin.last r) j = if j = Fin.last r then 1 else 0) :
    h = embHom r E (h.submatrix Fin.castSucc Fin.castSucc) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [embHom_last_last, hr]; simp
    | cast b => rw [embHom_last_castSucc, hr]; simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [embHom_castSucc_last, hc]; simp [Fin.castSucc_ne_last]
    | cast b => rw [embHom_castSucc_castSucc]; rfl

end Blocks

end GlobalTheory.JR.Step

namespace GlobalTheory.JR.Step

section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

theorem actU_liftH_support {r : ℕ} (X : Hn r F E) (ν : E) (l : F) (hν : ‖ν‖ = 1)
    (g : Matrix.unitaryGroup (Fin (r + 1)) E)
    (hg : unitU (r + 1) F E (actU g (liftH X ν l)) ≠ 0) :
    ∃ k ∈ uO (r + 1) E, ∃ s, g = k * uEmb r E s := by
  have hmem := Set.mem_of_indicator_ne_zero hg
  have hv : ∀ i, ‖(g.1 *ᵥ (ν • eL r E)) i‖ ≤ 1 := hmem.2.1
  set v : Fin (r + 1) → E := fun i => g.1 i (Fin.last r) with hvdef
  have hgv : g.1 *ᵥ eL r E = v := by
    funext i; simp [eL, Matrix.mulVec_single_one, v]
  have hint : ∀ i, ‖v i‖ ≤ 1 := by
    intro i
    have := hv i
    rw [Matrix.mulVec_smul, hgv, Pi.smul_apply, smul_eq_mul, norm_mul, hν, one_mul] at this
    exact this
  have hunit : star v ⬝ᵥ v = 1 := by
    have h1 : (star g.1 * g.1) (Fin.last r) (Fin.last r) = 1 := by
      rw [Matrix.mem_unitaryGroup_iff'.mp g.2]; simp
    rw [← h1]
    simp [dotProduct, Matrix.mul_apply, v, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  obtain ⟨k, hk, hke⟩ := _root_.GlobalTheory.UnitaryTransitive.uO_transitive F E r v hint hunit
  set h := k⁻¹ * g with hh
  have he : h.1 *ᵥ eL r E = eL r E := by
    have hgk : g.1 *ᵥ eL r E = k.1 *ᵥ eL r E := by rw [hgv]; exact hke.symm
    have hk1 : (k⁻¹).1 = star k.1 := rfl
    calc h.1 *ᵥ eL r E = star k.1 *ᵥ (g.1 *ᵥ eL r E) := by
          rw [Matrix.mulVec_mulVec, ← hk1]; rfl
      _ = star k.1 *ᵥ (k.1 *ᵥ eL r E) := by rw [hgk]
      _ = eL r E := by rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp k.2, Matrix.one_mulVec]
  have hse : star h.1 *ᵥ eL r E = eL r E := by
    conv_lhs => rw [← he]
    rw [Matrix.mulVec_mulVec, Matrix.mem_unitaryGroup_iff'.mp h.2, Matrix.one_mulVec]
  have hc : ∀ i, h.1 i (Fin.last r) = if i = Fin.last r then 1 else 0 := by
    intro i
    have := congrFun he i
    simpa [eL, Matrix.mulVec_single_one, Pi.single_apply] using this
  have hr : ∀ j, h.1 (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j
    have h0 := congrArg star (congrFun hse j)
    simp only [eL, Matrix.mulVec_single_one, Pi.single_apply, Matrix.star_eq_conjTranspose] at h0
    have h3 : star ((h.1)ᴴ.col (Fin.last r) j) = h.1 (Fin.last r) j := by
      simp [Matrix.col, Matrix.conjTranspose_apply]
    rw [← h3, h0]
    split_ifs <;> simp
  set S := h.1.submatrix Fin.castSucc Fin.castSucc with hSdef
  have hS : h.1 = embHom r E S := eq_embHom_of_last h.1 hc hr
  have hstar : star (embHom r E S) = embHom r E (star S) := by
    simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one]
  have h1 : embHom r E (S * star S) = 1 := by
    rw [map_mul, ← hstar, ← hS]; exact Matrix.mem_unitaryGroup_iff.mp h.2
  have hSu : S ∈ Matrix.unitaryGroup (Fin r) E := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    have h2 := congrFun (congrFun h1 (Fin.castSucc a)) (Fin.castSucc b)
    rw [embHom_castSucc_castSucc] at h2
    rw [h2]
    simp [Matrix.one_apply, Fin.castSucc_inj]
  refine ⟨k, hk, ⟨S, hSu⟩, ?_⟩
  have hu : uEmb r E ⟨S, hSu⟩ = h := Subtype.ext hS.symm
  rw [hu, hh, mul_inv_cancel_left]

end Main

end GlobalTheory.JR.Step

theorem GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s :=
  fun X ν l hν g hg => GlobalTheory.JR.Step.actU_liftH_support X ν l hν g hg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
section
noncomputable section

namespace GlobalTheory.MeetsGen

def pU {K G : Type} [Field K] [Group G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ u : U, MonoidAlgebra.single (u : G) ((Fintype.card U : K)⁻¹ * f u)

def cU {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * MonoidAlgebra.single g⁻¹ (1 : K)

def uElt {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) (e : MonoidAlgebra K G) :
    MonoidAlgebra K G :=
  cU U f * e + (1 - e)

theorem uup_eq_one_of_le_one {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ) (hr : r ≤ 1) (u : Formalism.L2.NX.GProd p r)
    (hu : u ∈ Formalism.L2.NX.Uup p r) : u = 1 := by
  funext x
  apply Units.ext
  ext a c
  have ha : a = c := Fin.ext (by have := a.2; have := c.2; omega)
  subst ha
  simp only [Pi.one_apply, Units.val_one, Matrix.one_apply_eq]
  exact ((Formalism.L2.NX.mem_Uup).1 hu x).2 a

theorem map_uElt {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (U : Subgroup G) [Fintype U]
    (f : U → E) (e : MonoidAlgebra E G) :
    MonoidAlgebra.mapRingHom G j (uElt U f e) = uElt U (fun u => j (f u)) (MonoidAlgebra.mapRingHom G j e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [uElt, cU, pU, map_add (f := _), map_mul, map_sub, map_one, map_sum, MonoidAlgebra.mapRingHom_single, map_inv₀,
    map_natCast]

theorem eq_sum_of_uElt_mul {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K)
    (e v : MonoidAlgebra K G) (hI : e * e = e) (hC : ∀ a, e * a = a * e) (hv : uElt U f e * v = 1) :
    e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * (MonoidAlgebra.single g⁻¹ (1 : K) * e * v) := by
  have h1 : e * uElt U f e = cU U f * e := by
    simp only [uElt]
    rw [mul_add, mul_sub, mul_one, hI, sub_self, add_zero, ← mul_assoc, hC (cU U f), mul_assoc, hI]
  calc e = e * (uElt U f e * v) := by rw [hv, mul_one]
    _ = cU U f * e * v := by rw [← mul_assoc, h1]
    _ = _ := by
      simp only [cU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [mul_assoc]

end GlobalTheory.MeetsGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerBoundBigCell
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LamBound

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem norm_etaK (A : Et F E) (t : A.K) : ‖A.etaK t‖ = 1 := by
  unfold Et.etaK eta
  split_ifs <;> simp

theorem absK_nonneg (A : Et F E) (t : A.K) : 0 ≤ A.absK t := by
  unfold Et.absK
  split_ifs <;> simp

theorem bdd_of_loc_const (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (O : Set K) (hO : IsCompact O) (Ψ : SpecialLinearGroup (Fin 2) K → ℂ) (U : Set K) (hU : U ∈ 𝓝 (0 : K))
    (hΨ : ∀ g k : SpecialLinearGroup (Fin 2) K, (∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) - 1) i j ∈ U) →
      Ψ (g * k) = Ψ g) :
    ∃ C : ℝ, ∀ k : SpecialLinearGroup (Fin 2) K, (∀ i j, (k : Matrix (Fin 2) (Fin 2) K) i j ∈ O) → ‖Ψ k‖ ≤ C := by
  classical
  let T : Set (Matrix (Fin 2) (Fin 2) K) := {M | ∀ i j, M i j ∈ O} ∩ {M | M.det = 1}
  have hT : IsCompact T := by
    have h1 : IsCompact {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} := by
      have := isCompact_univ_pi (fun _ : Fin 2 => isCompact_univ_pi (fun _ : Fin 2 => hO))
      have he : {M : Matrix (Fin 2) (Fin 2) K | ∀ i j, M i j ∈ O} =
          Set.univ.pi (fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 => O) := by
        ext M
        exact ⟨fun h => Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j,
          fun h i j => Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h i) j⟩
      rw [he]; exact this
    exact h1.inter_right (isClosed_eq (continuous_id.matrix_det) continuous_const)
  let N : Matrix (Fin 2) (Fin 2) K → Set (Matrix (Fin 2) (Fin 2) K) := fun M =>
    {M' | ∀ i j, (M.adjugate * M' - 1) i j ∈ U}
  have hN : ∀ M ∈ T, N M ∈ 𝓝 M := by
    intro M hM
    have hc : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => M.adjugate * M' - 1) :=
      (continuous_const.matrix_mul continuous_id).sub continuous_const
    have h0 : M.adjugate * M - 1 = 0 := by
      rw [Matrix.adjugate_mul, hM.2]; simp
    have hij : ∀ i j, ∀ᶠ M' in 𝓝 M, (M.adjugate * M' - 1) i j ∈ U := by
      intro i j
      have hcij : Continuous (fun M' : Matrix (Fin 2) (Fin 2) K => (M.adjugate * M' - 1) i j) :=
        hc.matrix_elem i j
      have := hcij.tendsto M
      simp only [h0, Matrix.zero_apply] at this
      exact this hU
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  obtain ⟨t, htT, hcov⟩ := hT.elim_nhds_subcover N hN
  let g : Matrix (Fin 2) (Fin 2) K → ℝ := fun M => if h : M.det = 1 then ‖Ψ ⟨M, h⟩‖ else 0
  refine ⟨∑ M ∈ t, g M, fun k hk => ?_⟩
  have hkT : (k : Matrix (Fin 2) (Fin 2) K) ∈ T := ⟨hk, k.2⟩
  obtain ⟨M, hMt, hkM⟩ := Set.mem_iUnion₂.1 (hcov hkT)
  have hdet : M.det = 1 := (htT M hMt).2
  let k₀ : SpecialLinearGroup (Fin 2) K := ⟨M, hdet⟩
  have he : Ψ k = Ψ k₀ := by
    have := hΨ k₀ (k₀⁻¹ * k) (by
      intro i j
      have := hkM i j
      exact this)
    simpa using this
  have hg : g M = ‖Ψ k₀‖ := by simp only [g, dif_pos hdet]; rfl
  rw [he, ← hg]
  exact Finset.single_le_sum (f := g) (fun M _ => by simp only [g]; split_ifs <;> positivity) hMt

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  intro F E _ _ _ _ U A Ψ hΨ
  have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let b := Module.finBasis F A.K
  have : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcpt, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  obtain ⟨V, hV, hloc⟩ := hΨ.1
  obtain ⟨C, hC⟩ := bdd_of_loc_const A.K A.OK hcpt Ψ V hV hloc
  refine ⟨C, fun z s α β hα hβ hs hsz h => ?_⟩
  have hu : (s : A.K) * ((s⁻¹ : A.Kˣ) : A.K) = 1 := Units.mul_inv s
  let k : SpecialLinearGroup (Fin 2) A.K := ⟨!![-β, α; -(s : A.K), -((s : A.K) * z)], by
    simp [Matrix.det_fin_two]; linear_combination h⟩
  have hk : wS A.K * nS z = nS (-((s : A.K) * β)) * mS s * k := by
    apply Subtype.ext
    show !![(0 : A.K), 1; -1, 0] * !![1, z; 0, 1] =
      !![1, -((s : A.K) * β); 0, 1] * !![(s : A.K), 0; 0, ((s⁻¹ : A.Kˣ) : A.K)] * !![-β, α; -(s : A.K), -((s : A.K) * z)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (-1 : A.K) * h - (β * (s : A.K) * z) * hu
  have hkO : ∀ i j, (k : Matrix (Fin 2) (Fin 2) A.K) i j ∈ A.OK := by
    rw [← hR]
    have hα' : α ∈ R := by rw [← SetLike.mem_coe, hR]; exact hα
    have hβ' : β ∈ R := by rw [← SetLike.mem_coe, hR]; exact hβ
    have hs' : (s : A.K) ∈ R := by rw [← SetLike.mem_coe, hR]; exact hs
    have hsz' : (s : A.K) * z ∈ R := by rw [← SetLike.mem_coe, hR]; exact hsz
    intro i j; fin_cases i <;> fin_cases j <;> simp [k, R.neg_mem, hα', hβ', hs', hsz']
  rw [hk, hΨ.2, norm_mul, norm_mul, norm_etaK, Complex.norm_real, Real.norm_of_nonneg (absK_nonneg A _), one_mul,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC k hkO) (absK_nonneg A _)

end GlobalTheory.JR.LamBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerSwap
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (u v : A.K) :
    A.psiK ψ (u + v) = A.psiK ψ u * A.psiK ψ v := by
  unfold psiK
  rw [map_add (f := _), AddChar.map_add_eq_mul]

theorem psiK_continuous (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) := by
  have h1 : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact (DualLattice.stdChar_continuous hψ).comp h1

theorem NL_continuous [Unram F E] (A : Et F E) : Continuous A.NL := by
  obtain ⟨⟨b⟩, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have : A.NL = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [this]
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hlin : Continuous (((b.coord i).comp (LinearMap.mulRight A.K (b j))).restrictScalars F) :=
    IsModuleTopology.continuous_of_linearMap _
  convert hlin using 1
  funext y
  simp [Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.Et

namespace GlobalTheory.JR.Et

theorem whittaker_swap : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
  intro F E _ _ _ _ _ A ψ hψ μK _ μ _ φ hφ x a c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hOpen, hCpt, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  set M : Set A.K := {z : A.K | c • z ∈ A.OK} with hMdef
  have hOKclosed : IsClosed A.OK := by
    have : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by
      change IsOpen (R : Set A.K); rw [hR]; exact hOpen
    have h2 := AddSubgroup.isClosed_of_isOpen _ this
    change IsClosed (R : Set A.K) at h2
    rwa [hR] at h2
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hMopen : IsOpen M := hOpen.preimage hsm
  have hMclosed : IsClosed M := hOKclosed.preimage hsm
  have hMcpt : IsCompact M := by
    have : M = (fun w : A.K => c⁻¹ • w) '' A.OK := by
      ext z
      constructor
      · intro hz
        exact ⟨c • z, hz, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩
        change c • c⁻¹ • w ∈ A.OK
        simpa [smul_smul, mul_inv_cancel₀ hc] using hw
    rw [this]
    exact hCpt.image (continuous_const_smul _)
  have hMmeas : MeasurableSet M := hMopen.measurableSet
  let g : A.K → A.L → ℂ := fun z y => φ y * A.psiK ψ (z * (x * A.NL y - a))
  let f : A.K → A.L → ℂ := fun z y => M.indicator (fun _ => (1 : ℂ)) z * g z y
  have hpt : ∀ z y, φ y * A.psiK ψ (z * x * A.NL y) * A.psiK ψ (-(a * z)) = g z y := by
    intro z y
    simp only [g]
    rw [mul_assoc, ← psiK_add]
    congr 2
    ring
  have hL : ∀ z, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) = ∫ y, g z y ∂μ := by
    intro z
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun y => hpt z y)
  have hind : ∀ (h : A.K → ℂ) z, M.indicator (fun _ => (1 : ℂ)) z * h z = M.indicator h z := by
    intro h z
    by_cases hz : z ∈ M <;> simp [hz]
  have hcontI : Continuous (M.indicator (fun _ : A.K => (1 : ℂ))) :=
    IsClopen.continuous_indicator ⟨hMclosed, hMopen⟩ continuous_const
  have hφc : Continuous φ := hφ.1.continuous
  have hcont : Continuous (Function.uncurry f) := by
    have hN := A.NL_continuous
    have hP := A.psiK_continuous hψ
    refine (hcontI.comp continuous_fst).mul ((hφc.comp continuous_snd).mul (hP.comp ?_))
    exact continuous_fst.mul (((continuous_const.mul (hN.comp continuous_snd))).sub continuous_const)
  have hsupp : HasCompactSupport (Function.uncurry f) := by
    have hsub : Function.support (Function.uncurry f) ⊆ M ×ˢ tsupport φ := by
      rintro ⟨z, y⟩ hzy
      simp only [Function.mem_support, Function.uncurry_apply_pair, f, g] at hzy
      refine ⟨?_, subset_tsupport _ ?_⟩
      · by_contra hz
        exact hzy (by simp [hz])
      · intro h0
        exact hzy (by simp [h0])
    exact IsCompact.of_isClosed_subset (hMcpt.prod hφ.2) (isClosed_tsupport _)
      (closure_minimal hsub (hMclosed.prod (isClosed_tsupport _)))
  have hswap := integral_integral_swap_of_hasCompactSupport hcont hsupp (μ := μK) (ν := μ)
  calc ∫ z in M, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK
      = ∫ z in M, (∫ y, g z y ∂μ) ∂μK := setIntegral_congr_fun hMmeas (fun z _ => hL z)
    _ = ∫ z, M.indicator (fun z => ∫ y, g z y ∂μ) z ∂μK := (integral_indicator hMmeas).symm
    _ = ∫ z, ∫ y, f z y ∂μ ∂μK := by
      congr 1 with z
      rw [← hind, ← integral_const_mul]
    _ = ∫ y, ∫ z, f z y ∂μK ∂μ := hswap
    _ = ∫ y, φ y * ∫ z in M, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by
      congr 1 with y
      rw [← integral_const_mul, ← integral_indicator hMmeas]
      congr 1 with z
      rw [← hind]

end GlobalTheory.JR.Et
end
end

