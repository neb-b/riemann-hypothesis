module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ColEApply
section
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def colE (m n : ℕ) : (Fin n → Fin m → AF F ⊗[F] E) ≃ₜ+ Mx F E m n where
  toFun := toMx
  invFun := fun X j a => X a j
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  continuous_toFun := continuous_pi fun a => continuous_pi fun j => (continuous_apply a).comp (continuous_apply j)
  continuous_invFun := continuous_pi fun j => continuous_pi fun a => (continuous_apply j).comp (continuous_apply a)

def colM (m n : ℕ) : (Fin n → Fin m → AF F ⊗[F] E) ≃ᵐ Mx F E m n := (colE (F := F) (E := E) m n).toHomeomorph.toMeasurableEquiv

theorem toMx_mem {m n : ℕ} (Y : Fin n → Fin m → AF F ⊗[F] E) :
    toMx Y ∈ ratMx F E m n ↔ Y ∈ MeasP.ratTupA F E n m := by
  rw [mem_ratMx]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨fun j a => X a j, ?_⟩
    funext j a
    exact congrFun (congrFun hX a) j
  · rintro ⟨Z, hZ⟩
    refine ⟨Matrix.of fun a j => Z j a, ?_⟩
    funext a j
    rw [← hZ]
    rfl

def ratEq (m n : ℕ) : ratMx F E m n ≃ MeasP.ratTupA F E n m where
  toFun X := ⟨(colE m n).symm X.1, (toMx_mem _).1 X.2⟩
  invFun Y := ⟨toMx Y.1, (toMx_mem _).2 Y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem meas_toMx (d : SD σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m → AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 := by
  have hemb : MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) := (colM d.m d.n).measurableEmbedding
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact (colE (F := F) (E := E) d.m d.n).toAddEquiv.isAddHaarMeasure_map μ (colE d.m d.n).continuous
      (colE d.m d.n).symm.continuous
  · rw [ratM_eq]
    refine hF.image_of_equiv (colM d.m d.n).toEquiv ?_ (ratEq d.m d.n) ?_
    · exact ((colM d.m d.n).measurePreserving_symm μ).quasiMeasurePreserving
    · intro g x
      rfl
  · rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective, h1]

end PositivityTheory.SiegelWeilFormula.MeasD

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ExistsNeZeroOfMap
section
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp

namespace PositivityTheory.SiegelWeilFormula.MeasD

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem conj_sym {ι κ : Type} [Fintype ι] (hσ : ∀ a, σ (σ a) = a) (P : Matrix ι κ E) (M : Matrix ι ι E) (s : E)
    (hM : ∀ i j, σ (M j i) = s * M i j) (i j : κ) :
    σ ((Pᵀ * M * P.map σ) j i) = s * (Pᵀ * M * P.map σ) i j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hM, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem frame_sign (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (hn : 1 ≤ n) (J : Matrix (Fin n) (Fin n) E) (s : E)
    (hJ : ∀ i j, σ (J j i) = s * J i j) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hb : b.1ᵀ * dbl J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) : (((ε : ℤ) : E)) = s := by
  have hD : ∀ i j, σ (dbl J j i) = s * dbl J i j := by
    rintro (i | i) (j | j) <;> simp [dbl, hJ]
  have h := conj_sym hσ b.1 (dbl J) s hD (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩)
  rw [hb] at h
  simpa using h

theorem ne_zero_of_sig {m r s : ℕ} (hm : 1 ≤ m) (M : Matrix (Fin m) (Fin m) ℂ) (h : HasSig M r s) : M ≠ 0 := by
  rintro rfl
  obtain ⟨hrs, A, hA⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at hA
  rcases Nat.eq_zero_or_pos r with hr | hr
  · have hs : 0 < s := by omega
    have := congrFun (congrFun hA (Sum.inr ⟨0, hs⟩)) (Sum.inr ⟨0, hs⟩)
    simp at this
  · have := congrFun (congrFun hA (Sum.inl ⟨0, hr⟩)) (Sum.inl ⟨0, hr⟩)
    simp at this

theorem exists_ne_zero_of_map {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (f : E →+* ℂ) (c : ℂ) (h : c • J.map f ≠ 0) :
    ∃ i j, J i j ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  ext i j
  simp [hc i j]

theorem eta_sign (d : SD σ) {η : E} (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) {ε : ℤˣ}
    (hb : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    σ η = -(((ε : ℤ) : E)) * η := by
  have hσ := sigma_sigma_of_good d.ok.good
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := frame_sign hσ d.ok.hn d.Y.J (-1) (fun i j => by rw [hY, neg_one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 1
      (by rw [one_smul]; exact ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.herm] at h
    rw [he, neg_neg, one_mul]
    exact mul_right_cancel₀ hij h
  · have he := frame_sign hσ d.ok.hn d.Y.J 1 (fun i j => by rw [hY, one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 Complex.I (ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.skew] at h
    rw [he, neg_one_mul]
    apply mul_right_cancel₀ hij
    linear_combination -h

end PositivityTheory.SiegelWeilFormula.MeasD

end
end

