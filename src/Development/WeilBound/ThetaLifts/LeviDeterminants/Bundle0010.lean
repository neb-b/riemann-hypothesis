module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0009
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0005
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0004
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ChiIndep
section
noncomputable section

open scoped TensorProduct NNReal Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac

namespace PositivityTheory.ThKF0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem chi_indep (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {θ θ' : 𝓞 E} (h : (θ : E) + σ θ = 1)
    (h' : (θ' : E) + σ θ' = 1) {v : Pl (F := F)} {γ} (hγ : γ ∈ latAtV X W v) :
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  have h0 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1 (by rw [map_one]; exact one_mem _)
    γ hγ γ hγ
  rw [← mul_one (B.ψ (_ * symp _ (inclR (F := F) (AF F) (θ' : E)) _ _ _ _)), ← h0, ← AddChar.map_add_eq_mul]
  congr 1
  have hc := PositivityTheory.ThK.Vac.cA_cA (PositivityTheory.ThK.Vac.sigma_sigma hB.cm)
  have hh := GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (JA := incM F X.J) (JB := incM F W.J) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hX.herm]) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = -inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hW.skew, map_neg]) γ γ
  have e1 : cA σ (inclR (F := F) (AF F) (θ : E)) = 1 - inclR (F := F) (AF F) (θ : E) := by
    rw [GlobalTheory.VacIndic.cA_inclR, eq_sub_of_add_eq' h, map_sub, map_one]
  have e2 : cA σ (inclR (F := F) (AF F) (θ' : E)) = 1 - inclR (F := F) (AF F) (θ' : E) := by
    rw [GlobalTheory.VacIndic.cA_inclR, eq_sub_of_add_eq' h', map_sub, map_one]
  simp only [symp, one_mul]
  rw [show ((θ * (θ - θ') : 𝓞 E) : E) = θ * (θ - θ') by simp, map_mul (inclR (F := F) (AF F)), map_sub (inclR (F := F) (AF F))]
  generalize hTens (cA σ) (incM F X.J) (incM F W.J) γ γ = T at hh ⊢
  generalize inclR (F := F) (AF F) (θ : E) = a at e1 ⊢
  generalize inclR (F := F) (AF F) (θ' : E) = a' at e2 ⊢
  have t := GlobalTheory.VacCocycle.trace_conj (R := AF F) (cA σ) hc (a * (a - a') * T)
  rw [map_mul (cA σ), map_mul (cA σ), map_sub (cA σ), e1, e2, hh, show (1 - a) * (1 - a - (1 - a')) * -T = a * T - a' * T - a * (a - a') * T by ring,
    map_sub, map_sub] at t
  have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = u at h3 ⊢
  change u * Algebra.trace (AF F) (AE F E) (a * T) =
    u * Algebra.trace (AF F) (AE F E) (a' * T) + Algebra.trace (AF F) (AE F E) (a * (a - a') * T)
  linear_combination u * t + (Algebra.trace (AF F) (AE F E) (a * (a - a') * T)) * h3

theorem loc_eig {ψ : AddChar (AF F) ℂ} (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    {v : Pl (F := F)} {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) {γ} (hγ : γ ∈ latAtV X W v) {c : ℂ}
    (h : Acts (evFin F v) (co.rho ψ γ) φ (c • φ)) : schr (psiAt ψ v) (locCo co v γ) φ = c • φ :=
  GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun t ht =>
    (GlobalTheory.VacBridge.rho_acts_locCo co ψ v γ ((latAtV_at_stable X W v).1 γ hγ) φ t ht).symm.trans (h t ht)

theorem vac_line (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W) (v : Pl (F := F)) {φ φ'}
    (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') : ∃ c : ℂ, c ≠ 0 ∧ φ' = c • φ := by
  obtain ⟨hs, h0, θ, hθ, hA⟩ := h
  obtain ⟨hs', h0', θ', hθ', hA'⟩ := h'
  obtain ⟨c, hc⟩ := PositivityTheory.ThK.Vac.local_line M.co hB.std v (latAtV X W v) (latAtV_at_stable X W v).1
    (fun z hz h => PositivityTheory.ThK.Vac.mem_latAtV hB hX hW v hz h) _ hs hs' h0 (fun γ hγ => loc_eig M.co hs hγ (hA γ hγ))
    fun γ hγ => by
      have k := loc_eig M.co hs' hγ (hA' γ hγ)
      rw [← chi_indep hB hX hW hθ hθ' hγ] at k
      exact k
  exact ⟨c, fun c0 => h0' (by rw [hc, c0, zero_smul]), hc⟩

end PositivityTheory.ThKF0

end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EigenIntertwinerTwoPlanes
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

set_option maxHeartbeats 1600000 in
theorem adapted_plane_model_evaluation_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoB H H') e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  classical
  obtain ⟨Q, h⟩ := frOK_herm hB hH hX
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F Q * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F Q * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (incM F H.ι * z * (incM F H'.ι)ᵀ) = Matrix.fromBlocks z 0 0 0 := fun z => by
    rw [hw, w_mul, h.qi, h'.qi]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have hπ : ∀ v, ∀ γ ∈ latAtV X W v, (w γ).submatrix .inl .inl ∈ latAtV X₁ W₁ v := fun v γ hγ =>
    lat_map (X₁ := X₁) (W₁ := W₁) h.low h'.low hγ
  have qv : ∀ z, incM F Q *ᵥ (incM F H.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h.qi]; ext (i | i) <;> simp
  have qv' : ∀ z, incM F Q' *ᵥ (incM F H'.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h'.qi]; ext (i | i) <;> simp
  let G : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) E := (frame H')ᵀ * W.J * (frame H').map σ
  have hG : incM F G = Matrix.fromBlocks (incM F W₁.J) 0 0 !![0, 1; -1, 0] := by
    have := h'.gram
    rw [Int.cast_neg, Int.cast_one] at this
    rw [← this, incM_mul, incM_mul]
    rfl
  have hGh : ∀ i j, cA σ (incM F G j i) = -1 * incM F G i j := fun i j => by
    have := inc_herm (F := F) (η := -1) (J := G) (gram_herm σ (conj_conj hB) (fun i j => by simp [hW.skew]) _) i j
    rwa [Int.cast_neg, Int.cast_one] at this
  obtain ⟨A0, a0, e0⟩ := h.msk 0 1 0
  obtain ⟨A1, a1, e1⟩ := h.msk 1 0 0
  obtain ⟨C0, c0, f0⟩ := h'.msk 1 1 1
  obtain ⟨C1, c1, f1⟩ := h'.msk 0 1 0
  obtain ⟨Ma, e, h1, h2⟩ := exists_model hB hX hW hM hM₁ (κ := (Fin d₁ ⊕ Fin 2) ⊕ Fin n₁) (by simp [hH.rank, hH'.rank]; ring)
    (fun z => Sum.elim (w z (.inr 1)) (fun i => ((w z).submatrix .inl id) i (.inr 1)))
    (fun z => Sum.elim (DL (cA σ) (incM F G) (w z)) (DR (cA σ) (incM F X₁.J) ((w z).submatrix .inl id)))
    (fun z => (w z).submatrix .inl .inl)
    ⟨fun z z' => by ext (k | k) <;> simp, fun c z => by ext (k | k) <;> simp⟩
    ⟨fun z z' => by ext (k | k) <;> simp only [map_add (f := _), DR, DL, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.add_apply,
        Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib, neg_add],
      fun c z => by ext (k | k) <;> simp [DR, DL, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g := h.gram
      rw [Int.cast_one] at g
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one, ← hG] at g'
      rw [hTens_fr _ _ h.pq h'.pq, g, g', splitL _ hc _ hGh, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, map_add (f := _)]
      conv_lhs => rw [hG, splitR _ hc (fun i j => by simpa using h.herm₁ i j), ← hG]
      simp only [← hw]
      rw [show ∀ z, ((w z).submatrix Sum.inl id).submatrix id Sum.inl = (w z).submatrix .inl .inl from fun _ => rfl,
        show ∀ z, ((w z).submatrix Sum.inl id).submatrix id Sum.inl = (w z).submatrix .inl .inl from fun _ => rfl]
      ring)
    (fun x => by
      simp only [hw, w_inc]
      generalize Q * x * Q'ᵀ = y
      refine ⟨⟨Sum.elim (y (.inr 1)) (fun i => (y.submatrix .inl id) i (.inr 1)), by ext (k | k) <;> rfl⟩,
        ⟨Sum.elim (DL σ G y) (DR σ X₁.J (y.submatrix .inl id)), ?_⟩, y.submatrix .inl .inl, rfl⟩
      ext (k | k)
      · exact congrFun (DL_inc G y) k
      · exact congrFun (DR_inc X₁.J (y.submatrix .inl id)) k)
    H.ι H'.ι (isoB H H') (fun z => by
      simp only [hi]
      exact ⟨by ext ((k | k) | k) <;> simp, by ext; simp⟩)
    (by
      rintro u (⟨y, rfl⟩ | ⟨y, rfl⟩)
      · simp only [hw, w_vec, h.qx]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩
      · simp only [hw, w_vec, h'.qx, qv]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨hπ v γ hγ, _, add_mem (lat_map a0 c0 hγ) (lat_map a1 c1 hγ), by
      simp only [map_add (f := _)]
      simp only [hw, w_msk e0 f0, w_msk e1 f1]
      generalize incM F Q * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext ((k | k) | k) <;> simp [mask]
      · ext; simp [mask]
      · ext (k | k)
        · simp only [Sum.elim_inl, DL]
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 2
          rcases l with l | l
          · simp [mask]
          · fin_cases l <;> simp [mask]
        · simp [DR, mask]⟩)
  exact ⟨Ma, e, h1, h2⟩

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsAdaptedModelTwoPlanes
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

set_option maxHeartbeats 1600000 in
theorem adapted_plane_model_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁)
    (H' : Plane E d d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ H.ι H'.ι (isoA H H') e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hB hX hW hM hH hH' hM₁
  classical
  obtain ⟨Q, h⟩ := frOK_herm hB hH hX
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F Q * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F Q * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (incM F H.ι * z * (incM F H'.ι)ᵀ) = Matrix.fromBlocks z 0 0 0 := fun z => by
    rw [hw, w_mul, h.qi, h'.qi]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have hπ : ∀ v, ∀ γ ∈ latAtV X W v, (w γ).submatrix .inl .inl ∈ latAtV X₁ W₁ v := fun v γ hγ =>
    lat_map (X₁ := X₁) (W₁ := W₁) h.low h'.low hγ
  have qv : ∀ z, incM F Q *ᵥ (incM F H.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h.qi]; ext (i | i) <;> simp
  have qv' : ∀ z, incM F Q' *ᵥ (incM F H'.ι *ᵥ z) = Sum.elim z 0 := fun z => by
    rw [Matrix.mulVec_mulVec, h'.qi]; ext (i | i) <;> simp
  let G : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E := (frame H)ᵀ * X.J * (frame H).map σ
  have hG : incM F G = Matrix.fromBlocks (incM F X₁.J) 0 0 !![0, 1; 1, 0] := by
    have := h.gram
    rw [Int.cast_one] at this
    rw [← this, incM_mul, incM_mul]
    rfl
  have hGh : ∀ i j, cA σ (incM F G j i) = 1 * incM F G i j := fun i j => by
    have := inc_herm (F := F) (η := 1) (J := G) (gram_herm σ (conj_conj hB) (fun i j => by simp [hX.herm]) _) i j
    rwa [Int.cast_one] at this
  obtain ⟨A0, a0, e0⟩ := h.msk 1 1 1
  obtain ⟨A1, a1, e1⟩ := h.msk 0 1 0
  obtain ⟨C0, c0, f0⟩ := h'.msk 0 1 0
  obtain ⟨C1, c1, f1⟩ := h'.msk 1 0 0
  obtain ⟨Ma, e, h1, h2⟩ := exists_model hB hX hW hM hM₁ (κ := (Fin n₁ ⊕ Fin 2) ⊕ Fin d₁) (by simp [hH.rank, hH'.rank]; ring)
    (fun z => Sum.elim (fun i => w z i (.inr 1)) (((w z).submatrix id .inl) (.inr 1)))
    (fun z => Sum.elim (DR (cA σ) (incM F G) (w z)) (DL (cA σ) (incM F W₁.J) ((w z).submatrix id .inl)))
    (fun z => (w z).submatrix .inl .inl)
    ⟨fun z z' => by ext (k | k) <;> simp, fun c z => by ext (k | k) <;> simp⟩
    ⟨fun z z' => by ext (k | k) <;> simp only [map_add (f := _), DR, DL, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.add_apply,
        Matrix.submatrix_apply, mul_add, Finset.sum_add_distrib, neg_add],
      fun c z => by ext (k | k) <;> simp [DR, DL, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one] at g'
      have g := h.gram
      rw [Int.cast_one, ← hG] at g
      rw [hTens_fr _ _ h.pq h'.pq, g, g', splitR _ hc hGh, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, map_add (f := _)]
      conv_lhs => rw [hG, splitL _ hc _ (fun i j => by simpa using h'.herm₁ i j), ← hG]
      simp only [← hw]
      rw [show ∀ z, ((w z).submatrix id Sum.inl).submatrix Sum.inl id = (w z).submatrix .inl .inl from fun _ => rfl,
        show ∀ z, ((w z).submatrix id Sum.inl).submatrix Sum.inl id = (w z).submatrix .inl .inl from fun _ => rfl]
      ring)
    (fun x => by
      simp only [hw, w_inc]
      generalize Q * x * Q'ᵀ = y
      refine ⟨⟨Sum.elim (fun i => y i (.inr 1)) ((y.submatrix id .inl) (.inr 1)), by ext (k | k) <;> rfl⟩,
        ⟨Sum.elim (DR σ G y) (DL σ W₁.J (y.submatrix id .inl)), ?_⟩, y.submatrix .inl .inl, rfl⟩
      ext (k | k)
      · exact congrFun (DR_inc G y) k
      · exact congrFun (DL_inc W₁.J (y.submatrix id .inl)) k)
    H.ι H'.ι (isoA H H') (fun z => by
      simp only [hi]
      exact ⟨by ext ((k | k) | k) <;> simp, by ext; simp⟩)
    (by
      rintro u (⟨y, rfl⟩ | ⟨y, rfl⟩)
      · simp only [hw, w_vec, h'.qx]
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩
      · simp only [hw, w_vec, h.qx, qv']
        exact ⟨by ext (k | k) <;> simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨hπ v γ hγ, _, add_mem (lat_map a0 c0 hγ) (lat_map a1 c1 hγ), by
      simp only [map_add (f := _)]
      simp only [hw, w_msk e0 f0, w_msk e1 f1]
      generalize incM F Q * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext ((k | k) | k) <;> simp [mask]
      · ext; simp [mask]
      · ext (k | k)
        · simp only [Sum.elim_inl, DR]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 2
          rcases l with l | l
          · simp [mask]
          · fin_cases l <;> simp [mask]
        · simp [DL, mask]⟩)
  exact ⟨Ma, e, h1, h2⟩

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsModel0
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt

set_option maxHeartbeats 400000 in
theorem exists_model0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ →
    ∃ (κ₀ : Type) (_ : Fintype κ₀) (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n × Fin d₁) (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d₁)
      (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ 1 H'.ι (iso0 n H') e ∧
      (∀ z, Ma.co.e (z * (incM F H'.ι)ᵀ) = (glue ε 0 (M₁.co.e z).1, glue ε 0 (M₁.co.e z).2)) ∧
      (∀ y, ∃ q, Ma.co.e (Matrix.vecMulVec y (incV F H'.x)) = (0, glue ε q 0)) ∧
      (∀ y, ∃ p, Ma.co.e (Matrix.vecMulVec y (incV F H'.y)) = (glue ε p 0, 0)) ∧ (∀ f b, T f b = f (glue ε 0 b)) ∧
      ∃ ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ,
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH' hM₁
  classical
  obtain ⟨Q', h'⟩ := frOK_skew hB hH' hW
  let w : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d₁ ⊕ Fin 2) (AE F E) :=
    { toFun := fun z => incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F Q')ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c z => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hw : ∀ z, w z = incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F Q')ᵀ := fun _ => rfl
  have hc := cA_cA (σ := σ) hB
  have hi : ∀ z, w (z * (incM F H'.ι)ᵀ) = Matrix.fromCols z 0 := fun z => by
    rw [hw, incM_one', Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h'.qi]
    ext i (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  have h1 : ∀ u ∈ X.L, (1 : Matrix (Fin n) (Fin n) E) *ᵥ u ∈ X.L := fun u hu => by rwa [Matrix.one_mulVec]
  obtain ⟨C0, c0, f0⟩ := h'.msk 0 1 0
  obtain ⟨ε, Ma, e, p, q, hMa, hco, hp, hq, he, T, hT, hev⟩ := exists_modelS hB hX hW hM hM₁ (κ := Fin n)
    (by simp [hH'.rank]; ring) (fun z i => w z i (.inr 1)) (fun z => DR (cA σ) (incM F X.J) (w z))
    (fun z => (w z).submatrix id .inl) ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    ⟨fun z z' => by ext; simp only [map_add (f := _), DR, Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib, neg_add], fun c z => by ext; simp [DR, Finset.smul_sum]⟩
    ⟨fun z z' => by ext; simp, fun c z => by ext; simp⟩
    (fun z z' => by
      have g' := h'.gram
      rw [Int.cast_neg, Int.cast_one] at g'
      rw [hTens_fr _ _ (Matrix.one_mul 1) h'.pq, g', Matrix.transpose_one, Matrix.one_mul (incM F X.J),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
        splitR _ hc (fun i j => by simpa using inc_herm (F := F) (η := 1) (J := X.J) (fun i j => by simp [hX.herm]) i j)]
      simp only [hw, incM_one'])
    (fun x => by
      simp only [hw, w_inc]
      generalize (1 : Matrix (Fin n) (Fin n) E) * x * Q'ᵀ = y
      exact ⟨⟨fun i => y i (.inr 1), rfl⟩, ⟨_, DR_inc X.J y⟩, y.submatrix id .inl, rfl⟩)
    1 H'.ι (iso0 n H') (fun z => by
      simp only [incM_one', Matrix.one_mul, hi]
      exact ⟨by ext; simp, by ext; simp⟩)
    (by
      rintro u ⟨y, rfl⟩
      simp only [hw, w_vec, h'.qx]
      exact ⟨by ext; simp [Matrix.vecMulVec_apply], by ext; simp [Matrix.vecMulVec_apply]⟩)
    (fun v γ hγ => ⟨lat_map (X₁ := X) (W₁ := W₁) h1 h'.low hγ, _, lat_map h1 c0 hγ, by
      simp only [hw, w_msk (m := 1) (show incM F (1 : Matrix (Fin n) (Fin n) E) * incM F 1 = 1 * incM F 1 by
        rw [incM_one', Matrix.one_mul]) f0]
      generalize incM F (1 : Matrix (Fin n) (Fin n) E) * γ * (incM F Q')ᵀ = y
      refine ⟨?_, ?_, ?_⟩
      · ext; simp [mask]
      · ext; simp [mask]
      · ext; simp [DR, mask]⟩)
  refine ⟨_, inferInstance, ε, Ma, e, T, hMa, he, fun z => ?_, fun y => ⟨q (Matrix.vecMulVec y (incV F H'.x)), ?_⟩,
    fun y => ⟨p (Matrix.vecMulVec y (incV F H'.y)), ?_⟩, hT, hev⟩
  · rw [hco, hp _ (by ext; simp [hi]), hq _ (by ext; simp [hi, DR]),
      show (w (z * (incM F H'.ι)ᵀ)).submatrix id Sum.inl = z by ext; simp [hi]]
  · have e1 : w (Matrix.vecMulVec y (incV F H'.x)) = Matrix.vecMulVec y (Pi.single (.inr 0) 1) := by
      rw [hw, w_vec, h'.qx, incM_one', Matrix.one_mulVec]
    rw [hco, hp _ (by ext; simp [e1, Matrix.vecMulVec_apply]),
      show (w (Matrix.vecMulVec y (incV F H'.x))).submatrix id Sum.inl = 0 by ext; simp [e1, Matrix.vecMulVec_apply], map_zero]
    exact Prod.ext (glue_zero ε) rfl
  · have e1 : w (Matrix.vecMulVec y (incV F H'.y)) = Matrix.vecMulVec y (Pi.single (.inr 1) 1) := by
      rw [hw, w_vec, h'.qy, incM_one', Matrix.one_mulVec]
    rw [hco, hq _ (by ext; simp [e1, DR, Matrix.vecMulVec_apply]),
      show (w (Matrix.vecMulVec y (incV F H'.y))).submatrix id Sum.inl = 0 by ext; simp [e1, Matrix.vecMulVec_apply], map_zero]
    exact Prod.ext rfl (glue_zero ε)

end PositivityTheory.ThKF0
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsNeOfSurjOn
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem surjOn_of_pure (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ)) (hi : Function.Surjective ei)
    (hSB : ∀ v, Set.SurjOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _))
    (hstd : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (hloc : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) :
    Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _) := by
  change schA F κ ≤ (schA F κ).map e
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := Span.exists_sum_finprod hg
  have h1 : pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
  obtain ⟨f₀, rfl⟩ := hi f
  have hp : ∀ v, ∃ φ₀ ∈ SB (κ → Fv F v), ev v φ₀ = φ k v ∧ (ev v (φ k v) = φ k v → φ₀ = φ k v) := fun v => by
    by_cases h : ev v (φ k v) = φ k v
    · exact ⟨_, hφSB k v, h, fun _ => rfl⟩
    · obtain ⟨φ₀, h0, h1⟩ := hSB v (hφSB k v)
      exact ⟨φ₀, h0, h1, fun h' => absurd h' h⟩
  choose φ₀ h0 h1 h2 using hp
  have hs : ∀ᶠ v in cofinite, φ₀ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hφstd k, hstd] with v e1 e2
    rw [h2 v (by rw [e1, e2]), e1]
  refine ⟨_, GlobalTheory.TensUniq.pure_mem_schA f₀ φ₀ h0 hs, ?_⟩
  rw [hloc f₀ φ₀ h0 hs]
  simp only [h1]

theorem exists_ne_of_surjOn {e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)} (h : Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _)) :
    ∃ Φ ∈ schA F κ, e Φ ≠ 0 := by
  obtain ⟨φ, hφ, h0⟩ := _root_.GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  obtain ⟨Φ, hΦ, rfl⟩ := h hφ
  exact ⟨Φ, hΦ, fun h1 => h0 (by rw [h1]; rfl)⟩

theorem tw_surj (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} (d d₁ : Darboux B κ) : ∃ e, Tw ψ d d₁ e ∧ Set.SurjOn e (schA F κ : Set _) (schA F κ : Set _) := by
  obtain ⟨e, ei, ev, h1, h2, h3, -, h5, h6⟩ := hA F ψ hψ κ (d.e.symm.trans d₁.e) fun w w' => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← d₁.form, d.form, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  have hs := surjOn_of_pure e ei ev ei.surjective (fun v => (h3 v).surjOn) h5 h6
  refine ⟨e, ⟨h1, fun u Φ hΦ => ?_, Span.comp_mem_adm e ei ev (fun v φ hφ => (h3 v).mapsTo hφ) h5 h6, exists_ne_of_surjOn hs⟩, hs⟩
  have := h2 (d.e u) Φ hΦ
  rwa [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at this

theorem twEx (hA : PositivityTheory.Mix.AdelSt) : TwEx := fun _ _ _ _ hψ _ _ _ _ _ _ d d₁ => (tw_surj hA hψ d d₁).imp fun _ h => h.1

theorem tw_bij (hA : PositivityTheory.Mix.AdelSt) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} (d d₁ : Darboux B κ) : ∃ e e', Tw ψ d d₁ e ∧ Tw ψ d₁ d e' ∧
      Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) ∧ (∀ Φ ∈ schA F κ, e' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e' Φ) = Φ := by
  obtain ⟨e, h, hs⟩ := tw_surj hA hψ d d₁
  obtain ⟨e', h', -⟩ := tw_surj hA hψ d₁ d
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h'.ne
    obtain ⟨Ψ, hΨ, rfl⟩ := hs hΦ
    exact hne ((ha Ψ hΨ).trans (by rw [a0, zero_smul]))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  have hscaled : Tw ψ d₁ d (a⁻¹ • e') := by
    constructor
    · exact fun Φ hΦ => Submodule.smul_mem _ _ (h'.maps Φ hΦ)
    · intro w Φ hΦ
      rw [LinearMap.smul_apply, LinearMap.smul_apply, h'.Heisenberg₂ w Φ hΦ, rho_smul]
    · intro l hl g hg
      obtain ⟨T, hT⟩ := h'.adm l hl g hg
      refine ⟨a⁻¹ • T, fun f => ?_⟩
      rw [LinearMap.comp_smul, LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]
    ·
      obtain ⟨Φ, hΦ, h0⟩ := h'.ne
      exact ⟨Φ, hΦ, smul_ne_zero (inv_ne_zero a0) h0⟩
  refine ⟨e, _, h, hscaled, ⟨h.maps, fun x hx y hy hxy => ?_, hs⟩, h1, fun Φ hΦ => ?_⟩
  · rw [← h1 x hx, hxy, h1 y hy]
  · obtain ⟨Ψ, hΨ, rfl⟩ := hs hΦ
    rw [h1 Ψ hΨ]

end PositivityTheory.ThKF0

end
end

