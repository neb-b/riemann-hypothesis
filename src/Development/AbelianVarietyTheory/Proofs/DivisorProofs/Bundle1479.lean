module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignatures
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.FockVacuum

noncomputable section

namespace GlobalTheory.HoweD

section Sign

variable {ι : Type} {P Q R S : ι → ℕ}

def cplxD (ι : Type) (P Q R S : ι → ℕ) : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) where
  toFun c w := Matrix.of fun a b => lineSign a b * Complex.I * c w a b
  map_add' c c' := by ext w a b; simp [mul_add]
  map_smul' r c := by ext w a b; simp; ring

theorem cplxD_apply (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S c w a b = lineSign a b * Complex.I * c w a b := rfl

theorem cplxD_cplxD (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) : cplxD ι P Q R S (cplxD ι P Q R S c) = -c := by
  ext w a b
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, ← mul_assoc]

theorem herm_cplxD [Fintype ι] (c c' : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    ∑ w, ∑ a, ∑ b, lineSign a b * cplxD ι P Q R S c w a b * star (cplxD ι P Q R S c' w a b) =
      ∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b) := by
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h]
  · linear_combination (-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I
  · linear_combination (c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I

theorem herm_cplxD_pos [Fintype ι] (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

theorem cplxD_single [DecidableEq ι] (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S (Pi.single w (Matrix.single a b 1)) =
      (lineSign a b).re • (Pi.single w (Matrix.single a b Complex.I) : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := by
  ext w' a' b'
  rw [cplxD_apply]
  by_cases hw : w' = w
  · subst hw
    by_cases hab : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hab
      rcases lineSign_cases a b with h | h <;> simp [h]
    · simp [Matrix.single_apply, hab]
  · simp [hw]

end Sign

theorem exists_vacuumD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD
  have hU := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨X, Y, hX, hY, hYp, hXY⟩ := exists_siegel (trPair F κ) p q (cplxD _ P Q R S) cplxD_cplxD
    (fun c c' => by rw [hω, hω, herm_cplxD]) (fun c hc => by rw [hω]; exact herm_cplxD_pos c hc) hs
  obtain ⟨f, hf0, hf⟩ := exists_gaussian X Y hX hY hYp
  refine ⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩
  have e1 := hU' _ u ⟨hu, hc⟩
  have e2 := hU' _ u' ⟨hu', hc'⟩
  set c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b 1) with hcdef
  set c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'
  have hJ : cplxD _ P Q R S c = (lineSign a b).re • c' := cplxD_single w a b
  ext x
  have h1 := hXY c x
  have h2 := hXY (cplxD _ P Q R S c) x
  rw [cplxD_cplxD] at h2
  rw [hJ] at h1 h2
  simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
  have k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x := by
    rw [hD u hu, hf, e1]; rfl
  have k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x := by
    rw [hD u' hu', hf, e2]; rfl
  change D u f x + (lineSign a b * Complex.I) * D u' f x = 0
  rw [k1, k2]
  have h1' := congrArg (fun t : ℝ => (t : ℂ)) h1
  have h2' := congrArg (fun t : ℝ => (t : ℂ)) h2
  have hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b := by
    rcases lineSign_cases a b with h | h <;> simp [h]
  push_cast at h1' h2'
  rw [hl] at h1' h2'
  linear_combination (2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' +
    (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I

end GlobalTheory.HoweD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace GlobalTheory.PrimFrameMove

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem exists_rightInverse {X : Matrix A D k} (hX : IsPrimFrame (SplitFlip.stdLat k D) X) :
    ∃ R : Matrix D A k, (∀ i j, R i j ∈ 𝒪[k]) ∧ X * R = 1 := by
  have hli : LinearIndependent k X.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, ← hX.1, rank_eq_finrank_span_row]; rfl
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let f : (A → 𝒪[k]) →ₗ[𝒪[k]] (D → 𝒪[k]) := X'.vecMulLinear
  have hf : ∀ v j, ((f v j : 𝒪[k]) : k) = (∑ i, (v i : k) • X.row i) j := fun v j => by
    simp [f, X', vecMul, dotProduct, Finset.sum_apply]
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : ∑ i, (v i : k) • X.row i = 0 := by
      funext j; rw [← hf, hv]; rfl
    funext i
    exact Subtype.ext (Fintype.linearIndependent_iff.1 hli _ h1 i)
  have hsat : ∀ (r : 𝒪[k]) (x : D → 𝒪[k]), r ≠ 0 → r • x ∈ LinearMap.range f → x ∈ LinearMap.range f := by
    rintro r x hr ⟨v, hv⟩
    have hr' : (r : k) ≠ 0 := fun h => hr (Subtype.ext h)
    have h1 : (fun j => (x j : k)) = (r : k)⁻¹ • ∑ i, (v i : k) • X.row i := by
      funext j
      rw [Pi.smul_apply, ← hf, hv]
      simp [hr']
    have h2 : (fun j => (x j : k)) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      refine ⟨?_, mem_stdLat.2 fun j => (x j).2⟩
      rw [h1]
      exact Submodule.smul_mem (Submodule.span k _) _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    refine ⟨d, funext fun j => Subtype.ext ?_⟩
    rw [hf]
    exact congrFun hd j
  have : Module.IsTorsionFree 𝒪[k] ((D → 𝒪[k]) ⧸ LinearMap.range f) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r q h => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact .inl hr
    · refine .inr ((Submodule.Quotient.mk_eq_zero _).2 (hsat r x hr ?_))
      rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  obtain ⟨l, hl⟩ : ∃ l : (D → 𝒪[k]) →ₗ[𝒪[k]] (A → 𝒪[k]), l ∘ₗ f = LinearMap.id := by
    have hs' : ∃ s : _ →ₗ[𝒪[k]] _, (LinearMap.range f).mkQ ∘ₗ s = LinearMap.id := ⟨s, hs⟩
    have H := ((LinearMap.exact_map_mkQ_range f).split_tfae hinj (Submodule.mkQ_surjective _)).out 1 2
    exact H.1 hs'
  refine ⟨Matrix.of fun j i => (l (Pi.single j 1) i : k), fun j i => (l (Pi.single j 1) i).2, ?_⟩
  ext i i'
  have h1 : l (f (Pi.single i 1)) = Pi.single i 1 := LinearMap.congr_fun hl _
  have h2 : f (Pi.single i 1) = ∑ j, X' i j • Pi.single j 1 := by
    funext j; simp [f, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum] at h1
  have h3 := congrArg Subtype.val (congrFun h1 i')
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  push_cast at h3
  rw [Matrix.mul_apply, Matrix.one_apply]
  refine h3.trans ?_
  rw [Pi.single_apply]
  by_cases h : i = i'
  · simp [h]
  · simp [h, Ne.symm h]

theorem exists_mem_glLatCong {u : kˣ} (hu : valuation k (u : k) < 1) {M : Matrix D D k}
    (hM : ∀ i j, valuation k (M i j) ≤ valuation k (u : k)) :
    ∃ κ ∈ glLatCong u (SplitFlip.stdLat k D), κ.val = 1 + M := by
  let M' : Matrix D D 𝒪[k] := Matrix.of fun i j => ⟨M i j, (hM i j).trans hu.le⟩
  have hK : IsUnit (1 + M') := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 0 := by
      ext r j
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact (hM r j).trans_lt hu
    rw [map_add (f := _), this]; simp
  obtain ⟨w, hw⟩ := hK
  have hv : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w).val = 1 + M := by
    show (algebraMap 𝒪[k] k).mapMatrix w.val = _
    rw [hw, map_add (f := _), map_one]; rfl
  refine ⟨_, GlobalTheory.FunObj.GivenAdm.mem_glLatCong.2 ⟨⟨w, rfl⟩, ?_⟩, hv⟩
  rw [hv, add_sub_cancel_left]
  exact hM


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem vecMul_diagGL_mem (a b c : D → kˣ) (h : ∀ j, b j = a j * c j) (x : D → k) :
    x ᵥ* (diagGL c).val ∈ diagLat b ↔ x ∈ diagLat a := by
  refine forall_congr' fun j => ?_
  have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
  rw [diagGL_val, vecMul_diagonal, map_mul, h, Units.val_mul, map_mul]
  exact mul_le_mul_iff_left₀ h0

theorem exists_glLatCong_move (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (c : D → kˣ) (u : kˣ) (hu : valuation k (u : k) < 1) (X Z : Matrix A D k) (hX : IsPrimFrame (diagLat c) X)
    (hZ : Z ∈ matLat A (u • diagLat c)) : ∃ κ ∈ glLatCong u (diagLat c), X + Z = X * κ.val := by
  set g : GL D k := diagGL c with hg
  have h1 : ∀ x, x ᵥ* g.val ∈ diagLat c ↔ x ∈ SplitFlip.stdLat k D := vecMul_diagGL_mem 1 c c (by simp)
  have h2 : ∀ x, x ᵥ* g.val ∈ u • diagLat c ↔ x ∈ u • SplitFlip.stdLat k D := fun x => by
    rw [SplitFlip.stdLat, smul_diagLat, smul_diagLat]
    exact vecMul_diagGL_mem _ _ c (by simp) x
  have h1' : ∀ x, x ᵥ* (g⁻¹).val ∈ SplitFlip.stdLat k D ↔ x ∈ diagLat c := fun x => by
    rw [← h1, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have h2' : ∀ x, x ᵥ* (g⁻¹).val ∈ u • SplitFlip.stdLat k D ↔ x ∈ u • diagLat c := fun x => by
    rw [← h2, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨R, hR, hXR⟩ := exists_rightInverse (SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1')
  have hZ' : GlobalTheory.FunObj.GivenAdm.CongM u (Z * (g⁻¹).val) :=
    GlobalTheory.FunObj.GivenAdm.mem_matLat_smul.1 fun i => (h2' (Z.row i)).2 (hZ i)
  obtain ⟨κ, ⟨hκ, hκ'⟩, hv⟩ := exists_mem_glLatCong hu (hZ'.mul_left (Y := R) hR)
  refine ⟨g⁻¹ * κ * g, ⟨fun x => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, h1, hκ, h1']
  · rw [show (g⁻¹ * κ * g).val - 1 = (g⁻¹).val * (κ.val - 1) * g.val by
      rw [mul_sub, sub_mul, mul_one, Units.inv_mul, Units.val_mul, Units.val_mul],
      ← vecMul_vecMul, ← vecMul_vecMul, h2]
    exact hκ' _ ((h1' x).2 hx)
  · rw [Units.val_mul, Units.val_mul, hv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_add,
      ← Matrix.mul_assoc _ R, hXR, Matrix.mul_one, Matrix.one_mul, ← Matrix.add_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]

end GlobalTheory.PrimFrameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.TowerFD

theorem exists_fd_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ),
    ∃ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν := by
  intro F E _ _ _ _ _ nS nT
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AF F ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (WOF F E nS nT) :=
    inferInstanceAs (LocallyCompactSpace (Fin nT → Fin nS → AF F ⊗[F] E))
  have : SecondCountableTopology (WOF F E nS nT) :=
    inferInstanceAs (SecondCountableTopology (Fin nT → Fin nS → AF F ⊗[F] E))
  have : T2Space (WOF F E nS nT) := inferInstanceAs (T2Space (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hdisc : DiscreteTopology (ratLF F E nS nT) := by
    obtain ⟨U, hU, hx⟩ := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
      (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
    have hN : (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => U) ∈
        nhds (0 : WOF F E nS nT) :=
      set_pi_mem_nhds Set.finite_univ fun _ _ => set_pi_mem_nhds Set.finite_univ fun _ _ => hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    rw [isOpen_singleton_iff_nhds_eq_pure]
    refine le_antisymm (Filter.le_pure_iff.2 ?_) (pure_le_nhds _)
    have hc : ContinuousAt (fun x : ratLF F E nS nT => (x : WOF F E nS nT)) 0 :=
      continuous_subtype_val.continuousAt
    refine Filter.mem_of_superset (hc.preimage_mem_nhds hN) ?_
    rintro ⟨_, y, rfl⟩ hy
    have hy0 : y = 0 := by
      funext i j
      exact hx _ (hy i (Set.mem_univ i) j (Set.mem_univ j))
    subst hy0
    exact Subtype.ext (map_zero _)
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hcov : ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈
      (Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :=
    fun x => ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  have tZ : IsTopologicalAddGroup (WOF F E nS nT) := inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (@GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) _ _ tZ _ _ _ _ _ (ratLF F E nS nT) hdisc _
      hKc hcov).1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

end GlobalTheory.TowerFD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveComplexStructureDarbouxPairStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_complex_structure_darboux_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  first | exact @GlobalTheory.GaussFockPair.exists_pos_complex_structure | exact GlobalTheory.GaussFockPair.exists_pos_complex_structure | (intros; apply GlobalTheory.GaussFockPair.exists_pos_complex_structure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsFixedLevelKtypes
section
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory Topology

noncomputable section

namespace GlobalTheory.HCFCusp

theorem finiteDimensional_cuspSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  intro E _ _ _ a L hL W _ χ N ν _ α _ _
  have hopen : ∀ φ : Sm E a, (∀ k ∈ L, finRep E a k φ = φ) → IsOpen {k | finRep E a k φ = φ} := by
    intro φ hφ
    rw [isOpen_iff_forall_mem_open]
    intro k hk
    refine ⟨(k * ·) '' (L : Set (GL (Fin a) (Af E))), ?_, isOpenMap_mul_left k _ hL, ⟨1, L.one_mem, mul_one k⟩⟩
    rintro _ ⟨l, hl, rfl⟩
    change finRep E a (k * l) φ = φ
    rw [map_mul, Module.End.mul_apply, hφ l hl]
    exact hk
  refine _root_.GlobalTheory.HCF.finiteDimensional_cuspGL E a L hL W ‹_› {χ} (Set.finite_singleton χ) N _
    (Submodule.span_mono fun φ hφ => hφ.1) ?_
  intro φ hφ
  have P : (∀ k ∈ L, finRep E a k φ = φ) ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsCuspidal φ.1 := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨hx.1.2.1, hx.1.1.left, hx.2⟩
    | zero =>
      refine ⟨fun k _ => map_zero _, fun _ _ => rfl, fun r _ _ _ _ μ 𝓕 _ _ g => ?_⟩
      change ∫ z in 𝓕, (0 : ℂ) ∂μ = 0
      exact integral_zero _ _
    | add x y _ _ hx hy =>
      refine ⟨fun k hk => by rw [map_add (f := _), hx.1 k hk, hy.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change x.1 _ + y.1 _ = x.1 g + y.1 g
        rw [hx.2.1, hy.2.1]
      · haveI := hμ
        have ix := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a x (hopen x hx.1)) hx.2.1 μ h𝓕 g
        have iy := GlobalTheory.CuspRep.CuspidalL2GL.integrableOn_unip
          (ContAut.continuous_of_isOpen_stab E a y (hopen y hy.1)) hy.2.1 μ h𝓕 g
        change ∫ z in 𝓕, (x.1 (unip z * g) + y.1 (unip z * g)) ∂μ = 0
        rw [integral_add ix iy, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, hy.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, add_zero]
    | smul c x _ hx =>
      refine ⟨fun k hk => by rw [map_smul, hx.1 k hk], fun γ g => ?_, fun r h0 h1 _ _ μ 𝓕 hμ h𝓕 g => ?_⟩
      · change c * x.1 _ = c * x.1 g
        rw [hx.2.1]
      · change ∫ z in 𝓕, c * x.1 (unip z * g) ∂μ = 0
        rw [integral_const_mul, hx.2.2 r h0 h1 μ 𝓕 hμ h𝓕 g, mul_zero]
  exact P.2.2

end GlobalTheory.HCFCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_integral_fin_sum_compact : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  first | exact @GlobalTheory.CxForm.IntegralSum.integral_sum | exact GlobalTheory.CxForm.IntegralSum.integral_sum | (intros; apply GlobalTheory.CxForm.IntegralSum.integral_sum <;> assumption)
end

