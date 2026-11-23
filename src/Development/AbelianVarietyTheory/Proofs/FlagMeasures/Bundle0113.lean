module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientLatticeRealizedIsometrically
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuotientLatticeRealizedIsometricallyStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_lattice_realized_isometrically : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → ∃ (m : ℕ) (q : Matrix (Fin m) (Fin n) K) (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (Q : InfinitePlace K → Matrix (Fin m) (Fin n) ℂ), m + rkK S = rkK A ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, Q w * (Q w)ᴴ = 1) ∧ (∀ w, ∀ y ∈ A, fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) = Q w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ (∀ w z, (Q w)ᴴ *ᵥ z ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K)))) ∧ (∀ w, ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))) ∧ (∀ y ∈ S, q *ᵥ y = 0) ∧ Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ ∧ ∀ N', N' ≤ A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) → N' ≠ ⊥ → ∃ N, S < N ∧ N ≤ A ∧ sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X' N' := by
  intro K _ _ _ _ n X A S hX hA hSat
  have hSA : S ≤ A := hSat.1
  have hUU : Submodule.span K (S : Set (Fin n → K)) ≤ Submodule.span K (A : Set (Fin n → K)) :=
    Submodule.span_mono hSA
  obtain ⟨m, q, hm, hker, hsurj⟩ := GlobalTheory.QuotCoord.exists_quot_matrix _ _ hUU
  have hS : ∀ y ∈ S, q *ᵥ y = 0 := fun y hy =>
    (hker y (Submodule.subset_span (hSA hy))).2 (Submodule.subset_span hy)
  have htop : Submodule.span K
      (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ := by
    rw [← hsurj, Submodule.map_coe]
    exact Submodule.span_image (Matrix.toLin' q)
  have hQ := fun w => GlobalTheory.QuotCoord.exists_coisometry (m := m)
    (QuotientRealization.pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w)
    (QuotientRealization.pv (Pi.basisFun K (Fin n)) X (Submodule.span K (A : Set (Fin n → K))) w)
    (Submodule.span_mono (Set.image_mono hUU))
    (by rw [QuotientRealization.finrank_pv _ _ hX, QuotientRealization.finrank_pv _ _ hX]; exact hm)
  choose Q hQ1 hQ2 hQ3 hQ4 using hQ
  have hQ3' : ∀ w, ∀ u ∈ Submodule.span ℂ
      (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
      Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
    fun w u hu => QuotientRealization.pv_le _ X S w _ (hQ3 w _ (GlobalTheory.QuotCoord.toLp_mem_pv X A w u hu))
  have hY := fun w => GlobalTheory.QuotCoord.exists_frame X w (hX w) q A S hS htop (Q w) (hQ3' w)
  choose X' hX' hc using hY
  refine ⟨m, q, X', Q, hm, hX', hQ1, hc, fun w z => QuotientRealization.pv_le _ X A w _ (hQ2 w z), hQ3', hS, htop, ?_⟩
  intro N' hN' hne
  have hmap : (A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K))).map
      ((Matrix.toLin' q).restrictScalars (𝓞 K)) = N' := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hN' hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
  have hSN : S ≤ A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K)) := by
    intro y hy
    refine ⟨hSA hy, ?_⟩
    show q *ᵥ y ∈ N'
    rw [hS y hy]
    exact N'.zero_mem
  refine ⟨_, lt_of_le_of_ne hSN ?_, inf_le_left, ?_⟩
  · intro h
    apply hne
    rw [← hmap, ← h, eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact hS y hy
  have sizeQ_eq_size (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ w, IsUnit (X w).det)
      (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (hX' : ∀ w, IsUnit (X' w).det)
      (q : Matrix (Fin m) (Fin n) K) (A S N : Submodule (𝓞 K) (Fin n → K)) (hA : A.FG)
      (hSat : IsSat (realize (Pi.basisFun K (Fin n)) X) A S) (hSN : S ≤ N) (hNA : N ≤ A)
      (hker : ∀ y ∈ Submodule.span K (A : Set (Fin n → K)),
        q *ᵥ y = 0 ↔ y ∈ Submodule.span K (S : Set (Fin n → K)))
      (hnorm : ∀ w, ∀ y ∈ A, normAt (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) =
        ‖(QuotientRealization.pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w)ᗮ.starProjection
          (WithLp.toLp 2 (fcoord (Pi.basisFun K (Fin n)) X w y))‖) :
      sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X'
        (N.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) := by
    classical
    set U := Submodule.span K (S : Set (Fin n → K)) with hU
    set b := Pi.basisFun K (Fin n)
    set b'' := Pi.basisFun K (Fin m)
    have hNfg : N.FG := Submodule.FG.of_le hA hNA
    set N'' := N.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) with hN''
    have hUle : U ≤ Submodule.span K (N : Set (Fin n → K)) := Submodule.span_mono hSN
    have hrk : rkK N'' + rkK S = rkK N := by
      have hspan : Submodule.span K (N'' : Set (Fin m → K)) =
          (Submodule.span K (N : Set (Fin n → K))).map (Matrix.toLin' q) := by
        rw [hN'', Submodule.map_coe]
        exact Submodule.span_image (Matrix.toLin' q)
      let W := Submodule.span K (N : Set (Fin n → K))
      let fW : W →ₗ[K] (Fin m → K) := Matrix.toLin' q ∘ₗ W.subtype
      have h1 := LinearMap.finrank_range_add_finrank_ker fW
      have hr : LinearMap.range fW = W.map (Matrix.toLin' q) := by
        rw [LinearMap.range_comp, Submodule.range_subtype]
      have hk : LinearMap.ker fW = U.comap W.subtype := by
        ext y
        exact hker y (Submodule.span_mono hNA y.2)
      rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hUle).finrank_eq] at h1
      unfold rkK
      rw [hspan]
      exact h1
    have hrkR : ((rkK N : ℝ) - rkK S) = rkK N'' := by
      rw [← hrk]; push_cast; ring
    let ρ := realize b X
    let ρ'' := realize b'' X'
    have hNlat := plLat K _ _ b X hX N hNfg
    have hN''lat := plLat K _ _ b'' X' hX' N'' (hNfg.map _)
    have : DiscreteTopology (zl ρ N) := hNlat.1.2
    have hsatN : Formalism.F.IsSaturated (zl ρ N) (zl ρ S) :=
      ⟨QuotientRealization.zl_mono ρ hSN, fun x hx hxs => hSat.2.2 x (QuotientRealization.zl_mono ρ hNA hx) hxs⟩
    have : DiscreteTopology (Formalism.F.quot (zl ρ N) (zl ρ S)) :=
      (Formalism.F.degQuot _ _ _ inferInstance hsatN).1
    have : DiscreteTopology (zl ρ'' N'') := hN''lat.1.2
    let W := Submodule.span ℝ (zl ρ S : Set (EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)))
    let f : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2) :=
      (Wᗮ.starProjection.toLinearMap.toAddMonoidHom).comp (ρ.comp N.subtype.toAddMonoidHom)
    let g : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin m × Fin 2) :=
      ρ''.comp (((Matrix.toLin' q).toAddMonoidHom).comp N.subtype.toAddMonoidHom)
    have h1 : ∀ y, y ∈ Formalism.F.quot (zl ρ N) (zl ρ S) ↔ ∃ m : N, f m = y := by
      intro y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
    have h2 : ∀ y, y ∈ zl ρ'' N'' ↔ ∃ m : N, g m = y := by
      intro y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact ⟨Matrix.toLin' q x, ⟨x, hx, rfl⟩, rfl⟩
    have hn : ∀ m, ‖f m‖ = ‖g m‖ := by
      rintro ⟨x, hx⟩
      have hsq : ‖f ⟨x, hx⟩‖ ^ 2 = ‖g ⟨x, hx⟩‖ ^ 2 := by
        show ‖Wᗮ.starProjection (ρ x)‖ ^ 2 = ‖ρ'' (q *ᵥ x)‖ ^ 2
        rw [QuotientRealization.proj_norm_sq b X S x, PlaceOperatorNorms.norm_sq_realize]
        simp only [hnorm _ x (hNA hx)]
        rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
    have hcov := QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn
    have hht : htQ b X N S = ht b'' X' N'' := by
      unfold htQ ht
      rw [hcov, hrkR, ← Nat.cast_mul, Real.rpow_natCast]
    unfold sizeQ size
    rw [hht, hrkR]
  · rw [sizeQ_eq_size X hX X' hX' q A S _ hA hSat hSN inf_le_left hker ?_, hmap]
    intro w y hy
    rw [hQ4 w _ (GlobalTheory.QuotCoord.toLp_mem_pv X A w _ (Submodule.subset_span ⟨y, hy, rfl⟩)), normAt]
    exact congrArg cnorm (hc w y hy)

end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFinEqSumCastLEOfVanish
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorTri

theorem sum_fin_eq_sum_castLE_of_vanish {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ)
    (hf : ∀ k : Fin n, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin l, f (Fin.castLE hl k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) ((Fin.castLE_injective hl).injOn) (by simp) ?_ (by simp)
  intro k _ hk
  apply hf
  by_contra h
  exact hk ⟨⟨k.val, by omega⟩, by simp, rfl⟩

theorem leadBlock_lower_mul {n l : ℕ} (hl : l ≤ n) (c z : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, i < j → c i j = 0) :
    (c * z).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      c.submatrix (Fin.castLE hl) (Fin.castLE hl) * z.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => c (Fin.castLE hl i) k * z k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc _ k (by rw [Fin.lt_def]; have := i.isLt; simp only [Fin.val_castLE]; omega), zero_mul]

theorem leadBlock_mul_upper {n l : ℕ} (hl : l ≤ n) (z c : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, j < i → c i j = 0) :
    (z * c).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      z.submatrix (Fin.castLE hl) (Fin.castLE hl) * c.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => z (Fin.castLE hl i) k * c k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc k _ (by rw [Fin.lt_def]; have := j.isLt; simp only [Fin.val_castLE]; omega), mul_zero]

theorem leadMinor_lower_mul_mul_upper :
    ∀ (n : ℕ) (c z c' : Matrix (Fin n) (Fin n) ℂ), (∀ i j, i < j → c i j = 0) → (∀ i j, j < i → c' i j = 0) → ∀ (l : ℕ) (hl : l ≤ n), leadMinor (c * z * c') l hl = (∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) * c' (Fin.castLE hl i) (Fin.castLE hl i)) * leadMinor z l hl := by
  intro n c z c' hc hc' l hl
  have h1 : (c.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_lowerTriangular
    intro i j hij
    exact hc _ _ (show i < j from hij)
  have h2 : (c'.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c' (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_upperTriangular
    intro i j hij
    exact hc' _ _ (show j < i from hij)
  change ((c * z * c').submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
    _ * (z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
  rw [leadBlock_mul_upper hl _ _ hc', leadBlock_lower_mul hl _ _ hc, Matrix.det_mul, Matrix.det_mul,
    h1, h2, Finset.prod_mul_distrib]
  ring

end GlobalTheory.LeadMinorTri
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumInnerClassRepsIndep
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem sum_inner_classReps_indep : ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W), (∀ h v w, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ) → (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → ∀ (C C' : Type) [Fintype C] [Fintype C'] (s : C → Gf) (s' : C' → Gf), (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s c * (κ : Gf)) → (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s' c * (κ : Gf)) → ∀ φ φ' : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (∀ (γ : Γ) (x : Gf) (κ : K), φ' (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ' x)) → ∑ c, ⟪φ (s c), φ' (s c)⟫_ℂ = ∑ c, ⟪φ (s' c), φ' (s' c)⟫_ℂ := by
  intro Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'
  have hf : ∀ (γ : Γ) (x : Gf) (κ : K),
      ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ := by
    intro γ x κ
    rw [hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]
    have hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]
    have : (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [RCLike.conj_mul, hn]; simp
    rw [this, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf) :=
    ⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro c1 c2 h
      obtain ⟨γ1, κ1, h1⟩ := hg c1
      obtain ⟨γ2, κ2, h2⟩ := hg c2
      rw [h] at h1
      refine (hs (s c2)).unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩
      rw [h2, h1]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro c'
      obtain ⟨c, ⟨γ, κ, h⟩, -⟩ := hs (s' c')
      refine ⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩
      rw [h]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine Fintype.sum_bijective g hbij _ _ (fun c => ?_)
  obtain ⟨γ, κ, h⟩ := hg c
  have := hf γ (s' (g c)) κ
  rw [← h] at this
  exact this

end GlobalTheory
end

