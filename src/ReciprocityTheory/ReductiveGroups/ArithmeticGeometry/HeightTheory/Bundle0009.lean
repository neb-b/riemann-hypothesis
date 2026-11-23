module

public import ReciprocityTheory.SemistableReduction.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulEmbeddingColumns
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

section Proj

variable {K : Type} [Field K] {r k : ℕ}

noncomputable def hBm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l j => σ (b j l)

noncomputable def hPm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin r) ℂ :=
  1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ

noncomputable def hns {r : ℕ} (x : Fin r → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

private theorem linearIndependent_map_ringHom_complex' (σ : K →+* ℂ) {s : Type*} [Fintype s] {v : s → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  let A : Matrix (Fin r) s K := Matrix.of fun l i => v i l
  have hAv : ∀ t : s → K, A *ᵥ t = ∑ i, t i • v i := by
    intro t
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    have h1 : ∑ i, t i • v i = 0 := by rw [← hAv]; exact ht
    funext i
    exact Fintype.linearIndependent_iff.mp hv t h1 i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hker
  have hLA : LinearMap.toMatrix' g * A = 1 := by
    have e : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    have := congrArg LinearMap.toMatrix' hg
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
    rwa [e] at this
  have hLAσ : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hLA]
    exact Matrix.map_one σ (map_zero σ) (map_one σ)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hAc : A.map σ *ᵥ c = 0 := by
    rw [← hc]
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hc0 : c = 0 := by
    calc c = ((LinearMap.toMatrix' g).map σ * A.map σ) *ᵥ c := by rw [hLAσ, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hAc, Matrix.mulVec_zero]
  intro i
  rw [hc0]
  rfl

theorem linearIndependent_map_embedding (σ : K →+* ℂ) {ι : Type*} {v : ι → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_map_ringHom_complex' σ (hv.comp (Subtype.val : s → ι) Subtype.val_injective)

theorem embeddingColumns_mulVec (σ : K →+* ℂ) (b : Fin k → Fin r → K) (z : Fin k → ℂ) :
    hBm σ b *ᵥ z = ∑ j, z j • fun l => σ (b j l) := by
  funext l
  simp [hBm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem isUnit_det_embeddingGram (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    IsUnit ((hBm σ b)ᴴ * hBm σ b).det := by
  have hli := linearIndependent_map_embedding σ hb
  have hinj : Function.Injective (hBm σ b).mulVec := by
    intro x y hxy
    have h1 : ∑ j, (x - y) j • (fun l => σ (b j l)) = 0 := by
      rw [← embeddingColumns_mulVec, Matrix.mulVec_sub, hxy, sub_self]
    have h2 := Fintype.linearIndependent_iff.mp hli (x - y) h1
    funext j
    exact sub_eq_zero.mp (h2 j)
  have hker : LinearMap.ker ((hBm σ b)ᴴ * hBm σ b).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self, LinearMap.ker_eq_bot]
    exact hinj
  have hinj2 : Function.Injective ((hBm σ b)ᴴ * hBm σ b).mulVec := LinearMap.ker_eq_bot.mp hker
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj2)

theorem conjTranspose_mul_orthogonalProjector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    (hBm σ b)ᴴ * hPm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, sub_self]

theorem orthogonalProjector_mul_embeddingColumns (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hBm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_one, sub_self]

theorem orthogonalProjector_conjTranspose (σ : K →+* ℂ) (b : Fin k → Fin r → K) : (hPm σ b)ᴴ = hPm σ b := by
  simp only [hPm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem orthogonalProjector_mul_self (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hPm σ b = hPm σ b := by
  have h := conjTranspose_mul_orthogonalProjector σ hb
  calc hPm σ b * hPm σ b
      = (1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) * hPm σ b := rfl
    _ = hPm σ b - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * ((hBm σ b)ᴴ * hPm σ b) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = hPm σ b := by rw [h, Matrix.mul_zero, sub_zero]

theorem orthogonalProjector_orthogonal (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (v : Fin r → ℂ) (y : Fin k → ℂ) : star (hPm σ b *ᵥ v) ⬝ᵥ (hBm σ b *ᵥ y) = 0 := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_embeddingColumns σ hb, Matrix.vecMul_zero, zero_dotProduct]

theorem normSqSum_add_of_orthogonal {r : ℕ} (a c : Fin r → ℂ) (h : star a ⬝ᵥ c = 0) :
    hns (a + c) = hns a + hns c := by
  unfold hns
  have h' : ∑ i, (a i * (starRingEnd ℂ) (c i)).re = 0 := by
    have h1 : ∑ i, a i * (starRingEnd ℂ) (c i) = (starRingEnd ℂ) (star a ⬝ᵥ c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [← Complex.re_sum, h1, h, map_zero, Complex.zero_re]
  simp only [Pi.add_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, h', mul_zero, add_zero]

theorem orthogonalProjector_mulVec_ne_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∉ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) ≠ 0 := by
  intro h0
  have hli := linearIndependent_map_embedding σ ((linearIndependent_finCons).mpr ⟨hb, hq⟩)
  have hcons : (fun i l => σ ((Fin.cons q b : Fin (k + 1) → Fin r → K) i l)) =
      (Fin.cons (fun l => σ (q l)) (fun j l => σ (b j l)) : Fin (k + 1) → Fin r → ℂ) := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [hcons, linearIndependent_finCons] at hli
  apply hli.2
  have hv : (fun i => σ (q i)) =
      (hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) *ᵥ fun i => σ (q i) := by
    unfold hPm at h0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  have hv2 : (fun i => σ (q i)) =
      hBm σ b *ᵥ (((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ fun i => σ (q i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hv
  rw [hv2, embeddingColumns_mulVec]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem orthogonalProjector_mulVec_eq_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∈ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hq
  have h1 : (fun i => σ ((∑ j, c j • b j) i)) = hBm σ b *ᵥ fun j => σ (c j) := by
    rw [embeddingColumns_mulVec]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum, map_mul]
  rw [h1, Matrix.mulVec_mulVec, orthogonalProjector_mul_embeddingColumns σ hb, Matrix.zero_mulVec]

end Proj

section PT

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem crossGram_eq_embeddingColumns (σ : K →+* ℂ) {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramX 1 σ b c = (hBm σ b)ᴴ * hBm σ c := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramX, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem gramMatrix_eq_embeddingColumns (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC 1 σ b = (hBm σ b)ᴴ * hBm σ b := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem quotientGram_eq_projector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) (i j : Fin m) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c i j =
      star (hPm σ b *ᵥ fun l => σ (c i l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (c j l)) := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin r) (Fin m) ℂ) (i j : Fin m),
      (Cᴴ * M * C) i j = star (fun l => C l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
    intro M C i j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hq : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
    rw [gramMatrix_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, crossGram_eq_embeddingColumns]
    unfold hPm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hq, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_self σ hb]
  rfl

end PT

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValPlRes
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace ValPl

open IsDedekindDomain WithZero IsLocalRing

variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]

variable (F) in
theorem resDeg_addv (v : HeightOneSpectrum (integralClosure O L)) :
    letI := resAlg (F := F) (addv L v);
    Module.finrank (ResidueField ((vRing (addv L v)).comap (algebraMap F L)))
      (ResidueField (vRing (addv L v))) = v.asIdeal.inertiaDeg O := by
  classical
  set w := addv L v with hw_def
  letI : Algebra (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w)) :=
    resAlg (F := F) w
  have hunit : ∀ x : vRing w, IsUnit x ↔ w (x : L) = 0 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have hm : ((u : vRing w) : L) * ((↑u⁻¹ : vRing w) : L) = 1 :=
        congrArg Subtype.val u.mul_inv
      have h1 : w ((u : vRing w) : L) + w ((↑u⁻¹ : vRing w) : L) = 0 := by
        rw [← AddValuation.map_mul, hm, AddValuation.map_one]
      exact wt_add_eq_zero (u : vRing w).2 (↑u⁻¹ : vRing w).2 h1
    · intro h0
      have hx0 : (x : L) ≠ 0 := fun h => by
        rw [h, AddValuation.map_zero] at h0; exact WithTop.top_ne_zero h0
      have hinv : (x : L)⁻¹ ∈ vRing w := by
        show 0 ≤ w (x : L)⁻¹
        have h2 : w (x : L) + w (x : L)⁻¹ = 0 := by
          rw [← AddValuation.map_mul, mul_inv_cancel₀ hx0, AddValuation.map_one]
        rw [h0, zero_add] at h2
        rw [h2]
      exact ⟨⟨x, ⟨_, hinv⟩, Subtype.ext (by simp [mul_inv_cancel₀ hx0]),
        Subtype.ext (by simp [inv_mul_cancel₀ hx0])⟩, rfl⟩
  have hmaxV : ∀ x : vRing w, x ∈ maximalIdeal (vRing w) ↔ 0 < w (x : L) := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne x.2 (Ne.symm h), fun h => h.ne'⟩

  let φB : integralClosure O L →+* vRing w :=
    (algebraMap (integralClosure O L) L).codRestrict (vRing w) (fun b => addv_nonneg v b)
  let ψB : integralClosure O L →+* ResidueField (vRing w) := (residue (vRing w)).comp φB
  have hψB : ∀ b, ψB b = residue (vRing w) (φB b) := fun _ => rfl
  have hkerB : RingHom.ker ψB = v.asIdeal := by
    ext b
    rw [RingHom.mem_ker, hψB, IsLocalRing.residue_eq_zero_iff, hmaxV]
    exact addv_pos_iff v b
  haveI := v.isMaximal
  have hsurjB : Function.Surjective ψB := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    have hxv : v.valuation L (x : L) ≤ 1 := by
      by_cases hx0 : (x : L) = 0
      · rw [hx0, map_zero]; exact zero_le
      have h := x.2
      change 0 ≤ addv L v (x : L) at h
      rw [addv_apply v hx0] at h
      have h' : 0 ≤ -log (v.valuation L (x : L)) := by exact_mod_cast h
      have hne : v.valuation L (x : L) ≠ 0 := by simpa using hx0
      rw [← exp_log hne, ← exp_zero, exp_le_exp]
      omega
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (x : L) hxv
    obtain ⟨d', i, hi, hdi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal d.2
    refine ⟨n * d', ?_⟩
    have hd1 : ψB d * ψB d' = 1 := by
      have : d' * d - 1 ∈ RingHom.ker ψB := by
        rw [hkerB]
        have : d' * d - 1 = -i := by linear_combination hdi
        rw [this]; exact v.asIdeal.neg_mem hi
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero] at this
      rw [mul_comm]; exact this
    have hxd : x * φB d = φB n := Subtype.ext (by
      change (x : L) * algebraMap (integralClosure O L) L d = algebraMap (integralClosure O L) L n
      exact hnd)
    have hres := congrArg (residue (vRing w)) hxd
    rw [map_mul] at hres
    rw [map_mul, hψB n, ← hres, mul_assoc, ← hψB, hd1, mul_one]
  let jB : (integralClosure O L ⧸ v.asIdeal) ≃+* ResidueField (vRing w) :=
    (Ideal.quotEquivOfEq hkerB.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjB)

  have hOw : ∀ a : O, algebraMap O F a ∈ (vRing w).comap (algebraMap F L) := fun a => by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact ((addv_mem_placesOver v).2 a).1
  let φO : O →+* (vRing w).comap (algebraMap F L) := (algebraMap O F).codRestrict _ hOw
  let ψO : O →+* ResidueField ((vRing w).comap (algebraMap F L)) := (residue _).comp φO
  have hψO : ∀ a, ψO a = residue _ (φO a) := fun _ => rfl
  have hmaxV0 : ∀ x : (vRing w).comap (algebraMap F L),
      x ∈ maximalIdeal ((vRing w).comap (algebraMap F L)) ↔ 0 < w (algebraMap F L x) := by
    intro x
    have h := hmaxV (comapIncl (vRing w) (algebraMap F L) x)
    have e : ((comapIncl (vRing w) (algebraMap F L) x : vRing w) : L) = algebraMap F L x := rfl
    rw [e] at h
    rw [← h, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact ⟨fun hx hu => hx (isUnit_of_map_unit _ _ hu), fun hx hu => hx (hu.map _)⟩
  have hkerO : RingHom.ker ψO = maximalIdeal O := by
    ext a
    rw [RingHom.mem_ker, hψO, IsLocalRing.residue_eq_zero_iff, hmaxV0]
    change 0 < w (algebraMap F L (algebraMap O F a)) ↔ _
    rw [← IsScalarTower.algebraMap_apply]
    exact ((addv_mem_placesOver v).2 a).2
  have hsurjO : Function.Surjective ψO := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    by_cases hx0 : (x : F) = 0
    · refine ⟨0, ?_⟩
      rw [map_zero]
      have : x = 0 := Subtype.ext hx0
      rw [this, map_zero]
    rcases ValuationRing.isInteger_or_isInteger O (x : F) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, by rw [hψO]; congr 1; exact Subtype.ext ha⟩
    · by_cases hau : IsUnit a
      · obtain ⟨u, rfl⟩ := hau
        refine ⟨↑u⁻¹, ?_⟩
        rw [hψO]; congr 1
        apply Subtype.ext
        change algebraMap O F ↑u⁻¹ = (x : F)
        have h1 : algebraMap O F (u : O) * algebraMap O F ↑u⁻¹ = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 : algebraMap O F (u : O) = (x : F)⁻¹ := ha
        rw [h2] at h1
        field_simp at h1
        linear_combination h1
      · exfalso
        have ham : a ∈ maximalIdeal O := hau
        have hpos := (((addv_mem_placesOver v).2 a).2).2 ham
        rw [IsScalarTower.algebraMap_apply O F L, ha, map_inv₀] at hpos
        have hxnn : 0 ≤ w (algebraMap F L (x : F)) := x.2
        have hxL : algebraMap F L (x : F) ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ (algebraMap F L).injective]; exact hx0
        have hs : w (algebraMap F L (x : F)) + w (algebraMap F L (x : F))⁻¹ = 0 := by
          rw [← AddValuation.map_mul, mul_inv_cancel₀ hxL, AddValuation.map_one]
        have := wt_add_eq_zero hxnn hpos.le hs
        rw [this, zero_add] at hs
        rw [hs] at hpos
        exact lt_irrefl _ hpos
  let jO : (O ⧸ maximalIdeal O) ≃+* ResidueField ((vRing w).comap (algebraMap F L)) :=
    (Ideal.quotEquivOfEq hkerO.symm).trans (RingHom.quotientKerEquivOfSurjective hsurjO)
  have hmax : (v.asIdeal.comap (algebraMap O (integralClosure O L))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) v.asIdeal
  haveI : v.asIdeal.LiesOver (maximalIdeal O) := ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  have hc : (algebraMap (ResidueField ((vRing w).comap (algebraMap F L)))
      (ResidueField (vRing w))).comp jO.toRingHom =
      jB.toRingHom.comp (algebraMap (O ⧸ maximalIdeal O) (integralClosure O L ⧸ v.asIdeal)) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    simp only [RingHom.comp_apply, Ideal.Quotient.algebraMap_mk_of_liesOver]
    change ResidueField.map (comapIncl (vRing w) (algebraMap F L)) (jO _) = jB _
    simp only [jO, jB, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk, hψO, hψB, ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change algebraMap F L (algebraMap O F a) = algebraMap (integralClosure O L) L (algebraMap O _ a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) v.asIdeal]
  exact (Algebra.finrank_eq_of_equiv_equiv jO jB hc).symm

end ValPl

end ReciprocityTheory.ChartRestriction.G.T0
end

