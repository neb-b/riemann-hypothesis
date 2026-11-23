module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussianQuadFormRationalCoordsHermitian
section
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.GaussDict

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem exists_emb_comb_transpose (w : (E →+* ℂ) → ℂ) :
    ∃ c : Fin (Module.finrank ℚ E) → ℂ, ∀ σ : E →+* ℂ,
      ∑ j, σ (Module.finBasis ℚ E j) * c j = w σ := by
  classical
  let e : (E →+* ℂ) ≃ Fin (Module.finrank ℚ E) :=
    Fintype.equivFinOfCardEq (NumberField.Embeddings.card E ℂ)

  let A : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ :=
    Matrix.of fun i j => e.symm i (Module.finBasis ℚ E j)
  have hT : Function.Surjective Aᵀ.mulVec := by
    intro c
    obtain ⟨w', hw'⟩ := GlobalTheory.SW.Dict.exists_emb_comb (E := E) c
    refine ⟨fun i => w' (e.symm i), funext fun j => ?_⟩
    rw [← hw' j]
    exact e.symm.sum_comp (fun σ => σ (Module.finBasis ℚ E j) * w' σ)
  have hA : IsUnit A := by
    have h := Matrix.mulVec_surjective_iff_isUnit.mp hT
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] at h
    exact (Matrix.isUnit_iff_isUnit_det _).mpr h
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA (fun i => w (e.symm i))
  refine ⟨c, fun σ => ?_⟩
  have h := congrFun hc (e σ)
  simpa [Matrix.mulVec, dotProduct, A] using h

theorem exists_coords {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (v v' : Ψ → Fin N → ℂ) :
    ∃ u : QI E N → ℂ, ∀ (τ : Ψ) (a : Fin N),
      ∑ j, τ.1 (Module.finBasis ℚ E j) * u (a, j) = v τ a ∧
      ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (a, j) = v' τ a := by
  classical
  have hc : ∀ σ : E →+* ℂ, σ ∉ Ψ → ComplexEmbedding.conjugate σ ∈ Ψ := fun σ hσ => by
    rw [hΨ, ComplexEmbedding.involutive_conjugate E σ]
    exact hσ

  let w : Fin N → (E →+* ℂ) → ℂ := fun a σ =>
    if h : σ ∈ Ψ then v ⟨σ, h⟩ a else v' ⟨_, hc σ h⟩ a
  choose c hc' using fun a => exists_emb_comb_transpose (w a)
  refine ⟨fun p => c p.1 p.2, fun τ a => ⟨?_, ?_⟩⟩
  · rw [hc' a τ.1]
    simp [w, τ.2]
  · have hn : ComplexEmbedding.conjugate τ.1 ∉ Ψ := (hΨ τ.1).mp τ.2
    have h := hc' a (ComplexEmbedding.conjugate τ.1)
    simp only [ComplexEmbedding.conjugate_coe_eq] at h
    rw [h]
    simp only [w, dif_neg hn]
    exact congrArg (fun t => v' t a) (Subtype.ext (ComplexEmbedding.involutive_conjugate E τ.1))

theorem im_tauOf (Ψ : Finset (E →+* ℂ)) (Z : CM Ψ N N) :
    ((tauOf Ψ Z).map fun t => (t.im : ℂ)) = tauOf Ψ (fun τ => imH (Z τ)) := by
  ext p q
  simp only [Matrix.map_apply, tauOf, Matrix.of_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Complex.im_eq_sub_conj, map_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
    Complex.star_def, smul_eq_mul, map_add, map_mul, Complex.conj_conj]
  ring

theorem tauOf_mulVec (Ψ : Finset (E →+* ℂ)) (Y : CM Ψ N N) (u : QI E N → ℂ) (p : QI E N) :
    (tauOf Ψ Y *ᵥ u) p = ∑ τ : Ψ, (τ.1 (Module.finBasis ℚ E p.2) *
      (Y τ *ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) p.1 +
      conj (τ.1 (Module.finBasis ℚ E p.2)) *
      ((Y τ)ᵀ *ᵥ fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) p.1) := by
  simp only [Matrix.mulVec, dotProduct, tauOf, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem zetaOf_dot (Ψ : Finset (E →+* ℂ)) (z z' : CM Ψ n N) (k : Fin n) (u : QI E N → ℂ) :
    zetaOf Ψ z z' k ⬝ᵥ u = ∑ τ : Ψ,
      (z τ k ⬝ᵥ (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) +
      z' τ k ⬝ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) := by
  simp only [dotProduct, zetaOf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring

end GlobalTheory.SW.GaussDict

private theorem exists_tauOf_mulVec_eq_zetaOf {E : Type} [Field E] [NumberField E] {Ψ : Finset (E →+* ℂ)}
    (hΨ : IsType Ψ) {m N : ℕ} (Y : CM Ψ N N) (hY : ∀ τ, IsUnit (Y τ)) (z z' : CM Ψ m N)
    (k : Fin m) :
    ∃ u : QI E N → ℂ, tauOf Ψ Y *ᵥ u = zetaOf Ψ z z' k ∧
      zetaOf Ψ z z' k ⬝ᵥ u = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (Y τ)⁻¹ *ᵥ z τ k := by
  obtain ⟨u, hu⟩ := GlobalTheory.SW.GaussDict.exists_coords hΨ (fun τ => ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k)
    (fun τ => (Y τ)⁻¹ *ᵥ z τ k)
  have h1 : ∀ τ : Ψ, (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) =
      ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k := fun τ => funext fun a => (hu τ a).1
  have h2 : ∀ τ : Ψ, (fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) =
      (Y τ)⁻¹ *ᵥ z τ k := fun τ => funext fun a => (hu τ a).2
  have hY1 : ∀ τ, Y τ * (Y τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  have hY2 : ∀ τ, (Y τ)ᵀ * ((Y τ)ᵀ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  refine ⟨u, funext fun p => ?_, ?_⟩
  · rw [GlobalTheory.SW.GaussDict.tauOf_mulVec]
    simp only [h1, h2, Matrix.mulVec_mulVec, hY1, hY2, Matrix.one_mulVec, zetaOf]
    exact Finset.sum_congr rfl fun τ _ => by ring
  · rw [GlobalTheory.SW.GaussDict.zetaOf_dot]
    simp only [h1, h2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
    ring

theorem GlobalTheory.SW.gauss_form_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  intro E _ _ _ Ψ hΨ n N Z hZ z z' k
  rw [GlobalTheory.SW.GaussDict.im_tauOf]
  have hY : ∀ τ : Ψ, IsUnit (imH (Z τ)) := fun τ =>
    ((show ∀ τ : Ψ, (imH (Z τ)).PosDef from hZ) τ).isUnit
  have hsurj : Function.Surjective (tauOf Ψ fun τ => imH (Z τ)).mulVec := fun ξ => by
    obtain ⟨w, w', hw⟩ := GlobalTheory.SW.Dict.zetaOf_surj (n := 1) hΨ (fun _ => ξ)
    obtain ⟨u, hu, -⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY w w' 0
    exact ⟨u, by rw [hu, hw]⟩
  have hU := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  obtain ⟨u, hu, hdot⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY z z' k
  have hinv : (tauOf Ψ fun τ => imH (Z τ))⁻¹ *ᵥ zetaOf Ψ z z' k = u := by
    rw [← hu, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  rw [hinv, hdot]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real


open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.thH_summable_and_inj : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin N) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N,
      (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ x Z z z')‖) ∧
      ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
        (∀ z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thH Ψ ψ Z z z') → φ = ψ := by
  intro E _ _ _ Ψ hΨ n N φ hφ Z hZ
  obtain ⟨hbij, hup, hsurj, hdict, hSB⟩ := _root_.GlobalTheory.SW.thH_eq_thS_dictionary E Ψ hΨ n N
  classical
  have hexp : ∀ (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
      (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ),
      cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ (_root_.GlobalTheory.SW.ofQ m) Z z z') =
        cexp (π * I * ∑ k, (_root_.GlobalTheory.SW.qv (m k) ⬝ᵥ
          (_root_.GlobalTheory.SW.tauOf Ψ Z) *ᵥ _root_.GlobalTheory.SW.qv (m k) +
          2 * _root_.GlobalTheory.SW.qv (m k) ⬝ᵥ (_root_.GlobalTheory.SW.zetaOf Ψ z z') k)) := by
    intro z z' m
    have h := hdict (fun x => if x = _root_.GlobalTheory.SW.ofQ m then 1 else 0) Z z z'
    unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.thS at h
    rw [tsum_eq_single (_root_.GlobalTheory.SW.ofQ m), tsum_eq_single m] at h
    · simpa using h
    all_goals (intro b hb; simp [hbij.1.eq_iff, hb])
  refine ⟨fun z z' => ?_, fun ψ hψ hθ => ?_⟩
  · rw [← (Equiv.ofBijective _ hbij).summable_iff]
    have hs := _root_.GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) _ (hup Z hZ)
      (_root_.GlobalTheory.SW.zetaOf Ψ z z')
    refine hs.congr fun m => ?_
    simp only [Function.comp_apply, Equiv.ofBijective_apply, hexp]
  · have h := _root_.GlobalTheory.SW.eq_of_thS_eq _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
      (fun m => ψ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) ((hSB ψ).1 hψ) _ (hup Z hZ)
      (fun ζ => by
        obtain ⟨z, z', rfl⟩ := hsurj ζ
        rw [← hdict, ← hdict]
        exact hθ z z')
    funext x
    obtain ⟨m, rfl⟩ := hbij.2 x
    exact congrFun h m
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LinearIndependentMul
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.LagRep

theorem linearIndependent_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E)
    (hW : LinearIndependent E (fun i => W i)) : LinearIndependent E (fun i => (b * W) i) := by
  have h1 : Function.Injective W.vecMul := Matrix.vecMul_injective_iff.mpr hW
  have h2 : Function.Injective b.vecMul :=
    Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det b).mpr hb.isUnit)
  refine Matrix.vecMul_injective_iff.mp ?_
  intro s t hst
  apply h2
  apply h1
  simpa only [Matrix.vecMul_vecMul] using hst

theorem span_mul_le {E κ ι : Type} [Field E] [Fintype κ]
    (b : Matrix κ κ E) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) ≤
      Submodule.span E (Set.range fun i => W i) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : (b * W) i = ∑ k, b i k • W k := by
    ext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  show (b * W) i ∈ Submodule.span E (Set.range fun i => W i)
  rw [this]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_mul {E κ ι : Type} [Field E] [Fintype κ] [DecidableEq κ]
    (b : Matrix κ κ E) (hb : b.det ≠ 0) (W : Matrix κ ι E) :
    Submodule.span E (Set.range fun i => (b * W) i) =
      Submodule.span E (Set.range fun i => W i) := by
  refine le_antisymm (span_mul_le b W) ?_
  have := span_mul_le b⁻¹ (b * W)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hb.isUnit, Matrix.one_mul] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ccT_ccT' {α β : Type} (A : Matrix α β E) : ccT (ccT A) = A := by
  ext i j
  simp [ccT, cc]

theorem ccT_mul' {α β δ : Type} [Fintype β] (A : Matrix α β E) (B : Matrix β δ E) :
    ccT (A * B) = ccT B * ccT A := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]

theorem lower_rows {N : ℕ} (γ : M2 E N) (hγ : γ ∈ UU E N) :
    LinearIndependent E (fun i => (γ.submatrix Sum.inr id) i) ∧
      γ.submatrix Sum.inr id * Matrix.J (Fin N) E * ccT (γ.submatrix Sum.inr id) = 0 := by
  obtain ⟨⟨hdet, -, hc, -⟩, -⟩ := unitary_act_halfSpace E ∅ N γ hγ
  constructor
  · have h : LinearIndependent E (fun i => γ i) :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det γ).mpr hdet)
    exact h.comp Sum.inr Sum.inr_injective
  · have h : γ * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := by
      have : ccT (ccT γ) * Matrix.J (Fin N) E * ccT γ = Matrix.J (Fin N) E := hc
      rwa [ccT_ccT'] at this
    ext i j
    have h' : (γ * Matrix.J (Fin N) E * ccT γ) (Sum.inr i) (Sum.inr j) = 0 := by
      rw [h]
      simp [Matrix.J]
    exact h'

theorem exists_rep_den : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ),
    ∃ c : ℕ, 0 < c ∧ ∀ U : Lag E N, ∃ γ ∈ UU E N, Den c γ ∧ botSpan γ = U.1 := by
  intro E _ _ _ N
  classical
  obtain ⟨c, C, hc, hprim⟩ := exists_nearly_primitive E N
  obtain ⟨c', hc', hext⟩ := RowExt.exists_unitary_ext E N c hc
  refine ⟨c', hc', ?_⟩
  rintro ⟨U, γ₀, hγ₀, rfl⟩
  obtain ⟨hli, hiso⟩ := lower_rows γ₀ hγ₀
  set W₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E := γ₀.submatrix Sum.inr id with hW₀
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin N × (Fin N ⊕ Fin N) => W₀ p.1 p.2)
  set D : Matrix (Fin N) (Fin N) E := (d : E) • (1 : Matrix (Fin N) (Fin N) E) with hD
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Int.cast_ne_zero.mpr hd)
  have hDint : IntM (D * W₀) := by
    intro i j
    have := hint (W₀ i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    rw [hD, Matrix.smul_mul, Matrix.one_mul]
    simpa [zsmul_eq_mul] using this
  obtain ⟨a, ha, -, haint, hap⟩ := hprim _ (D * W₀) hDint (linearIndependent_mul D hDdet W₀ hli)
  obtain ⟨γ, hγ, hden, hrows⟩ := hext (a * (D * W₀)) haint
    (linearIndependent_mul a ha _ (linearIndependent_mul D hDdet W₀ hli))
    (by
      have : a * (D * W₀) * Matrix.J (Fin N) E * ccT (a * (D * W₀)) =
          a * D * (W₀ * Matrix.J (Fin N) E * ccT W₀) * (ccT D * ccT a) := by
        simp only [ccT_mul', Matrix.mul_assoc]
      rw [this, hiso, Matrix.mul_zero, Matrix.zero_mul]) hap
  refine ⟨γ, hγ, hden, ?_⟩
  show botSpan γ = botSpan γ₀
  unfold botSpan
  simp only [hrows]
  rw [span_mul a ha, span_mul D hDdet]
  rfl

end GlobalTheory.SW.LagRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PosSemidefSubMulConjTranspose
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

variable {N : ℕ}

theorem norm_det_le_add_posSemidef (A P : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (hP : P.PosSemidef) : ‖A.det‖ ≤ ‖(A + P).det‖ := by
  have h1 : imH (I • A) = A := by
    have := imH_add_I_smul 0 A hA.1
    simpa [imH] using this
  have h := (norm_det_denom_mono N 1 0 (I • A) P (by simp) (by simpa using Matrix.PosDef.one)
    (by rwa [h1]) hP).2
  simpa [← smul_add, det_smul] using h

theorem star_dotProduct_self_eq_sum (x : Fin N → ℂ) :
    star x ⬝ᵥ x = ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul']

theorem posSemidef_sub_mul_conjTranspose (X : Matrix (Fin N) (Fin N) ℂ) (B : ℝ)
    (hX : ∀ a b, ‖X a b‖ ≤ B) :
    ((((N : ℝ) ^ 2 * B ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine IsHermitian.sub ?_ (isHermitian_mul_conjTranspose_self X)
    simp [IsHermitian]
  · have h1 : star x ⬝ᵥ (X * Xᴴ) *ᵥ x = star (Xᴴ *ᵥ x) ⬝ᵥ (Xᴴ *ᵥ x) := by
      rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec]
    rw [sub_mulVec, dotProduct_sub, h1, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self_eq_sum, star_dotProduct_self_eq_sum, smul_eq_mul, ← ofReal_mul,
      ← ofReal_sub, Complex.zero_le_real, sub_nonneg]
    have h2 : ∀ a, ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ B ^ 2 * (N * ∑ b, ‖x b‖ ^ 2) := by
      intro a
      have h3 : ‖(Xᴴ *ᵥ x) a‖ ≤ B * ∑ b, ‖x b‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le Finset.univ fun b => Xᴴ a b * x b).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, conjTranspose_apply, norm_star]
        exact mul_le_mul_of_nonneg_right (hX b a) (norm_nonneg _)
      have h4 : (∑ b, ‖x b‖) ^ 2 ≤ N * ∑ b, ‖x b‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun b => ‖x b‖)
      calc ‖(Xᴴ *ᵥ x) a‖ ^ 2 ≤ (B * ∑ b, ‖x b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ = B ^ 2 * (∑ b, ‖x b‖) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left h4 (sq_nonneg B)
    refine (Finset.sum_le_sum fun a _ => h2 a).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem denom_mul_conjTranspose (C D X : Matrix (Fin N) (Fin N) ℂ) (h : (C * Dᴴ).IsHermitian)
    (hX : X.IsHermitian) (δ : ℝ) :
    (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ =
      (C * X + D) * (C * X + D)ᴴ + ((δ : ℂ) ^ 2) • (C * Cᴴ) := by
  have h1 : D * Cᴴ = C * Dᴴ := by simpa using h.eq
  have h2 : star (I * δ : ℂ) = -(I * δ) := by simp
  have h3 : (δ : ℂ) ^ 2 = -((I * δ) * (I * δ)) := by
    have : I * δ * (I * δ) = (I * I) * (δ : ℂ) ^ 2 := by ring
    rw [this, I_mul_I]; ring
  rw [h3]
  generalize (I * δ : ℂ) = t at h2 ⊢
  simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, conjTranspose_one, hX.eq, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h1]
  module

theorem norm_det_mul_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    (A * Aᴴ).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_mul, det_conjTranspose, star_def, Complex.mul_conj']
  simp

theorem norm_det_denom_compare :
    ∀ (N : ℕ) (δ B : ℝ), 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C D Z : Matrix (Fin N) (Fin N) ℂ, (C * Dᴴ).IsHermitian → (C * Cᴴ + D * Dᴴ).PosDef → (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → (∀ a b, ‖(Z + Zᴴ) a b‖ ≤ B) → c * ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ≤ ‖(C * Z + D).det‖ ∧ ‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 = (C * Cᴴ + D * Dᴴ).det.re := by
  intro N δ B hδ
  set K : ℝ := (N : ℝ) ^ 2 * (B / 2) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := δ ^ 2 / (2 * δ ^ 2 + 1 + 2 * K) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : 0 ≤ 1 - 2 * c := by
    rw [hc, sub_nonneg, ← mul_div_assoc, div_le_one (by positivity)]
    linarith
  have hc2 : 0 ≤ δ ^ 2 - c - 2 * c * K := by
    have : c * (2 * δ ^ 2 + 1 + 2 * K) = δ ^ 2 := by rw [hc]; field_simp
    nlinarith [mul_pos hc0 (pow_pos hδ 2)]
  refine ⟨Real.sqrt (c ^ N), by positivity, fun C D Z h hp hZ hB => ?_⟩
  have hG : (C * Cᴴ + D * Dᴴ).det =
      ((‖(C * (I • (1 : Matrix (Fin N) (Fin N) ℂ)) + D).det‖ ^ 2 : ℝ) : ℂ) := by
    have := denom_mul_conjTranspose C D 0 h isHermitian_zero 1
    rw [← norm_det_mul_conjTranspose]
    simp only [ofReal_one, mul_one, zero_add, Matrix.mul_zero, one_pow, one_smul] at this
    rw [this, add_comm]
  refine ⟨?_, by rw [hG, ofReal_re]⟩
  set X : Matrix (Fin N) (Fin N) ℂ := (2⁻¹ : ℂ) • (Z + Zᴴ) with hXdef
  have hX : X.IsHermitian := by
    simp [hXdef, IsHermitian, add_comm]
  have hXB : ∀ a b, ‖X a b‖ ≤ B / 2 := by
    intro a b
    have := hB a b
    rw [hXdef, Matrix.smul_apply, norm_smul]
    simp only [norm_inv, Complex.norm_ofNat]
    linarith
  have hone : ((δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hδ)
  have him : imH (X + (I * δ) • 1) = (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    rw [mul_smul, imH_add_I_smul _ _ hone.1, imH, hX.eq]
    simp
  have hZe : X + (I * δ) • 1 + I • (imH Z - (δ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = Z := by
    have h2 : I * (2 * I)⁻¹ = 2⁻¹ := by field_simp
    rw [smul_sub, imH, smul_smul, smul_smul, h2, hXdef]
    module
  have hm := (norm_det_denom_mono N C D (X + (I * δ) • 1) _ h hp (by rwa [him]) hZ).2
  rw [hZe] at hm
  refine le_trans ?_ hm
  have hP : ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)).PosSemidef := by
    refine (((posSemidef_self_mul_conjTranspose _).smul ?_).add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)).add
      (((posSemidef_sub_mul_conjTranspose X _ hXB).mul_mul_conjTranspose_same C).smul ?_) |>.add
      ((posSemidef_self_mul_conjTranspose _).smul ?_)
    · exact Complex.zero_le_real.2 hc1
    · exact Complex.zero_le_real.2 hc2
    · exact Complex.zero_le_real.2 (by positivity)
    · exact Complex.zero_le_real.2 hc0.le
  have hd := norm_det_le_add_posSemidef _ _ (hp.smul (Complex.zero_lt_real.2 hc0)) hP
  have he : (c : ℂ) • (C * Cᴴ + D * Dᴴ) + ((((1 - 2 * c : ℝ)) : ℂ) • ((C * X + D) * (C * X + D)ᴴ) +
      ((δ ^ 2 - c - 2 * c * K : ℝ) : ℂ) • (C * Cᴴ) +
      ((2 * c : ℝ) : ℂ) • (C * ((K : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X * Xᴴ) * Cᴴ) +
      (c : ℂ) • ((C * X + D + C * X) * (C * X + D + C * X)ᴴ)) =
      (C * (X + (I * δ) • 1) + D) * (C * (X + (I * δ) • 1) + D)ᴴ := by
    rw [denom_mul_conjTranspose C D X h hX]
    push_cast
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
    module
  rw [he, norm_det_mul_conjTranspose, det_smul, hG, ← ofReal_pow, ← ofReal_mul, norm_real,
    norm_real, Fintype.card_fin, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hd
  refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity)]

end GlobalTheory.SW
end

