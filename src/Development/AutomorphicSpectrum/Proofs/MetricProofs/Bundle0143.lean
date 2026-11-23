module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitian
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord

variable {I : Type} [Fintype I] [DecidableEq I]

theorem im_terms_separate (P Q R S : Matrix I I ℂ)
    (h : ∀ z w : I → ℂ, (z ⬝ᵥ P *ᵥ star w + z ⬝ᵥ Q *ᵥ w + star z ⬝ᵥ R *ᵥ star w
      + star z ⬝ᵥ S *ᵥ w).im = 0) :
    P = S.map star ∧ Q = R.map star := by
  have hs : ∀ (c : I) (γ : ℂ), star (Pi.single c γ : I → ℂ) = Pi.single c (star γ) := by
    intro c γ; ext i; by_cases hi : i = c
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  have he : ∀ (T : Matrix I I ℂ) (a b : I) (α β : ℂ),
      (Pi.single a α : I → ℂ) ⬝ᵥ T *ᵥ (Pi.single b β : I → ℂ) = α * β * T a b := by
    intro T a b α β
    simp [single_dotProduct, mulVec, dotProduct_single]
    ring
  have key : ∀ (a b : I) (α β : ℂ), (α * star β * P a b + α * β * Q a b
      + star α * star β * R a b + star α * β * S a b).im = 0 := by
    intro a b α β
    have := h (Pi.single a α) (Pi.single b β)
    rw [hs, hs, he, he, he, he] at this
    exact this
  have h4 : ∀ a b, (P a b).re = (S a b).re ∧ (P a b).im = -(S a b).im ∧
      (Q a b).re = (R a b).re ∧ (Q a b).im = -(R a b).im := by
    intro a b
    have h1 := key a b 1 1
    have h2 := key a b Complex.I 1
    have h3 := key a b 1 Complex.I
    have h4 := key a b Complex.I Complex.I
    simp [Complex.mul_im, Complex.add_im] at h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  constructor
  · ext a b
    apply Complex.ext
    · simpa using (h4 a b).1
    · simpa using (h4 a b).2.1
  · ext a b
    apply Complex.ext
    · simpa using (h4 a b).2.2.1
    · simpa using (h4 a b).2.2.2

theorem exists_linear_antilinear (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) :
    ∃ M D : Matrix I I ℂ, ∀ z, L z = M *ᵥ z + D *ᵥ star z := by
  refine ⟨Matrix.of fun i j => (L (Pi.single j 1) i - Complex.I * L (Pi.single j Complex.I) i) / 2,
    Matrix.of fun i j => (L (Pi.single j 1) i + Complex.I * L (Pi.single j Complex.I) i) / 2, ?_⟩
  intro z
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : I → ℂ) + (z j).im • (Pi.single j Complex.I : I → ℂ)) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hL : L z = ∑ j, ((z j).re • L (Pi.single j 1) + (z j).im • L (Pi.single j Complex.I)) := by
    conv_lhs => rw [hz]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_add (f := _), map_smul]
  rw [hL]
  ext i
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, mulVec, dotProduct, Matrix.of_apply,
    Pi.star_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have aux : ∀ (a b : ℂ) (x y : ℝ), (x : ℂ) * a + y * b =
      (a - Complex.I * b) / 2 * (x + y * Complex.I) + (a + Complex.I * b) / 2 * (x - y * Complex.I) := by
    intro a b x y
    have hI := Complex.I_mul_I
    linear_combination ((y : ℂ) * b) * hI
  have hc : star (z j) = (z j).re - (z j).im * Complex.I := by
    apply Complex.ext <;> simp
  have hz' : z j = (z j).re + (z j).im * Complex.I := (Complex.re_add_im _).symm
  simp only [Complex.real_smul]
  rw [aux, hc, ← hz']

theorem star_mulVec_star (Z : Matrix I I ℂ) (w : I → ℂ) :
    star (Z *ᵥ star w) = Z.map star *ᵥ w := by
  ext i
  simp [mulVec, dotProduct]

theorem form_tz (G Z : Matrix I I ℂ) (z w : I → ℂ) :
    tz Z z ⬝ᵥ G *ᵥ star (tz Z w) = z ⬝ᵥ G *ᵥ star w + z ⬝ᵥ (-(G * Z.map star)) *ᵥ w
      + star z ⬝ᵥ (-(Zᵀ * G)) *ᵥ star w + star z ⬝ᵥ (Zᵀ * G * Z.map star) *ᵥ w := by
  have hv : ∀ (y v : I → ℂ), (Z *ᵥ y) ⬝ᵥ v = y ⬝ᵥ Zᵀ *ᵥ v := by
    intro y v
    rw [dotProduct_mulVec, vecMul_transpose]
  simp only [tz, star_sub, star_mulVec_star, mulVec_sub, sub_dotProduct, dotProduct_sub, hv,
    mulVec_mulVec, neg_mulVec, dotProduct_neg, Matrix.mul_assoc]
  ring

theorem form_pullback (H M : Matrix I I ℂ) (a b : I → ℂ) :
    (M *ᵥ a) ⬝ᵥ H *ᵥ star (M *ᵥ b) = a ⬝ᵥ (Mᵀ * H * M.map star) *ᵥ star b := by
  have h1 : star (M *ᵥ b) = M.map star *ᵥ star b := by
    have := star_mulVec_star M (star b)
    rwa [star_star] at this
  have hv : ∀ (y v : I → ℂ), (M *ᵥ y) ⬝ᵥ v = y ⬝ᵥ Mᵀ *ᵥ v := by
    intro y v
    rw [dotProduct_mulVec, vecMul_transpose]
  rw [h1, hv, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem posDef_of_form (G : Matrix I I ℂ) (hG : G.IsHermitian)
    (hp : ∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ G *ᵥ star z).re) : G.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hG fun x hx => ?_
  have h := hp (star x) (by simpa using hx)
  rw [star_star] at h
  rw [Complex.lt_def]
  exact ⟨by simpa using h, by simpa using (hG.im_star_dotProduct_mulVec_self x).symm⟩

theorem symm_posDef_of_relations (G Z : Matrix I I ℂ) (hG : G.PosDef)
    (e1 : G - 1 = (Zᵀ * G * Z.map star).map star)
    (e2 : -(G * Z.map star) = (-(Zᵀ * G)).map star) :
    Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef := by
  set Zc := Z.map star with hZc
  set Gc := G.map star with hGc
  have hcc : Zc.map star = Z := by ext; simp [hZc]
  have hgc : Gc.map star = G := by ext; simp [hGc]
  have hct : Zᴴ = Zcᵀ := by ext; simp [hZc, conjTranspose_apply]
  have mapmul : ∀ A B : Matrix I I ℂ, (A * B).map star = A.map star * B.map star := by
    intro A B; ext i j; simp [Matrix.mul_apply]
  have mapone : (1 : Matrix I I ℂ).map star = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have mapsub : ∀ A B : Matrix I I ℂ, (A - B).map star = A.map star - B.map star := by
    intro A B; ext i j; simp
  have mapneg : ∀ A : Matrix I I ℂ, (-A).map star = -A.map star := by
    intro A; ext i j; simp
  have maptr : Zᵀ.map star = Zᴴ := by ext; simp [conjTranspose_apply]

  have r1 : G - 1 = Zᴴ * Gc * Z := by rw [e1, mapmul, mapmul, maptr, hcc]
  have r2 : G * Zc = Zᴴ * Gc := by
    have := e2
    rw [mapneg, mapmul, maptr] at this
    exact neg_injective this
  have hU : G * (1 - Zc * Z) = 1 := by
    have : G - 1 = G * Zc * Z := by rw [r1, r2]
    rw [mul_sub, mul_one, ← mul_assoc, ← this]
    abel
  have hV : Gc * (1 - Z * Zc) = 1 := by
    have := congrArg (Matrix.map · star) hU
    simp only [mapmul, mapsub, mapone, hcc] at this
    exact this
  have hU' : (1 - Zc * Z) * G = 1 := mul_eq_one_comm.mp hU
  have hV' : (1 - Z * Zc) * Gc = 1 := mul_eq_one_comm.mp hV
  have hcomm : (1 - Zc * Z) * Zc = Zc * (1 - Z * Zc) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
  have h3 : G * Zc = Zc * Gc := by
    calc G * Zc = G * Zc * ((1 - Z * Zc) * Gc) := by rw [hV', mul_one]
      _ = G * (Zc * (1 - Z * Zc)) * Gc := by simp only [mul_assoc]
      _ = G * ((1 - Zc * Z) * Zc) * Gc := by rw [hcomm]
      _ = (G * (1 - Zc * Z)) * Zc * Gc := by simp only [mul_assoc]
      _ = Zc * Gc := by rw [hU, one_mul]
  have h4 : Zc = Zᴴ := by
    have : Zc * Gc = Zᴴ * Gc := by rw [← h3, r2]
    calc Zc = Zc * (Gc * (1 - Z * Zc)) := by rw [hV, mul_one]
      _ = (Zc * Gc) * (1 - Z * Zc) := by rw [mul_assoc]
      _ = (Zᴴ * Gc) * (1 - Z * Zc) := by rw [this]
      _ = Zᴴ * (Gc * (1 - Z * Zc)) := by rw [mul_assoc]
      _ = Zᴴ := by rw [hV, mul_one]
  refine ⟨?_, ?_⟩
  · have := congrArg (Matrix.map · star) h4
    simp only [hcc] at this
    ext i j
    have h := congrFun (congrFun this j) i
    simpa [conjTranspose_apply] using h
  · rw [← h4]
    have hinv : (1 - Zc * Z) = G⁻¹ := (Matrix.inv_eq_right_inv hU).symm
    rw [hinv]
    exact hG.inv

theorem linear_part_injective (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H M D : Matrix I I ℂ)
    (hpos : ∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re)
    (hform : ∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im)
    (hL : ∀ z, L z = M *ᵥ z + D *ᵥ star z) : Function.Injective M.mulVec := by
  have hker : ∀ x : I → ℂ, M *ᵥ x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have h1 : L x = D *ᵥ star x := by rw [hL, hx, zero_add]
    have hsI : ∀ y : I → ℂ, star (Complex.I • y) = (-Complex.I) • star y := by
      intro y; ext i; simp
    have h2 : L (Complex.I • x) = (-Complex.I) • L x := by
      rw [hL, hsI, mulVec_smul, mulVec_smul, hx, smul_zero, zero_add, h1]
    have hsI' : star ((-Complex.I) • L x) = Complex.I • star (L x) := by
      ext i; simp
    have h3 := hform x (Complex.I • x)
    rw [h2, hsI', hsI, mulVec_smul, dotProduct_smul, dotProduct_smul] at h3
    have h4 : 0 ≤ (L x ⬝ᵥ H *ᵥ star (L x)).re := by
      by_cases h0 : L x = 0
      · simp [h0]
      · exact (hpos _ h0).le
    have h5 : 0 < x ⬝ᵥ star x := by
      rw [dotProduct_comm]; exact dotProduct_star_self_pos_iff.mpr hne
    rw [Complex.lt_def] at h5
    simp at h3 h5
    linarith [h5.1]
  intro x y hxy
  have : M *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hker _ this)

theorem exists_linearEquiv_tz {I : Type} [Fintype I] [DecidableEq I]
    (L : (I → ℂ) →ₗ[ℝ] (I → ℂ)) (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (hpos : ∀ z : I → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H *ᵥ star z).re)
    (hform : ∀ z w : I → ℂ, (L z ⬝ᵥ H *ᵥ star (L w)).im = (z ⬝ᵥ star w).im) :
    ∃ (A : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (Z : Matrix I I ℂ), Zᵀ = Z ∧ (1 - Zᴴ * Z).PosDef ∧
      ∀ z, L z = A (tz Z z) := by
  obtain ⟨M, D, hL⟩ := exists_linear_antilinear L
  have hinj := linear_part_injective L H M D hpos hform hL
  have hU : IsUnit M := mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hU
  set Z : Matrix I I ℂ := -(M⁻¹ * D) with hZ
  have hLZ : ∀ z, L z = M *ᵥ tz Z z := by
    intro z
    rw [hL, tz, mulVec_sub, mulVec_mulVec, hZ, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv M hdet, Matrix.one_mul, neg_mulVec, sub_neg_eq_add]
  set G : Matrix I I ℂ := Mᵀ * H * M.map star with hGdef
  have hGh : G.IsHermitian := by
    have hM : (M.map star)ᴴ = Mᵀ := by ext; simp [conjTranspose_apply]
    have hM' : (Mᵀ)ᴴ = M.map star := by ext; simp [conjTranspose_apply]
    rw [IsHermitian, hGdef, conjTranspose_mul, conjTranspose_mul, hM, hM', hH.eq, Matrix.mul_assoc]
  have hGpd : G.PosDef := by
    refine posDef_of_form G hGh fun z hz => ?_
    rw [hGdef, ← form_pullback]
    refine hpos _ fun h0 => hz (hinj ?_)
    rw [h0, mulVec_zero]
  have hrel : ∀ z w : I → ℂ, (z ⬝ᵥ (G - 1) *ᵥ star w + z ⬝ᵥ (-(G * Z.map star)) *ᵥ w
      + star z ⬝ᵥ (-(Zᵀ * G)) *ᵥ star w + star z ⬝ᵥ (Zᵀ * G * Z.map star) *ᵥ w).im = 0 := by
    intro z w
    have h := hform z w
    rw [hLZ, hLZ, form_pullback, form_tz] at h
    rw [sub_mulVec, one_mulVec, dotProduct_sub]
    simp only [Complex.add_im, Complex.sub_im] at h ⊢
    linarith
  obtain ⟨e1, e2⟩ := im_terms_separate _ _ _ _ hrel
  obtain ⟨hs, hp⟩ := symm_posDef_of_relations G Z hGpd e1 e2
  refine ⟨LinearEquiv.ofInjectiveEndo (Matrix.toLin' M) ?_, Z, hs, hp, fun z => ?_⟩
  · intro a b h
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
    exact hinj h
  · rw [hLZ]
    exact (Matrix.toLin'_apply M (tz Z z)).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.PeriodCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginary
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem star_dotProduct_mulVec_eq {I : Type} [Fintype I] (M : Matrix I I ℂ) (a b : I → ℂ) :
    star (a ⬝ᵥ M *ᵥ b) = star a ⬝ᵥ (Mᴴ)ᵀ *ᵥ star b := by
  simp only [dotProduct, mulVec, Finset.sum_apply, star_sum, star_mul', Pi.star_apply, transpose_apply,
    conjTranspose_apply, Finset.mul_sum, RCLike.star_def]

theorem im_tz_form {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ) (hZ : Zᵀ = Z)
    (hP : (1 - Zᴴ * Z).PosDef) (z w : I → ℂ) :
    (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im := by
  obtain ⟨B, hBdef⟩ : ∃ B, B = Zᴴ := ⟨_, rfl⟩
  rw [← hBdef] at hP ⊢
  have hBt : Bᵀ = B := by
    rw [hBdef]; ext i j
    simp only [transpose_apply, conjTranspose_apply]
    rw [← transpose_apply Z i j, hZ]
  have hBh : Bᴴ = Z := by rw [hBdef, conjTranspose_conjTranspose]
  have hdet : IsUnit (1 - B * Z).det := (Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit
  obtain ⟨H, hHdef⟩ : ∃ H, H = (1 - B * Z)⁻¹ := ⟨_, rfl⟩
  rw [← hHdef]
  have h1 : H * (1 - B * Z) = 1 := by rw [hHdef]; exact Matrix.nonsing_inv_mul _ hdet
  have h2 : (1 - B * Z) * H = 1 := by rw [hHdef]; exact Matrix.mul_nonsing_inv _ hdet
  have hHh : Hᴴ = H := by rw [hHdef]; exact hP.inv.isHermitian.eq
  have hT : (1 - B * Z)ᵀ = 1 - Z * B := by
    rw [transpose_sub, transpose_one, transpose_mul, hZ, hBt]
  have h3 : Hᵀ * (1 - Z * B) = 1 := by
    have := congrArg transpose h2
    rwa [transpose_mul, hT, transpose_one] at this
  have h4 : (1 - Z * B) * Hᵀ = 1 := by
    have := congrArg transpose h1
    rwa [transpose_mul, hT, transpose_one] at this
  have c1 : B * (1 - Z * B) = (1 - B * Z) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have c2 : Z * (1 - B * Z) = (1 - Z * B) * Z := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have K : H * B = B * Hᵀ := by
    calc H * B = H * B * ((1 - Z * B) * Hᵀ) := by rw [h4, Matrix.mul_one]
      _ = H * (B * (1 - Z * B)) * Hᵀ := by simp only [Matrix.mul_assoc]
      _ = H * (1 - B * Z) * (B * Hᵀ) := by rw [c1]; simp only [Matrix.mul_assoc]
      _ = B * Hᵀ := by rw [h1, Matrix.one_mul]
  have K2 : Z * H = Hᵀ * Z := by
    calc Z * H = Hᵀ * (1 - Z * B) * (Z * H) := by rw [h3, Matrix.one_mul]
      _ = Hᵀ * ((1 - Z * B) * Z) * H := by simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z * ((1 - B * Z) * H) := by rw [← c2]; simp only [Matrix.mul_assoc]
      _ = Hᵀ * Z := by rw [h2, Matrix.mul_one]
  have hHB : H = 1 + H * B * Z := by
    have : H * (1 - B * Z) = H - H * B * Z := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    rw [this] at h1
    rw [← h1]; abel
  have hs : star (tz Z w) = star w - B *ᵥ w := by
    unfold tz
    rw [star_sub, star_mulVec, star_star, ← hBdef, ← mulVec_transpose, hBt]
  have dz : ∀ y : I → ℂ, (Z *ᵥ star z) ⬝ᵥ y = star z ⬝ᵥ Z *ᵥ y := by
    intro y
    rw [dotProduct_mulVec (star z), ← mulVec_transpose, hZ]
  have e1 : z ⬝ᵥ H *ᵥ star w = z ⬝ᵥ star w + z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    conv_lhs => rw [hHB]
    rw [add_mulVec, one_mulVec, dotProduct_add]
  have e2 : z ⬝ᵥ H *ᵥ B *ᵥ w = z ⬝ᵥ (H * B) *ᵥ w := by rw [mulVec_mulVec]
  have e3 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ star w = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [dz, mulVec_mulVec]
  have e4 : (Z *ᵥ star z) ⬝ᵥ H *ᵥ B *ᵥ w = star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [dz, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have s3 : star (z ⬝ᵥ (H * B) *ᵥ w) = star z ⬝ᵥ (Z * H) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, conjTranspose_mul, hBh, hHh, transpose_mul, hZ, ← K2]
  have s4 : star (star z ⬝ᵥ (Z * H * B) *ᵥ w) = z ⬝ᵥ (H * B * Z) *ᵥ star w := by
    rw [star_dotProduct_mulVec_eq, star_star, conjTranspose_mul, conjTranspose_mul, hBh, hHh, ← hBdef,
      transpose_mul, transpose_mul, hZ, hBt, ← K]
  have main : tz Z z ⬝ᵥ H *ᵥ star (tz Z w) = z ⬝ᵥ star w + star (star z ⬝ᵥ (Z * H * B) *ᵥ w)
      - z ⬝ᵥ (H * B) *ᵥ w - star (z ⬝ᵥ (H * B) *ᵥ w) + star z ⬝ᵥ (Z * H * B) *ᵥ w := by
    rw [hs, s3, s4]
    unfold tz
    rw [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, e1, e2, e3, e4]
    ring
  rw [main]
  simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im]
  ring

theorem im_tz_form' : ∀ {I : Type} [Fintype I] [DecidableEq I] (Z : Matrix I I ℂ), Zᵀ = Z → (1 - Zᴴ * Z).PosDef → ∀ z w : I → ℂ, (tz Z z ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z w)).im = (z ⬝ᵥ star w).im :=
  fun Z hZ hP z w => im_tz_form Z hZ hP z w

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspace
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames

variable {E : Type} [Field E] [NumberField E] {Ψ : Type} {j j' g : ℕ}

theorem span_single_eq_eigSp {ι : Type} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k)
    (s : 𝓞 E →+* ℂ) (f : ι → Fin g) (h1 : ∀ i, emb σ (e.symm (f i)) = s)
    (h2 : ∀ k, emb σ (e.symm k) = s → ∃ i, f i = k) :
    Submodule.span ℂ (Set.range fun i : ι => (Pi.single (f i) 1 : Fin g → ℂ)) = eigSp B s := by
  have hmem : ∀ x : Fin g → ℂ, x ∈ eigSp B s ↔ ∀ a, B a x = s a • x := by
    intro x
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine (hmem _).2 fun a => ?_
    funext k
    rw [hB]
    by_cases hk : k = f i
    · subst hk
      simp [h1 i]
    · simp [Pi.single_eq_of_ne hk]
  · intro x hx
    have hx' := (hmem x).1 hx
    have hsum : x = ∑ k, x k • (Pi.single k 1 : Fin g → ℂ) := by
      funext m
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : x k = 0
    · simp [hk]
    · have hs : emb σ (e.symm k) = s := by
        ext a
        have h := congrFun (hx' a) k
        rw [hB, Pi.smul_apply, smul_eq_mul] at h
        exact mul_right_cancel₀ hk h
      obtain ⟨i, rfl⟩ := h2 k hs
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


omit [NumberField E] in
theorem conj_ne (σ : Ψ → (𝓞 E →+* ℂ)) (h : IsCMFam σ) (τ τ' : Ψ) : σ τ' ≠ (starRingEnd ℂ).comp (σ τ) :=
  fun hc => ((h.2 (σ τ)).1 ⟨τ, rfl⟩) ⟨τ', hc⟩


omit [NumberField E] in
theorem conj_comp_inj {s t : 𝓞 E →+* ℂ} (h : (starRingEnd ℂ).comp s = (starRingEnd ℂ).comp t) : s = t := by
  ext a
  have := congrArg (starRingEnd ℂ) (RingHom.congr_fun h a)
  simpa using this


omit [NumberField E] in
theorem conj_conj_comp (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem span_single_eigenspace [IsCMField E] [Fintype Ψ] (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (hcm : IsCMFam σ) (hB : ∀ a x k, B a x k = emb σ (e.symm k) a * x k) (τ : Ψ) :
    Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧
      Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) =
        eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  constructor
  · refine span_single_eq_eigSp σ e B hB (σ τ) (fun i : Fin j' => e (Sum.inl i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · have h : σ τ' = σ τ := hk
        obtain rfl := hcm.1 h
        exact ⟨b, rfl⟩
      · have h : (starRingEnd ℂ).comp (σ τ') = σ τ := hk
        refine absurd ?_ (conj_ne σ hcm τ τ')
        rw [← h, conj_conj_comp]
  · refine span_single_eq_eigSp σ e B hB _ (fun i : Fin j => e (Sum.inr i, τ)) (fun i => ?_) fun k hk => ?_
    · simp [emb]
    · obtain ⟨⟨u, τ'⟩, rfl⟩ := e.surjective k
      rw [Equiv.symm_apply_apply] at hk
      rcases u with b | b
      · exact absurd (show σ τ' = (starRingEnd ℂ).comp (σ τ) from hk) (conj_ne σ hcm τ τ')
      · have h : (starRingEnd ℂ).comp (σ τ') = (starRingEnd ℂ).comp (σ τ) := hk
        obtain rfl := hcm.1 (conj_comp_inj h)
        exact ⟨b, rfl⟩

theorem span_single_eigSp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) :=
  fun σ e B h hB τ => span_single_eigenspace σ e B h hB τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames
end

