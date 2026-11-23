module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductFirstCohomologyComparison
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0145
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.OmDec

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_sub_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g)
    (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f - h) g v = fderiv ℝ f g v - fderiv ℝ h g v := by
  rw [fderiv_sub hf hh]; rfl

theorem fderiv_zero_apply' (g v : E) : fderiv ℝ (0 : E → F) g v = 0 := by
  have h : fderiv ℝ (0 : E → F) g = 0 := by
    simpa using (fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : F))
  rw [h]; rfl

end General

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_left (A B : Mat n) (h : Mat n → V) : Rd (A - B) h = Rd A h - Rd B h := by
  funext g; simp [Rd, mul_sub]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  exact fderiv_zero_apply' _ _

theorem Rd_add_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a + b) g = Rd X a g + Rd X b g :=
  RCalc.fderiv_add_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_sub_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a - b) g = Rd X a g - Rd X b g :=
  fderiv_sub_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_smul_right (c : ℂ) (X : Mat n) {a : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (c • a) g = c • Rd X a g :=
  RCalc.fderiv_csmul_apply (RCalc.differentiableAt_of_smooth ha hg) c _

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  show ∑ d, Eu s c d (Epow s 0 d a f) = _
  rw [Finset.sum_eq_single a]
  · simp [Epow]
  · intro d _ hd
    simp [Epow, hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) :
    gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  show ∑ c, Eu s a c (Epow s 1 c a f) = _
  simp only [Epow_one]

theorem Eu_Eu_apply (s : Bool) (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) (ε : ℂ)
    (hε : ε = if s then -Complex.I else Complex.I) :
    Eu s a b (Eu s c d f) g = (1 / 4 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        + ε • Rd (Matrix.single a b 1) (Rd (Matrix.single c d Complex.I) f) g
        + ε • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d 1) f) g
        + (ε * ε) • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  have hX := RCalc.Rd_contDiffOn (Matrix.single c d (1 : ℂ)) hf
  have hY := RCalc.Rd_contDiffOn (Matrix.single c d Complex.I) hf
  have hS : ContDiffOn ℝ ∞ (ε • Rd (Matrix.single c d Complex.I) f) (GLs n) := hY.const_smul ε
  have key : ∀ Z : Mat n, Rd Z (Eu s c d f) g =
      (1 / 2 : ℂ) • (Rd Z (Rd (Matrix.single c d 1) f) g
        + ε • Rd Z (Rd (Matrix.single c d Complex.I) f) g) := by
    intro Z
    have e : Eu s c d f = (1 / 2 : ℂ) • (Rd (Matrix.single c d 1) f
        + ε • Rd (Matrix.single c d Complex.I) f) := by
      rw [hε]; rfl
    have hA : ContDiffOn ℝ ∞ (Rd (Matrix.single c d 1) f + ε • Rd (Matrix.single c d Complex.I) f)
        (GLs n) := hX.add hS
    rw [e, Rd_smul_right _ _ hA hg, Rd_add_right _ hX hS hg, Rd_smul_right _ _ hY hg]
  have e2 : Eu s a b (Eu s c d f) g = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) (Eu s c d f) g
      + ε • Rd (Matrix.single a b Complex.I) (Eu s c d f) g) := by
    rw [hε]; rfl
  rw [e2, key, key]
  module

theorem Eu_pair_apply (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Eu true a b (Eu true c d f) g + Eu false a b (Eu false c d f) g = (1 / 2 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  rw [Eu_Eu_apply true a b c d hf hg (-Complex.I) (by simp),
    Eu_Eu_apply false a b c d hf hg Complex.I (by simp)]
  have h1 : (-Complex.I) * (-Complex.I) = -1 := by simp
  have h2 : Complex.I * Complex.I = -1 := by simp
  rw [h1, h2]
  module

theorem Om_apply {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om f g = ∑ a, ∑ b, (Rd (Matrix.single a b 1) (Rd (Matrix.single b a 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single b a Complex.I) f) g) := by
  have h : Om f g = (2 : ℂ) • ∑ a, ∑ b,
      (Eu true a b (Eu true b a f) g + Eu false a b (Eu false b a f) g) := by
    simp only [Om, gel_two, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib]
  rw [h]
  simp only [Eu_pair_apply _ _ _ _ hf hg, Finset.smul_sum, smul_smul]
  norm_num

theorem Rd_sq_add (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A + B) (Rd (A + B) f) g =
      Rd A (Rd A f) g + Rd A (Rd B f) g + Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [RCalc.Rd_add_left A B f, RCalc.Rd_add_left A B (Rd A f + Rd B f)]
  simp only [Pi.add_apply]
  rw [Rd_add_right _ dA dB hg, Rd_add_right _ dA dB hg]
  abel

theorem Rd_sq_sub (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A - B) (Rd (A - B) f) g =
      Rd A (Rd A f) g - Rd A (Rd B f) g - Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [Rd_sub_left A B f, Rd_sub_left A B (Rd A f - Rd B f)]
  simp only [Pi.sub_apply]
  rw [Rd_sub_right _ dA dB hg, Rd_sub_right _ dA dB hg]
  abel

theorem sum_Ix (F : Ix n → V) :
    ∑ p, F p = ∑ a, ∑ b, (F (true, a, b) + F (false, a, b)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]

theorem sum_reindex (x y : Fin n → Fin n → V) :
    ∑ a, ∑ b, (x a b - y a b) = (1 / 4 : ℂ) • ∑ a, ∑ b,
      ((2 : ℂ) • (x a b + x b a) - (2 : ℂ) • (y a b + y b a)) := by
  have hx : ∑ a, ∑ b, x b a = ∑ a, ∑ b, x a b := Finset.sum_comm
  have hy : ∑ a, ∑ b, y b a = ∑ a, ∑ b, y a b := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hx, hy]
  module

theorem Om_eq_squares {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) :
    ContDiffOn ℝ ∞ f (GLs n) → ∀ g ∈ GLs n,
      Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g
        - (1 / 4 : ℂ) • ∑ p : Ix n, Rd (sk p) (Rd (sk p) f) g := by
  intro hf g hg
  rw [Om_apply hf hg, sum_reindex, sum_Ix, sum_Ix, ← smul_sub]
  congr 1
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e1 : hm (n := n) (true, a, b) = Matrix.single a b 1 + Matrix.single b a 1 := by simp [hm]
  have e2 : hm (n := n) (false, a, b) =
      Matrix.single a b Complex.I - Matrix.single b a Complex.I := by simp [hm]
  have e3 : sk (n := n) (true, a, b) = Matrix.single a b 1 - Matrix.single b a 1 := by simp [sk]
  have e4 : sk (n := n) (false, a, b) =
      Matrix.single a b Complex.I + Matrix.single b a Complex.I := by simp [sk]
  rw [e1, e2, e3, e4, Rd_sq_add _ _ hf hg, Rd_sq_sub _ _ hf hg, Rd_sq_add _ _ hf hg,
    Rd_sq_sub _ _ hf hg]
  module

end GlobalTheory.CompanionTheory.WaveSpd.OmDec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyOfBaseZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

section Kunneth

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem mp_box_left {T T' : C} (ψ : T ⟶ T') (b : C) (u : F.obj T ⊗[R] F.obj b) :
    mp (box F) (show ((T, b) : C × C) ⟶ (T', b) from (ψ, 𝟙 b)) u = (mp F ψ).toLinearMap.rTensor _ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change mp F ψ x ⊗ₜ[R] mp F (𝟙 b) y = mp F ψ x ⊗ₜ[R] y
    rw [mp_id]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem mp_box_right (a : C) {T T' : C} (ψ : T ⟶ T') (u : F.obj a ⊗[R] F.obj T) :
    mp (box F) (show ((a, T) : C × C) ⟶ (a, T') from (𝟙 a, ψ)) u = (mp F ψ).toLinearMap.lTensor _ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change mp F (𝟙 a) x ⊗ₜ[R] mp F ψ y = x ⊗ₜ[R] mp F ψ y
    rw [mp_id]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

variable {F}

theorem box_square (f : Z1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    (mp F ψ).toLinearMap.lTensor _ (f.1 (a, b) (a', b) (φ, 𝟙 b)) + f.1 (a', b) (a', b') (𝟙 a', ψ) =
      (mp F φ).toLinearMap.rTensor _ (f.1 (a, b) (a, b') (𝟙 a, ψ)) + f.1 (a, b') (a', b') (φ, 𝟙 b') := by
  have e1 := Z1.comp f (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (show ((a', b) : C × C) ⟶ (a', b') from (𝟙 a', ψ))
  have e2 := Z1.comp f (show ((a, b) : C × C) ⟶ (a, b') from (𝟙 a, ψ)) (show ((a, b') : C × C) ⟶ (a', b') from (φ, 𝟙 b'))
  rw [mp_box_right] at e1
  rw [mp_box_left] at e2
  rw [← e1, ← e2]
  congr 1
  simp

end Kunneth

theorem kunneth (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C]
    (F : C ⥤ CommAlgCat.{0} R) (hf : ∀ T, Module.Flat R (F.obj T)) (hU : USt F) (c : H1 (box F)) :
    ∃ x y : H1 F, c = (boxL F).pull1 x + (boxR F).pull1 y := by
  classical
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hz : ∀ b : C, ∃ t : Z1 F ⊗[R] F.obj b, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor _ t = f.1 (T, b) (T', b) (φ, 𝟙 b) := fun b ↦ by
    haveI := hf b
    let f₀ : ∀ (T T' : C) (_ : T ⟶ T'), F.obj T' ⊗[R] F.obj b := fun T T' φ ↦ f.1 (T, b) (T', b) (φ, 𝟙 b)
    refine GlobalTheory.T.flat_cocycle_tensor_representation R C F (F.obj b) f₀ ?_
    intro T T' T'' φ ψ
    have e := Z1.comp f (show ((T, b) : C × C) ⟶ (T', b) from (φ, 𝟙 b)) (show ((T', b) : C × C) ⟶ (T'', b) from (ψ, 𝟙 b))
    rw [mp_box_left] at e
    rw [← e]
    congr 1
    simp
    rfl
  choose t ht using hz
  have hcomp : ∀ (b b' : C) (ψ : b ⟶ b'), (H1.mk F).rTensor _ (t b') =
      (mp F ψ).toLinearMap.lTensor (H1 F) ((H1.mk F).rTensor _ (t b)) := fun b b' ψ ↦ by
    haveI := hf b'
    have k := GlobalTheory.T.cocycle_tensor_coboundary_class_zero R C F (F.obj b') (t b' - (mp F ψ).toLinearMap.lTensor (Z1 F) (t b))
      (fun a ↦ f.1 (a, b) (a, b') (𝟙 a, ψ)) (fun T T' φ ↦ by
        have e : (evZ F φ).rTensor _ ((mp F ψ).toLinearMap.lTensor (Z1 F) (t b)) =
            (mp F ψ).toLinearMap.lTensor _ ((evZ F φ).rTensor _ (t b)) := by
          rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
            LinearMap.lTensor_comp_rTensor]
        have s := box_square f φ ψ
        rw [map_sub, e, ht, ht]
        exact sub_eq_sub_iff_add_eq_add.2 (by rw [add_comm, ← s, add_comm]))
    have e : (H1.mk F).rTensor _ ((mp F ψ).toLinearMap.lTensor (Z1 F) (t b)) =
        (mp F ψ).toLinearMap.lTensor _ ((H1.mk F).rTensor _ (t b)) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [map_sub, e, sub_eq_zero] at k
    exact k
  obtain ⟨x, hx, -⟩ := hU (H1 F) (fun b ↦ (H1.mk F).rTensor _ (t b)) hcomp
  obtain ⟨z, rfl⟩ := H1.mk_surjective F x
  have hg : ∀ b : C, ∃ g : ∀ T : C, F.obj T ⊗[R] F.obj b, ∀ (T T' : C) (φ : T ⟶ T'),
      (evZ F φ).rTensor _ (z ⊗ₜ[R] (1 : F.obj b) - t b) = g T' - (mp F φ).toLinearMap.rTensor _ (g T) := fun b ↦
    _root_.GlobalTheory.CompanionTheory.Axis.rTensor_cocycle_eq_coboundary_of_class_eq_zero R C F (F.obj b) _ (by
      rw [map_sub, LinearMap.rTensor_tmul, hx b, sub_self])
  choose g hg using hg
  let G : C0 (box F) := fun T ↦ g T.2 T.1
  let f' : Z1 (box F) := f - (boxL F).pullbackOneCocycle z + (d0 (box F)).codRestrict (Z1 (box F)) (commAlgFunctorCoboundaryZero_mem_cocyclesOne _) G
  have hv : ∀ (a a' b : C) (φ : a ⟶ a'), f'.1 (a, b) (a', b) (φ, 𝟙 b) = 0 := fun a a' b φ ↦ by
    have e := hg b a a' φ
    rw [map_sub, LinearMap.rTensor_tmul, ht] at e
    have e2 : mp (box F) (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (G (a, b)) =
        (mp F φ).toLinearMap.rTensor _ (g b a) := mp_box_left F φ b _
    have e3 : f'.1 (a, b) (a', b) (φ, 𝟙 b) = f.1 (a, b) (a', b) (φ, 𝟙 b) - (z.1 a a' φ) ⊗ₜ[R] (1 : F.obj b) +
        (g b a' - mp (box F) (show ((a, b) : C × C) ⟶ (a', b) from (φ, 𝟙 b)) (G (a, b))) := rfl
    rw [e3, e2, ← e]
    change _ - z.1 a a' φ ⊗ₜ[R] (1 : F.obj b) + (z.1 a a' φ ⊗ₜ[R] (1 : F.obj b) - _) = 0
    abel
  obtain ⟨y, hy⟩ := GlobalTheory.T.cocycle_on_product_from_second_factor R C F hU f' hv
  refine ⟨H1.mk F z, H1.mk F y, ?_⟩
  rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, ← map_add (f := _), H1.mk_eq_mk]
  refine ⟨-G, ?_⟩
  rw [hy, map_neg]
  have : (f' : C1 (box F)) = f.1 - ((boxL F).pullbackOneCocycle z).1 + d0 (box F) G := rfl
  change -d0 (box F) G = f.1 - (((boxL F).pullbackOneCocycle z).1 + f'.1)
  rw [this]
  abel

theorem first_cohomology_of_base_zero (R : Type) [CommRing R] (c : HO1 (𝟙_ (Over (Sp R))).hom) : c = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))
  exact H1.eq_zero_of_isInitial _ (T₀ := op ⟨⊤, isAffineOpen_top _⟩)
    (Limits.IsInitial.ofUniqueHom (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top _⟩ from
        le_top (a := U.unop.1))).op) fun _ _ ↦ rfl) c

theorem isPullO_id (R : Type) [CommRing R] (X : Over (Sp R)) (a : HO1 X.hom) : IsPullO (wOver (𝟙 X)) a a :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull (wOver (𝟙 X))) (pairRes _ X.hom) (pairIdTrans X.left) (fun _ _ ↦ rfl) a

theorem ust_abelian : DescentSt → LowSt → SysBCSt → SteinSt → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (P : Type) [SemilatticeInf P] (S : Sys A.left P), USt (OSys A.hom S) := by
  intro hD hL hB hS R _ A _ g hA hg P _ S M _ _ z hz
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingEquiv.toOpposite R).symm.toRingHom)
  haveI : IsCentralScalar R M := ⟨fun r m ↦ rfl⟩
  obtain ⟨A', _, φ, hA', hg', hpb⟩ := _root_.GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom R (TrivSqZeroExt R M) A g hA hg
  have := hA.proper
  have := hA'.proper
  obtain ⟨S', m, -⟩ := hB R (TrivSqZeroExt R M) A.left A'.left A.hom A'.hom φ hpb inferInstance P S
  have hSt : Stein (OSys A'.hom S') :=
    ((hL _ _ _ _ _ (resSys A'.hom S') (hD _ _ A'.hom inferInstance P S')).2.2).1 (hS _ A' g hA' hg')
  exact GlobalTheory.T.exists_unique_constant_of_compatible_family R Pᵒᵖ (OSys A.hom S) M _ m hSt z hz

theorem isPullO_comp (R : Type) [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : HO1 Z.hom) (b : HO1 Y.hom) (c : HO1 X.hom) (h1 : IsPullO (wOver g) a b) (h2 : IsPullO (wOver f) b c) :
    IsPullO (wOver (f ≫ g)) a c :=
  _root_.GlobalTheory.CompanionTheory.Axis.PullO.isPullO_wOver_comp R X Y Z f g a b c h1 h2

theorem isPullO_add {R : Type} [CommRing R] {X Y : Over (Sp R)} (f : X ⟶ Y) {a a' : HO1 Y.hom} {b b' : HO1 X.hom}
    (h : IsPullO (wOver f) a b) (h' : IsPullO (wOver f) a' b') : IsPullO (wOver f) (a + a') (b + b') := by
  unfold IsPullO at *; rw [map_add (f := _), map_add (f := _), h, h']

theorem isPullO_unique {R : Type} [CommRing R] {X Y : Over (Sp R)} (f : X ⟶ Y) {a : HO1 Y.hom} {b b' : HO1 X.hom}
    (h : IsPullO (wOver f) a b) (h' : IsPullO (wOver f) a b') : b = b' :=
  (existsUnique_isPullO (wOver f) a).unique h h'

theorem isPullO_through_unit {R : Type} [CommRing R] {X Y : Over (Sp R)} (t : X ⟶ 𝟙_ (Over (Sp R)))
    (u : 𝟙_ (Over (Sp R)) ⟶ Y) (a : HO1 Y.hom) (b : HO1 X.hom) (h : IsPullO (wOver (t ≫ u)) a b) : b = 0 := by
  have h1 := isPullO_pullHO1 (wOver u) a
  rw [first_cohomology_of_base_zero R (pullHO1 (wOver u) a)] at h1
  have h2 := isPullO_comp R t u a 0 0 h1 ((map_zero _).trans (map_zero _).symm)
  exact isPullO_unique _ h h2

theorem axOSt : DescentSt → LowSt → SysBCSt → SteinSt → AxOSt := by
  intro hD hL hB hS R _ A _ g hA hg c h1 h2
  have hA2 := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have := hA.proper
  have := hA2.proper
  have := hA.smooth
  obtain ⟨P, _, _, ⟨S⟩⟩ := _root_.GlobalTheory.CompanionTheory.Axis.exists_finite_sys_of_separated_quasiCompact R A.left A.hom inferInstance inferInstance
  obtain ⟨Q, _, S', m, hm, hfst, hsnd⟩ := _root_.GlobalTheory.CompanionTheory.Axis.exists_boxSys R A P S
  have hU := ust_abelian hD hL hB hS R A g hA hg P S
  have hb := (hL _ _ _ _ _ (resSys A.hom S) (hD R _ A.hom inferInstance P S)).1
  have hb' := (hL _ _ _ _ _ (resSys (A ⊗ A).hom S') (hD R _ (A ⊗ A).hom inferInstance Q S')).1
  haveI : Finite Pᵒᵖ := Finite.of_injective Opposite.unop Opposite.unop_injective
  obtain ⟨w, hw⟩ := hm ((resSys (A ⊗ A).hom S').pull1 c)
  obtain ⟨x, y, rfl⟩ := kunneth R Pᵒᵖ (OSys A.hom S) (fun T ↦ _root_.GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth R _ A.hom inferInstance _) hU w
  obtain ⟨x₀, rfl⟩ := hb.2 x
  obtain ⟨y₀, rfl⟩ := hb.2 y
  have e1 := isPullO_pullHO1 (wOver (fst A A)) x₀
  have e2 := isPullO_pullHO1 (wOver (snd A A)) y₀
  have hc : c = pullHO1 (wOver (fst A A)) x₀ + pullHO1 (wOver (snd A A)) y₀ := by
    apply hb'.1
    rw [map_add (f := _), hfst _ _ e1, hsnd _ _ e2, ← hw, map_add (f := _)]
  set c₁ := pullHO1 (wOver (fst A A)) x₀ with hc₁
  set c₂ := pullHO1 (wOver (snd A A)) y₀ with hc₂

  have a1 := isPullO_pullHO1 (wOver (lift (𝟙 A) (1 : A ⟶ A))) c₁
  have a2 := isPullO_pullHO1 (wOver (lift (𝟙 A) (1 : A ⟶ A))) c₂
  have b1 := isPullO_pullHO1 (wOver (lift (1 : A ⟶ A) (𝟙 A))) c₁
  have b2 := isPullO_pullHO1 (wOver (lift (1 : A ⟶ A) (𝟙 A))) c₂
  have k1 := isPullO_comp R _ _ _ _ _ e1 a1
  have k2 := isPullO_comp R _ _ _ _ _ e2 a2
  have l1 := isPullO_comp R _ _ _ _ _ e1 b1
  have l2 := isPullO_comp R _ _ _ _ _ e2 b2
  rw [lift_fst] at k1
  rw [lift_snd, Hom.one_def] at k2
  rw [lift_fst, Hom.one_def] at l1
  rw [lift_snd] at l2
  have z2 := isPullO_through_unit _ _ _ _ k2
  have z3 := isPullO_through_unit _ _ _ _ l1
  have u1 := isPullO_unique _ k1 (isPullO_id R A x₀)
  have u2 := isPullO_unique _ l2 (isPullO_id R A y₀)
  rw [hc] at h1 h2
  have v1 := isPullO_unique _ h1 (isPullO_add _ a1 a2)
  have v2 := isPullO_unique _ h2 (isPullO_add _ b1 b2)
  rw [z2, add_zero, u1] at v1
  rw [z3, zero_add, u2] at v2
  rw [hc, hc₁, hc₂, ← v1, ← v2, map_zero, map_zero, add_zero]

end GlobalTheory.CompanionTheory.Axis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralConvApplyEq
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_conv_apply_eq {Γ V : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : Measure Γ) [μ.IsHaarMeasure]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F F' : Γ → (V →L[ℂ] V)) (φ : Γ → V) (hF : Continuous F) (hF' : Continuous F') (hφ : Continuous φ)
    (cF : HasCompactSupport F) (cF' : HasCompactSupport F') :
    ∫ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) ∂μ = ∫ y, F y (∫ z, F' z (φ (y * z)) ∂μ) ∂μ := by
  have h1 : ∀ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) = ∫ y, F y (F' (y⁻¹ * z) (φ z)) ∂μ := by
    intro z
    have hc : Continuous fun y => F y * F' (y⁻¹ * z) :=
      hF.mul (hF'.comp ((continuous_inv).mul continuous_const))
    have hs : HasCompactSupport fun y => F y * F' (y⁻¹ * z) :=
      HasCompactSupport.intro cF fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy]
    have := ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport (μ := μ) hs) (φ z)
    simpa using this
  simp_rw [h1]
  have hcont : Continuous (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have a1 : Continuous fun p : Γ × Γ => F p.2 := hF.comp continuous_snd
    have a2 : Continuous fun p : Γ × Γ => F' (p.2⁻¹ * p.1) :=
      hF'.comp (continuous_snd.inv.mul continuous_fst)
    have a3 : Continuous fun p : Γ × Γ => φ p.1 := hφ.comp continuous_fst
    exact a1.clm_apply (a2.clm_apply a3)
  have hsupp : HasCompactSupport (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have hK : IsCompact ((fun p : Γ × Γ => (p.1 * p.2, p.1)) '' (tsupport F ×ˢ tsupport F')) :=
      (IsCompact.prod cF cF').image ((continuous_fst.mul continuous_snd).prodMk continuous_fst)
    refine HasCompactSupport.intro hK ?_
    rintro ⟨z, y⟩ hzy
    by_cases hy : y ∈ tsupport F
    · by_cases hy' : y⁻¹ * z ∈ tsupport F'
      · exact absurd ⟨(y, y⁻¹ * z), ⟨hy, hy'⟩, by simp⟩ hzy
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy']
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap_of_hasCompactSupport hcont hsupp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∫ z, F y (F' (y⁻¹ * z) (φ z)) ∂μ = F y (∫ z, F' z (φ (y * z)) ∂μ)
  rw [← integral_mul_left_eq_self (fun z => F y (F' (y⁻¹ * z) (φ z))) y]
  simp only [inv_mul_cancel_left]
  have hc : Continuous fun z => F' z (φ (y * z)) :=
    hF'.clm_apply (hφ.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport fun z => F' z (φ (y * z)) :=
    HasCompactSupport.intro cF' fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  exact (F y).integral_comp_comm (hc.integrable_of_hasCompactSupport (μ := μ) hs)

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem KReg.continuous_val {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V} (hk : KReg k) :
    Continuous fun y : G n => k y.val :=
  hk.1.comp_continuous Units.continuous_val val_mem_GLs

theorem KReg.hasCompactSupport_val (hL : LgFacts) {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V}
    (hk : KReg k) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := hk.2
  refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => ?_
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem act_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg k → KReg k' →
    ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E (conv μ E k k') f x = act μ E k (act μ E k' f) x := by
  intro hL n _ _ μ _ E k k' f hk hk' hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨X, rfl⟩ : ∃ X : G n, X.val = x :=
    (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  have hφ : Continuous fun z : G n => f (X.val * z.val) :=
    hf.comp_continuous (continuous_const.mul Units.continuous_val) fun z => val_mem_GLs (X * z)
  have key := integral_conv_apply_eq μ (fun y : G n => k y.val) (fun y : G n => k' y.val)
    (fun z : G n => f (X.val * z.val)) hk.continuous_val hk'.continuous_val hφ
    (hk.hasCompactSupport_val hL) (hk'.hasCompactSupport_val hL)
  simp only [Units.val_mul, ← mul_assoc] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult
end

