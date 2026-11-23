module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFramesOfHolPeriods
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HuaIntegralPositiveDefiniteQuadric
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HuaQuadric

variable {p q : ℕ}

theorem exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R.det ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, ?_, hR⟩
  have h := hA.det_pos.ne'
  rw [hR, det_mul] at h
  exact (right_ne_zero_of_mul h).isUnit

theorem shear_fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin q) ℂ) (c : Matrix (Fin q) (Fin p) ℂ)
    (d : Matrix (Fin q) (Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (fromBlocks a b c d) Z = fromBlocks a (a * Z + b) (Zᴴ * a + c) ((Zᴴ * a + c) * Z + (Zᴴ * b + d)) := by
  simp [shear, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem exists_square {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) :
    ∃ (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ),
      IsUnit R.det ∧ IsUnit T.det ∧ A.det = (Complex.normSq R.det * Complex.normSq T.det : ℝ) ∧
      ∀ Z, (shear A Z).toBlocks₂₂ = Tᴴ * (1 + (R * Z * T⁻¹ + C)ᴴ * (R * Z * T⁻¹ + C)) * T := by
  obtain ⟨R, hR, ha⟩ := exists_factor (posDef_blocks hA).1
  have e : A.toBlocks₂₁ = A.toBlocks₁₂ᴴ := by
    ext a b
    exact (hA.1.apply _ _).symm
  have hRh : IsUnit Rᴴ.det := by rw [det_conjTranspose]; exact hR.star
  obtain ⟨c, hc⟩ : ∃ c, A.toBlocks₁₂ = Rᴴ * R * c :=
    ⟨R⁻¹ * (Rᴴ⁻¹ * A.toBlocks₁₂), by
      rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hR, mul_nonsing_inv_cancel_left _ _ hRh]⟩
  have hA' : A = fromBlocks (Rᴴ * R) (Rᴴ * R * c) (cᴴ * (Rᴴ * R)) A.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks A, e, ha, hc]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  generalize A.toBlocks₂₂ = d at hA'
  have hs : shear A (-c) = fromBlocks (Rᴴ * R) 0 0 (d - cᴴ * (Rᴴ * R * c)) := by
    rw [hA', shear_fromBlocks]
    simp [sub_eq_neg_add]
  have hS := (posDef_blocks (posDef_shear hA (-c))).2.1
  rw [hs, toBlocks_fromBlocks₂₂] at hS
  obtain ⟨T, hT, ht⟩ := exists_factor hS
  have hTh : IsUnit Tᴴ.det := by rw [det_conjTranspose]; exact hT.star
  refine ⟨R, T, R * c * T⁻¹, hR, hT, ?_, fun Z => ?_⟩
  · rw [← det_shear A (-c), hs, ht, det_fromBlocks_zero₂₁, det_mul, det_mul, det_conjTranspose, det_conjTranspose]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    rfl
  · rw [hA', shear_fromBlocks, toBlocks_fromBlocks₂₂, eq_add_of_sub_eq ht]
    simp only [conjTranspose_mul, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      conjTranspose_nonsing_inv, mul_nonsing_inv_cancel_left _ _ hTh,
      nonsing_inv_mul _ hT, Matrix.mul_one, Matrix.one_mul]
    abel

theorem quadric : ∀ (p q : ℕ) (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (A.det.re ^ (-(q : ℤ)) / grassConst p q) := by
  intro p q A hA
  obtain ⟨R, T, C, hR, hT, hd, hZ⟩ := exists_square hA
  have hr : 0 < Complex.normSq R.det := Complex.normSq_pos.2 hR.ne_zero
  have ht : 0 < Complex.normSq T.det := Complex.normSq_pos.2 hT.ne_zero
  let f : (Fin p × Fin q → ℂ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal ((1 + (toMat v)ᴴ * toMat v).det.re ^ (-((p + q : ℕ) : ℤ)))
  have hf : Measurable f :=
    ((Complex.continuous_re.comp (continuous_const.add
      (continuous_toMat.matrix_conjTranspose.matrix_mul continuous_toMat)).matrix_det).measurable.pow_const
        _).ennreal_ofReal
  have h1 : ∀ v : Fin p × Fin q → ℂ,
      ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) =
        ENNReal.ofReal (Complex.normSq T.det ^ (-((p + q : ℕ) : ℤ))) * f (vecOf (R * toMat v * T⁻¹ + C)) := by
    intro v
    simp only [f, toMat_vecOf]
    rw [← ENNReal.ofReal_mul (zpow_pos ht _).le, ← mul_zpow, hZ, det_mul, det_mul, det_conjTranspose, mul_right_comm,
      ← Complex.re_ofReal_mul, Complex.normSq_eq_conj_mul_self]
    rfl
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    GlobalTheory.FlagFibre.lintegral_affine p q R T⁻¹ C hR (isUnit_nonsing_inv_det _ hT) f hf]
  have h2 : ∫⁻ v, f v = ENNReal.ofReal (grassConst p q)⁻¹ := GlobalTheory.HuaIntegral.dual_mass p q
  have h3 : Complex.normSq T⁻¹.det = (Complex.normSq T.det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]
  rw [h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (zpow_pos ht _).le, ← ENNReal.ofReal_mul (by positivity), hd,
    Complex.ofReal_re, div_eq_mul_inv]
  congr 2
  simp only [_root_.zpow_neg, _root_.zpow_natCast, pow_add, mul_pow, inv_pow]
  field_simp

end GlobalTheory.HuaQuadric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEigBasisPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsEigBasis {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ)
    {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (v i)) ∧ (∀ i (a : 𝓞 E), v i ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x v a w

variable {O : Type} [CommRing O] {β : O →+* c.F}

theorem EigFrame.isEigBasis {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (g : EigFrame Z φ x) (τ : E →+* ℂ) : IsEigBasis Z.t φ x τ (g.v τ) :=
  ⟨g.tan τ, g.eig τ, g.basis τ⟩

def eigFrameOf {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)) (h : ∀ τ, IsEigBasis Z.t φ x τ (v τ)) :
    EigFrame Z φ x :=
  ⟨v, fun τ => (h τ).1, fun τ => (h τ).2.1, fun τ => (h τ).2.2⟩

section Transport

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ S'} {τ : E →+* ℂ} {n : ℕ}

theorem isEigBasis_push {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (h : IsEigBasis t' φ x τ v) :
    IsEigBasis t φ (x ≫ f) τ (fun i => v i ≫ m.φ) := by
  have hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := fun i => (h.1 i).1
  refine ⟨fun i => (tan_iff m rfl (hv i)).2 (h.1 i), fun i a => (eig_iff m (hv i) a _).2 (h.2.1 i a),
    fun w hw he => ?_⟩
  obtain ⟨w', hw1, rfl⟩ := exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) w (by rw [hw.1, Category.assoc])
  have hb := h.2.2 w' ((tan_iff m rfl hw1).1 hw) fun a => (eig_iff m hw1 a _).1 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv cf hw1).2 hb

theorem isEigBasis_pull {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsEigBasis t φ (x ≫ f) τ v) :
    ∃ v' : Fin n → (Sp (DualNumber R) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = v i) ∧ IsEigBasis t' φ x τ v' := by
  choose v' hv1 hv2 using fun i =>
    exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) (v i) (by rw [(h.1 i).1, Category.assoc])
  have e : v = fun i => v' i ≫ m.φ := funext fun i => (hv2 i).symm
  subst e
  refine ⟨v', fun i => rfl, fun i => (tan_iff m rfl (hv1 i)).1 (h.1 i), fun i a => (eig_iff m (hv1 i) a _).1 (h.2.1 i a),
    fun w hw he => ?_⟩
  have hb := h.2.2 (w ≫ m.φ) ((tan_iff m rfl hw.1).2 hw) fun a => (eig_iff m hw.1 a _).2 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv1 cf hw.1).1 hb

end Transport

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrueCx.TorHolo

section Hol

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Z : Scheme.{0}}

theorem isHolTo_of_openImmersion (i : X ⟶ Z) [IsOpenImmersion i] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have hU : i ⁻¹ᵁ (i ''ᵁ U) = U := i.preimage_image_eq U
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [← ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp] at this
    exact this
  exact key U hU f

theorem isHolTo_const {B : Set W} (hB : IsOpen B) (x : Sp ℂ ⟶ X) : IsHolTo B fun _ => x := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simpa only [h, and_true, Set.ofPred_mem_eq] using hB
  · simpa only [h, and_false, Set.ofPred_false] using isOpen_empty

theorem isHolTo_of_fst {S : Scheme.{0}} (p : X ⟶ Z) (q : S ⟶ Z) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    {y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback p q)} (s : Sp ℂ ⟶ S) (hs : ∀ b, y b ≫ pullback.snd _ _ = s)
    (h : IsHolTo B fun b => y b ≫ pullback.fst _ _) : IsHolTo B y := by
  have he : ∀ b, (y b ≫ pullback.fst p q) ≫ p = s ≫ q := fun b => by
    rw [← hs b, Category.assoc, Category.assoc, pullback.condition]
  refine LocLift.isHolTo_congr (holPair _ _ _ p q n B _ (fun _ => s) he hB h (isHolTo_const hB s)) fun b _ => ?_
  exact pullback.hom_ext (pullback.lift_fst _ _ _).symm ((hs b).trans (pullback.lift_snd _ _ _).symm)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousOn_of_isHolTo {B : Set W} {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1) :
    ContinuousOn y B := by
  rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
    ext b
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩

theorem differentiableAt_chart {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (h : IsHolTo B fun b => (y b).1)
    (ch : AlgChart p σ D) {b : W} (hb : b ∈ B) (hy : y b ∈ ch.e.source) :
    DifferentiableAt ℂ (fun v => ch.e (y v)) b := by
  refine (differentiableAt_piLp 2).2 fun a => ?_
  have h1 := ((h ch.U (ch.x a)).2).differentiableAt ((h ch.U (ch.x a)).1.mem_nhds ⟨hb, ch.source_subset hy⟩)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [((continuousOn_of_isHolTo h).continuousAt (hB.mem_nhds hb)).preimage_mem_nhds
    (ch.e.open_source.mem_nhds hy)] with v hv
  exact ch.apply_eq _ hv a

theorem isHolTo_symm (ch : AlgChart p σ D) : IsHolTo ch.e.target fun v => (ch.e.symm v).1 := fun U f =>
  ⟨ChartGlue.isOpen_over ch.e (isOpen_ptsIn U), ch.holo U f⟩

end Hol

section Frames

open GlobalTheory.TorsionHolomorphic ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} {Tau : Type}
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (X : Data E r) {B : Set W}

theorem differentiableOn_perFr {x : W → Frame X.Ψ r} (hx : ∀ b ∈ B, x b ∈ X.dom)
    (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b) τ a c) B) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    DifferentiableOn ℂ (fun b => perFr X (x b) v τ i) B := by
  unfold perFr
  split_ifs with h1 h2 h3 h4
  · simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun a _ =>
      (differentiableOn_matrix_inv _ B (hd _) (fun b hb => (hx b hb _).1) _ _).mul_const _
  · exact differentiableOn_const _
  · simp only [hermC]
    exact DifferentiableOn.fun_sum fun a _ => DifferentiableOn.fun_sum fun c _ =>
      ((hd _ _ _).mul_const _).mul_const _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

theorem differentiable_stdMat [Fintype Tau] (hj : j ≤ r) (κ : Tau ≃ X.Ψ) (τ : X.Ψ) (a c : Fin r) :
    Differentiable ℂ fun v => mat (stdMat X hj κ (unflat v)) τ a c := by
  refine differentiableOn_univ.1 (differentiableOn_matrix_mul (fun _ => mat (x0F X) τ)
    (fun v => reindex (idx hj).symm (idx hj).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) _
    (fun _ _ => differentiableOn_const _) (fun a c => ?_) a c)
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm]
  rcases idx hj a with a | a <;> rcases idx hj c with c | c
  · exact differentiableOn_const _
  · exact differentiableOn_apply (κ.symm τ, a, c) _
  · exact differentiableOn_const _
  · exact differentiableOn_const _

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) {σ : c.F →+* ℂ} {U : Unf Xo c σ r}

end Frames

end GlobalTheory.TrueCx.TorHolo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.CoordUniq

section Lin

variable {K : Type} [Field K] {m n : ℕ}

theorem tri_of_mul {T₁ T₂ M : Fin m → Fin m → K} (h₁ : ∀ i k, i < k → T₁ i k = 0) (h₂ : ∀ i k, i < k → T₂ i k = 0)
    (hd : ∀ i, T₂ i i ≠ 0) (h : ∀ i k, T₁ i k = ∑ j, T₂ i j * M j k) (i : Fin m) : ∀ k, i < k → M i k = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro k hk
    have e := h i k
    rw [h₁ i k hk, Finset.sum_eq_single i (fun j _ hj => by
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [ih j hj k (hj.trans hk), mul_zero]
      · rw [h₂ i j hj, zero_mul]) (by simp)] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hd i)

theorem diag_of_mul {T₂ M : Fin m → Fin m → K} (h₂ : ∀ i k, i < k → T₂ i k = 0) (hM : ∀ i k, i < k → M i k = 0)
    (i : Fin m) : ∑ j, T₂ i j * M j i = T₂ i i * M i i :=
  Finset.sum_eq_single i (fun j _ hj => by
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hM j i hj, mul_zero]
    · rw [h₂ i j hj, zero_mul]) (by simp)

theorem indep_of_tri {T : Fin m → Fin m → K} (h : ∀ i k, i < k → T i k = 0) (hd : ∀ i, T i i ≠ 0)
    {e : Fin m → Fin n → K} (hg : ∀ a : Fin m → K, ∑ i, a i • ∑ j, T i j • e j = 0 → a = 0)
    {b : Fin m → K} (hb : ∑ j, b j • e j = 0) : b = 0 := by
  have hdet : IsUnit (Matrix.of T).det := by
    rw [Matrix.det_of_isLowerTriangular (Matrix.of T) (fun i k hk => h i k hk)]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have e1 : Matrix.vecMul (Matrix.vecMul b (Matrix.of T)⁻¹) (Matrix.of T) = b := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have e2 := hg (Matrix.vecMul b (Matrix.of T)⁻¹) (by
    rw [← hb]
    conv_rhs => rw [← e1]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    rfl)
  rw [← e1, e2, Matrix.zero_vecMul]

end Lin

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_matrix {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ f₂ : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ M : Fin (Dw.mult τ) → Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∃ T₁ T₂ : Fin (Dw.mult τ) → Fin (Dw.mult τ) → k,
        (∀ i, T₁ i i = t₁ τ i) ∧ (∀ i, T₂ i i = t₂ τ i) ∧ (∀ i k, i < k → T₁ i k = 0) ∧ (∀ i k, i < k → T₂ i k = 0) ∧
          ∀ i k, T₁ i k = ∑ j, T₂ i j * ψ (M j k) := by
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan τ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan τ i)
  choose M hM using fun i => (f₁.basis τ _ (f₂.tan τ i) (f₂.eig τ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v τ = fun j => vec Z.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  refine ⟨M, fun {k} _ ψ φ' x' g t₁ t₂ h₁ h₂ => ?_⟩
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  choose T₁ a₁ b₁ c₁ using h₁ τ
  choose T₂ a₂ b₂ c₂ using h₂ τ
  letI : Algebra R k := ψ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  change ∀ cc, vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec Z.t x xc cc at hv
  choose G hG using fun i => vec_exists hx' _ (g.tan τ i)
  have d₁ : ∀ i, G i = ∑ j, T₁ i j • (ψ ∘ e₁ j) := fun i => by
    have := c₁ i
    simp only [he₁, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have d₂ : ∀ i, G i = ∑ j, T₂ i j • (ψ ∘ e₂ j) := fun i => by
    have := c₂ i
    simp only [he₂, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have hind : ∀ a : Fin (Dw.mult τ) → k, ∑ i, a i • G i = 0 → a = 0 := fun a ha => by
    have hb := g.basis τ _ (vec_tan hx' 0) ((vec_eig_iff hx' _ _).2 (Submodule.zero_mem _))
    rw [show g.v τ = fun j => vec Z.t _ xc' (G j) from funext hG] at hb
    exact hb.unique ((comb_iff hx' _ _ _).2 ha.symm) ((comb_iff hx' _ _ _).2 (by simp))
  refine ⟨T₁, T₂, a₁, a₂, b₁, b₂, fun i k' => ?_⟩
  have := indep_of_tri b₁ (fun i => a₁ i ▸ (t₁ τ i).ne_zero) (e := fun j => ψ ∘ e₁ j)
    (fun a ha => hind a (by simpa only [d₁] using ha))
    (b := fun k' => T₁ i k' - ∑ j, T₂ i j * ψ (M j k')) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← d₁, d₂, sub_eq_zero]
      funext q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hM', Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm)
  exact sub_eq_zero.1 (congrFun this k')

theorem exists_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, (t₁ τ i : k) = t₂ τ i * ψ (u τ i) := by
  obtain rfl : φ₁ = φ₂ := RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))
  choose M hM using exists_matrix f₁ f₂
  have hT : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hk => by
    obtain ⟨T₁, T₂, -, a₂, b₁, b₂, h⟩ := hM τ ι f₀ t₁ t₂ h₁ h₂
    exact hι ((tri_of_mul (M := fun i k => ι (M τ i k)) b₁ b₂ (fun i => a₂ i ▸ (t₂ τ i).ne_zero) h i k hk).trans
      (map_zero ι).symm)
  refine ⟨fun τ i => M τ i i, fun {k} _ ψ φ' x' g s₁ s₂ g₁ g₂ τ i => ?_⟩
  obtain ⟨T₁, T₂, a₁, a₂, -, b₂, h⟩ := hM τ ψ g s₁ s₂ g₁ g₂
  rw [← a₁, ← a₂, h]
  exact diag_of_mul (M := fun i k => ψ (M τ i k)) b₂ (fun i k hk => by simp only [hT τ i k hk, map_zero]) i

theorem exists_unit_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, t₁ τ i = t₂ τ i * Units.map (ψ : R →* k) (u τ i) := by
  obtain ⟨u, hu⟩ := exists_ratio f₁ f₂ hι h₁ h₂
  obtain ⟨v, hv⟩ := exists_ratio f₂ f₁ hι h₂ h₁
  have huv : ∀ τ i, u τ i * v τ i = 1 := fun τ i => hι (by
    have a := hu ι f₀ _ _ h₁ h₂ τ i
    have b := hv ι f₀ _ _ h₂ h₁ τ i
    rw [a, mul_assoc] at b
    rw [map_mul, map_one]
    exact (mul_left_cancel₀ (t₂ τ i).ne_zero ((mul_one _).trans b)).symm)
  exact ⟨fun τ i => Units.mkOfMulEqOne _ _ (huv τ i), fun ψ _ _ g s₁ s₂ g₁ g₂ τ i =>
    Units.ext (hu ψ g s₁ s₂ g₁ g₂ τ i)⟩

end Frames

theorem isLocalHom_of_algebraic {R F k : Type} [CommRing R] [IsLocalRing R] [Field F] [CharZero F] (φ : F →+* R)
    [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (ψ : R →+* k) : IsLocalHom ψ := by
  letI : Algebra ℚ R := (φ.comp (algebraMap ℚ F)).toAlgebra
  let ψ' : R →ₐ[ℚ] k := { ψ with commutes' := fun q => by simp }
  refine ⟨fun a ha => ?_⟩
  have h0 : ψ a ≠ 0 := ha.ne_zero
  have hi : IsIntegral ℚ (ψ a) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hc := minpoly.coeff_zero_ne_zero hi h0
  have h1 : ψ (Polynomial.aeval a (minpoly ℚ (ψ a))) = 0 :=
    (Polynomial.aeval_algHom_apply ψ' a _).symm.trans (minpoly.aeval ℚ (ψ a))
  have h2 : ¬ IsUnit (Polynomial.aeval a (minpoly ℚ (ψ a))) := fun h => (h.map ψ).ne_zero h1
  by_contra hna
  rw [← Polynomial.X_mul_divX_add (minpoly ℚ (ψ a)), map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  have h3 : algebraMap ℚ R ((minpoly ℚ (ψ a)).coeff 0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem (IsLocalRing.maximalIdeal R) h2
      (Ideal.mul_mem_right (Polynomial.aeval a (minpoly ℚ (ψ a)).divX) _ hna)
    rwa [add_sub_cancel_left] at this
  exact h3 (hc.isUnit.map _)

theorem stalk_ext {X : Scheme.{0}} {k : Type} [Field k] {y y' : X} {ψ : X.presheaf.stalk y →+* k}
    {ψ' : X.presheaf.stalk y' →+* k} (h : IsLocalHom ψ) (h' : IsLocalHom ψ')
    (e : spMap ψ ≫ X.fromSpecStalk y = spMap ψ' ≫ X.fromSpecStalk y') : y = y' ∧ HEq ψ ψ' := by
  have := (SpecToEquivOfLocalRing X (.of k)).symm.injective (a₁ := ⟨y, CommRingCat.ofHom ψ, h⟩)
    (a₂ := ⟨y', CommRingCat.ofHom ψ', h'⟩) e
  obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 this
  exact ⟨rfl, heq_of_eq (congrArg (fun f => f.1.hom) (eq_of_heq e'))⟩

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

end Coord

end GlobalTheory.ShFam.CoordUniq
end
end

