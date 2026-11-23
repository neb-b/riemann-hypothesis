module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSiegelReductionOrthogonal
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.RedTh

def siegelGlueMat {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin (s + m)) (Fin (s + m)) ℝ := fun i j =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun y => a x y) (fun _ => 0) j)
    (fun x => Fin.addCases (motive := fun _ => ℝ) (fun _ => 0) (fun y => b x y) j) i

@[simp] lemma siegelGlueMat_ll {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin s) : siegelGlueMat a b (Fin.castAdd m x) (Fin.castAdd m y) = a x y := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_lr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin s) (y : Fin m) : siegelGlueMat a b (Fin.castAdd m x) (Fin.natAdd s y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rl {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m) (y : Fin s) : siegelGlueMat a b (Fin.natAdd s x) (Fin.castAdd m y) = 0 := by
  simp [siegelGlueMat]

@[simp] lemma siegelGlueMat_rr {s m : ℕ} (a : Matrix (Fin s) (Fin s) ℝ) (b : Matrix (Fin m) (Fin m) ℝ)
    (x y : Fin m) : siegelGlueMat a b (Fin.natAdd s x) (Fin.natAdd s y) = b x y := by
  simp [siegelGlueMat]

lemma gram_apply_glue {n : ℕ} (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    gram d u i j = ∑ k, u k i * d k * u k j := by
  simp only [gram]
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal]

lemma siegelGlue_scale {s m : ℕ} (d₁ : Fin s → ℝ) (d₂ : Fin m → ℝ) (h₁ : ∀ i, 0 < d₁ i)
    (h₂ : ∀ i, 0 < d₂ i) :
    ∃ t : ℝ, 0 < t ∧ ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → t * d₁ i ≤ 4 * d₂ j := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact ⟨1, one_pos, fun _ j => j.elim0⟩
  · set j0 : Fin m := ⟨0, hm⟩
    have hS : 0 ≤ ∑ i, d₁ i := Finset.sum_nonneg (fun i _ => (h₁ i).le)
    refine ⟨d₂ j0 / (1 + ∑ i, d₁ i), div_pos (h₂ j0) (by linarith), fun i j hj => ?_⟩
    have hj' : j = j0 := Fin.ext hj
    subst hj'
    have hi : d₁ i ≤ ∑ k, d₁ k := Finset.single_le_sum (fun k _ => (h₁ k).le) (Finset.mem_univ i)
    have hpos : 0 < 1 + ∑ k, d₁ k := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    have := h₂ j0
    nlinarith

lemma isSiegel_glue {s m : ℕ} {e₁ : Fin s → ℝ} {u₁ : Matrix (Fin s) (Fin s) ℝ} {e₂ : Fin m → ℝ}
    {u₂ : Matrix (Fin m) (Fin m) ℝ} (h₁ : IsSiegel e₁ u₁) (h₂ : IsSiegel e₂ u₂)
    (hj : ∀ (i : Fin s) (j : Fin m), (j : ℕ) = 0 → e₁ i ≤ 4 * e₂ j) :
    IsSiegel (Fin.append e₁ e₂) (siegelGlueMat u₁ u₂) := by
  refine IsSiegel.mk ?_ ?_ ?_ ?_ ?_
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using h₁.nonneg a
    | right a => simpa using h₂.nonneg a
  · intro p q h
    induction p using Fin.addCases with
    | left a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd] at h
        simpa using h₁.step a b h
      | right b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := a.isLt
        simpa using hj a b (by omega)
    | right a =>
      induction q using Fin.addCases with
      | left b =>
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h
        have := b.isLt
        omega
      | right b =>
        simp only [Fin.val_natAdd] at h
        simpa using h₂.step a b (by omega)
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using h₁.diag a
    | right a => simpa using h₂.diag a
  · intro i j h
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.lower a b (by rw [Fin.lt_def] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.lower a b (by rw [Fin.lt_def] at h ⊢; simpa using h)
  · intro i j h
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        rw [siegelGlueMat_ll]
        exact h₁.upper a b (by rw [Fin.lt_def] at h ⊢; simpa using h)
      | right b => simp
    | right a =>
      induction j using Fin.addCases with
      | left b => simp
      | right b =>
        rw [siegelGlueMat_rr]
        exact h₂.upper a b (by rw [Fin.lt_def] at h ⊢; simpa using h)

lemma isSiegel_zero_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u) :
    IsSiegel (0 : Fin n → ℝ) u :=
  IsSiegel.mk (fun _ => le_refl _) (by simp) h.diag h.lower h.upper

lemma isSiegel_smul_of {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : IsSiegel d u)
    {t : ℝ} (ht : 0 ≤ t) : IsSiegel (fun i => t * d i) u := by
  refine IsSiegel.mk (fun i => mul_nonneg ht (h.nonneg i)) ?_ h.diag h.lower h.upper
  intro p q hpq
  have := h.step p q hpq
  nlinarith

theorem siegelData_glue_scaled : ∀ (s m : ℕ) (d₁ : Fin s → ℝ) (u₁ : Matrix (Fin s) (Fin s) ℝ) (d₂ : Fin m → ℝ) (u₂ : Matrix (Fin m) (Fin m) ℝ), IsSiegel d₁ u₁ → IsSiegel d₂ u₂ → (∀ i, 0 < d₁ i) → (∀ i, 0 < d₂ i) → ∃ (t : ℝ) (d d' : Fin (s + m) → ℝ) (u : Matrix (Fin (s + m)) (Fin (s + m)) ℝ), 0 < t ∧ IsSiegel d u ∧ IsSiegel d' u ∧ (∀ i, 0 < d' i) ∧ (∀ i j : Fin s, gram d u (Fin.castAdd m i) (Fin.castAdd m j) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.castAdd m j) = t * gram d₁ u₁ i j) ∧ (∀ (i : Fin s) (j : Fin m), gram d u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d u (Fin.natAdd s j) (Fin.castAdd m i) = 0 ∧ gram d' u (Fin.castAdd m i) (Fin.natAdd s j) = 0 ∧ gram d' u (Fin.natAdd s j) (Fin.castAdd m i) = 0) ∧ ∀ i j : Fin m, gram d u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j ∧ gram d' u (Fin.natAdd s i) (Fin.natAdd s j) = gram d₂ u₂ i j := by
  intro s m d₁ u₁ d₂ u₂ h₁ h₂ p₁ p₂
  obtain ⟨t, ht, hj⟩ := siegelGlue_scale d₁ d₂ p₁ p₂
  refine ⟨t, Fin.append (0 : Fin s → ℝ) d₂, Fin.append (fun i => t * d₁ i) d₂, siegelGlueMat u₁ u₂, ht,
    isSiegel_glue (isSiegel_zero_of h₁) h₂ (fun i j _ => by simpa using (h₂.nonneg j)),
    isSiegel_glue (isSiegel_smul_of h₁ ht.le) h₂ hj, ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left a => simpa using mul_pos ht (p₁ a)
    | right a => simpa using p₂ a
  · intro i j
    refine ⟨?_, ?_⟩
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue, Finset.mul_sum]
      simp only [siegelGlueMat_ll, siegelGlueMat_rl, Fin.append_left, Fin.append_right, zero_mul,
        mul_zero, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  · intro i j
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add]
      simp
  · intro i j
    refine ⟨?_, ?_⟩ <;>
    · rw [gram_apply_glue, Fin.sum_univ_add, gram_apply_glue]
      simp

end GlobalTheory.RedTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelLatticeRiemannFormOffBoundary
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_eq_comp_linearEquiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (p : Sp ℂ ⟶ X) (g g' : ℕ) (ex : (Fin g → ℂ) → (Over.mk p ⟶ t.G)) (e' : (Fin g' → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p ex → IsHolTo Set.univ (fun w => (ex w).left) → IsExpAt t p e' → IsHolTo Set.univ (fun w => (e' w).left) → ∃ L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' z = ex (L z) := by
  intro E _ _ _ H X t p g g' ex e' hex hhol he' hhol'
  have one : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), (∀ z w, f (z + w) = f z * f w) → f 0 = 1 := by
    intro m f hf
    have h := hf 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have der : ∀ {m : ℕ} (f : (Fin m → ℂ) → (Over.mk p ⟶ t.G)), IsExpAt t p f →
      ∀ v : epsPt p ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (f 0).left →
        ∃! w, IsDerivAt0 (fun z => (f z).left) w v.left := by
    intro m f hf v hv
    refine hf.2.2 v.left ⟨Over.w v, ?_⟩
    rw [hv, one f hf.1]
  have H3 := (GlobalTheory.holomorphic_hom_determined X t.G).2.2.1 p
  obtain ⟨h, hh, -⟩ := H3 (Fin g' → ℂ) g e' ex he'.1 hex.1 hhol' hhol (der ex hex)
  obtain ⟨h', hh', -⟩ := H3 (Fin g → ℂ) g' ex e' hex.1 he'.1 hhol hhol' (der e' he')
  obtain ⟨k, -, hk⟩ := H3 (Fin g' → ℂ) g' e' e' he'.1 he'.1 hhol' hhol' (der e' he')
  obtain ⟨k', -, hk'⟩ := H3 (Fin g → ℂ) g ex ex hex.1 hex.1 hhol hhol (der ex hex)
  have c1 : h' ∘ₗ h = LinearMap.id :=
    (hk _ fun z => by rw [LinearMap.comp_apply, ← hh', ← hh]).trans (hk _ fun z => rfl).symm
  have c2 : h ∘ₗ h' = LinearMap.id :=
    (hk' _ fun z => by rw [LinearMap.comp_apply, ← hh, ← hh']).trans (hk' _ fun z => rfl).symm
  exact ⟨LinearEquiv.ofLinear h h' c2 c1, hh⟩

theorem exists_hermForm_transport : ∀ (g g' : ℕ) (L : (Fin g' → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (Hm₀ : Matrix (Fin g') (Fin g') ℂ), Hm₀.IsHermitian → (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (hermForm Hm₀ z z).re) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ v w, hermForm Hm (L v) (L w) = hermForm Hm₀ v w := by
  intro g g' L Hm₀ hH hpos
  let A : Matrix (Fin g') (Fin g) ℂ := LinearMap.toMatrix' L.symm.toLinearMap
  have hA : ∀ v, A.mulVec v = L.symm v := fun v => LinearMap.toMatrix'_mulVec _ v
  have key : ∀ v w, hermForm (Aᵀ * Hm₀ * A.map star) v w = hermForm Hm₀ (L.symm v) (L.symm w) := by
    intro v w
    simp only [hermForm, ← hA]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
    congr 1
    ext j
    simp [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, mul_comm]
  refine ⟨Aᵀ * Hm₀ * A.map star, ?_, fun z hz => ?_, fun v w => ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hH.eq, Matrix.mul_assoc]
    congr 1
    · ext a b
      simp [Matrix.conjTranspose_apply]
  · rw [key]
    exact hpos _ (by simpa using hz)
  · rw [key, L.symm_apply_apply, L.symm_apply_apply]

theorem exists_pushed_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X), IsPeriod (Fu.Di i) ty P → Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) → y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p → ∃ e' : (Fin g → ℂ) → (Over.mk p ⟶ Z.t.G), IsExpAt Z.t p e' ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ (∀ z, e' z = 1 ↔ z ∈ P.range) ∧ ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hP hu hp
  exact ⟨pushEx Z Fu y i P p hu hp, _root_.GlobalTheory.ShFam.Hor.LogCh.isExpAt_pushEx E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    _root_.GlobalTheory.ShFam.Hor.LogCh.pushEx_hol E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    _root_.GlobalTheory.ShFam.Hor.LogCh.pushEx_eq_one_iff E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP,
    GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm E H Dw l Xo c O β Z g ty σ₀ Fu y i P p hu hp hP⟩

theorem kernel_lattice_of_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (x : CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g x ex hσ hpq hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  let e₀ : Fin (Fintype.card (Letter Dw)) ≃ Letter Dw := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c σ (e₀ j).1) hpq hσ hty
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := Fu.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ Fu y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨Hm, hH, hpos, ?_, ?_, ?_⟩
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(Fu.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.FlagMod (ev lieBasis rdet detChg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

section Basis

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}

theorem exists_eigBasis (g : EigFrame Z φ x) : ∃ b : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G),
    ∀ p, b p = g.vec p.1 p.2 := by
  have heig : ∀ (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → R) (b : 𝓞 E),
      actR Z.t.act b (∑ i, a i • g.vec τ i) = φ (embK c τ b) • ∑ i, a i • g.vec τ i := fun τ a b => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, g.act_vec, Finset.smul_sum, smul_comm (a _)]
  have hli : LinearIndependent R (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha p
    have hw := (_root_.GlobalTheory.EigDecomp.exists_unique_eigen_sum c φ (actR Z.t.act) 0).unique
      (y₁ := fun τ => ∑ i, a ⟨τ, i⟩ • g.vec τ i) (y₂ := fun _ => 0)
      ⟨fun τ b => heig τ _ b, by rw [← ha, Fintype.sum_sigma]⟩ ⟨fun τ b => by simp, by simp⟩
    have h0 := congrFun hw p.1
    exact Fintype.linearIndependent_iff.1 (g.linearIndependent_vec p.1) (fun i => a ⟨p.1, i⟩) h0 p.2
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    intro v _
    obtain ⟨w, ⟨hw, hs⟩, -⟩ := _root_.GlobalTheory.EigDecomp.exists_unique_eigen_sum c φ (actR Z.t.act) v
    rw [← hs]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := g.existsUnique_sum τ (w τ) (hw τ)
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨τ, i⟩, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun p => by rw [Module.Basis.mk_apply]⟩

def eigBasis (g : EigFrame Z φ x) : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G) :=
  (exists_eigBasis g).choose

theorem eigBasis_apply (g : EigFrame Z φ x) (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eigBasis g p = g.vec p.1 p.2 :=
  (exists_eigBasis g).choose_spec p

def eigBasisFin (g : EigFrame Z φ x) : Module.Basis (Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) R (TanM x Z.t.G) :=
  (eigBasis g).reindex (Fintype.equivFin _)

def frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : R :=
  rdet ((lieBasis M x h).toMatrix (eigBasisFin g))

theorem isUnit_frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : IsUnit (frameDet M h g) :=
  GlobalTheory.FlagMod.isUnit_rdet_toMatrix _ _

theorem ev_detChg_mul_frameDet (M M' : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) (g : EigFrame Z φ x) :
    ev x _ hh (detChg M M').val * frameDet M' h' g = frameDet M h g := by
  rw [GlobalTheory.FlagMod.ev_detChg M M' x h h' hh, frameDet, frameDet, GlobalTheory.FlagMod.rdet_toMatrix_mul]


open Classical in
theorem eigBasis_toMatrix (g g' : EigFrame Z φ x) :
    (eigBasis g).toMatrix (eigBasis g') = Matrix.blockDiagonal' fun τ => g.co g' τ := by
  classical
  ext ⟨σ, b⟩ ⟨τ, i⟩
  have hv : ∀ a, g.vec τ a = eigBasis g ⟨τ, a⟩ := fun a => (eigBasis_apply g ⟨τ, a⟩).symm
  rw [Module.Basis.toMatrix_apply, eigBasis_apply, g.vec_eq g' τ i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hv, map_sum, map_smul, Module.Basis.repr_self]
  by_cases h : σ = τ
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq, Finsupp.single_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp [Finsupp.single_apply, show ∀ a, (⟨τ, a⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≠ ⟨σ, b⟩ from
      fun a e => h (congrArg Sigma.fst e).symm]

open Classical in
theorem frameDet_change (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g g' : EigFrame Z φ x) :
    frameDet M h g' = frameDet M h g * ∏ τ, (g.co g' τ).det := by
  rw [frameDet, frameDet, ← GlobalTheory.FlagMod.rdet_toMatrix_mul _ (eigBasisFin g), GlobalTheory.FlagMod.rdet_self]
  congr 1
  have e : (eigBasisFin g).toMatrix (eigBasisFin g') =
      ((eigBasis g).toMatrix (eigBasis g')).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm := by
    ext i j
    simp [eigBasisFin, Module.Basis.toMatrix_apply]
  rw [e, Matrix.det_submatrix_equiv_self, eigBasis_toMatrix, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']

end Basis

section Flag

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem ev_fromSpecStalk_eq {Y : Scheme.{0}} (x : Y) {V : Y.Opens} (hx : x ∈ V) (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V)
    (u : Γ(Y, V)) : ev (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

theorem top_le_stalk_preimage {X Y : Scheme.{0}} (y : X) (f : X ⟶ Y) {V : Y.Opens} (hy : f y ∈ V) :
    ⊤ ≤ (X.fromSpecStalk y ≫ f) ⁻¹ᵁ V := by
  intro z _
  have hz : X.fromSpecStalk y z ⤳ y := by
    have : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (hz.map f.continuous).mem_open V.isOpen hy

theorem fnOf_app_eq_ev {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) {V : Y.Opens} (hg : genericPoint X ∈ f ⁻¹ᵁ V)
    (hh : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ f) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    fnOf (f ⁻¹ᵁ V) hg ((f.app V).hom a) = ev (X.fromSpecStalk (genericPoint X) ≫ f) V hh a := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (f ⁻¹ᵁ V) := top_le_stalk_preimage (genericPoint X) (𝟙 X) hg
  refine (ev_fromSpecStalk_eq (genericPoint X) hg h1 _).symm.trans (Eq.trans ?_
    (GlobalTheory.FlagMod.ev_appLE (X.fromSpecStalk (genericPoint X)) f le_rfl h1 hh a))
  rw [Scheme.Hom.app_eq_appLE]

variable {C}

variable (C)


end Flag

section Presents

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

end Presents

section Presents2

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem isEqn_finset_sum {X : Scheme.{0}} [IsIntegral X] {T : Type} (s : Finset T) (D : T → CartierDiv X) (y : X)
    (t : T → X.functionFieldˣ) (ht : ∀ i, (D i).IsEqn y (t i)) : (∑ i ∈ s, D i).IsEqn y (∏ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (ht a).add ih

end Presents2

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdealAlongStalkPointEqMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TraitStalk

theorem idlAlong_spMap_fromSpecStalk : ∀ (T : Scheme.{0}) (v : T) (J : T.IdealSheafData) (W : Type) [CommRing W] [IsLocalRing W]
    (g : T.presheaf.stalk v →+* W), IsLocalHom g → idlAlong J (spMap g ≫ T.fromSpecStalk v) = (FinalTheorems.stalkId J v).map g :=
  fun _ v J _ _ _ g _ => GlobalTheory.PolDiv.idlAlong_fromSpecStalk J v g

end GlobalTheory.TraitStalk
end

