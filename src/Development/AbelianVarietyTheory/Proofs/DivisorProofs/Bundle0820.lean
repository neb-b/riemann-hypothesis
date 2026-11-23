module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReordEqConj
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.ColumnMultSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def permUnit (κ : Type) [CommRing κ] {r : ℕ} (π : Equiv.Perm (Fin r)) : GL (Fin r) κ where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem reord_eq_conj {D : D7} {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) :
    ∃ w : G0 Pg r, ∀ g : G0 Pg r, reord π g = w * g * w⁻¹ := by
  refine ⟨fun PP => permUnit (kP PP.1) π, fun g => ?_⟩
  funext PP
  apply Units.ext
  show Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) π.symm (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) =
    π.toPEquiv.toMatrix * (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) * π.symm.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

theorem columnMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.Pg.card = 2 * D.R.f → (∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP)) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (∀ χ ∈ A.X, IsAbsIrrChar χ) → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P1], ∀ χ ∈ A.X, ∃ n : ℕ, (Nat.card F.P1 : D.what₂.LL)⁻¹ * ∑ h : F.P1, χ (h : G) * (((F.ψ1 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (n : D.what₂.LL) ∧ |(n : ℝ) - (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ)| ≤ 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hcard hq hadm hirr hprod _ χ hχ
  classical
  obtain ⟨ψ, hψ, -, π, -, hmem, hchi⟩ := hlev
  obtain ⟨w, hw⟩ := reord_eq_conj (D := D) (Pg := R.Pg) π
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  have hg : 0 < min (D.host.g 0) (D.host.g 1) := lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar (RingHom.id ℂ) R.Pg D.R.r fun g => D.what₂.embLL (χ (R.eG.symm g)) :=
    hprod χ hχ
  obtain ⟨⟨n, hn, hb⟩, -⟩ := GlobalTheory.FinGL.MultSharpObj.multSharp D.host.E ℂ (RingHom.id ℂ) R.Pg D.R.f
    (min (D.host.g 0) (D.host.g 1)) D.R.r D.R.rS D.R.k ψ hcard hk hr hg hadm hq hψ _ hp
  refine ⟨n, ?_, hb⟩
  have hm : ∀ g : G, R.eG g ∈ (R.levR F true).H ↔ g ∈ F.P1 := fun g => by
    show R.eG.symm (R.eG g) ∈ F.P1 ↔ _
    rw [MulEquiv.symm_apply_apply]
  have hc : ∀ (g : G) (h : R.eG g ∈ (R.levR F true).H), (((R.levR F true).chi ⟨R.eG g, h⟩ : ℂˣ) : ℂ) =
      D.what₂.embLL ((F.ψ1 ⟨g, (hm g).1 h⟩ : D.what₂.LLˣ) : D.what₂.LL) := fun g h => by
    show D.what₂.embLL ((F.ψ1 ⟨R.eG.symm (R.eG g), h⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply g
  let e : F.P1 ≃ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H :=
    (R.eG.trans (MulAut.conj w)).toEquiv.subtypeEquiv fun g => by
      rw [← hm, hmem, hw]; rfl
  apply D.what₂.embLL.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_natCast, ← hn, map_mul, map_inv₀, map_natCast, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.levelMult
  rw [Nat.card_congr e]
  congr 1
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_boundedLevelClassGroupFamily R.Pg D.R.r
  letI : Fintype (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H := Fintype.ofFinite _
  refine Fintype.sum_equiv e _ _ fun x => ?_
  have h1 : R.eG x ∈ (R.levR F true).H := (hm x).2 x.2
  have h2 := (hmem _).1 h1
  have he : e x = ⟨reord π (R.eG x), h2⟩ := Subtype.ext (hw _).symm
  rw [he, ← hchi _ h1 h2, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, hc]
  congr 2
  show χ x = χ (R.eG.symm (reord π (R.eG x)))
  rw [hw, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, (hirr χ hχ).conj]

end GlobalTheory.ColumnMultSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffine
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PeriodCoord

private theorem inv_mul_eq_mul_inv_of_intertwine {n : Type} [Fintype n] [DecidableEq n]
    (A B D : Matrix n n ℂ) (hA : A.det ≠ 0) (hD : D.det ≠ 0) (h : B * D = A * B) :
    A⁻¹ * B = B * D⁻¹ := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  calc A⁻¹ * B = A⁻¹ * (B * D) * D⁻¹ := by
          rw [Matrix.mul_assoc A⁻¹, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD', Matrix.mul_one]
    _ = A⁻¹ * A * B * D⁻¹ := by rw [h, Matrix.mul_assoc A⁻¹ A B]
    _ = B * D⁻¹ := by rw [Matrix.nonsing_inv_mul _ hA', Matrix.one_mul]

private theorem star_dot_mulVec {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    star (x ⬝ᵥ A *ᵥ y) = star x ⬝ᵥ A.map star *ᵥ star y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum]

private theorem star_mulVec' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  simp [mulVec, dotProduct, star_sum]

private theorem dot_left {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ Aᵀ *ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

private theorem map_star_mul' {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private theorem map_star_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : (A.map star).map star = A := by
  ext i j; simp

private theorem conj_transpose_intertwine {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) : (C.map star)ᵀ * Cᵀ * M₀ = M₀ * C.map star * C := by
  have f0 : M₀.map star = M₀ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simpa [conjTranspose_apply] using this
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have f1' : M₀ * C.map star = (C.map star)ᵀ * M₀ᵀ := by
    have := congrArg (fun A => A.map star) f1
    simp only [map_star_mul'] at this
    have e1 : (M₀ᵀ).map star = M₀ := by rw [transpose_map, f0, transpose_transpose]
    have e2 : (Cᵀ).map star = (C.map star)ᵀ := by rw [transpose_map]
    rw [e1, e2, f0] at this
    exact this
  rw [Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, ← f1']

theorem riemann_converse {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀) (_hdet : M₀.det ≠ 0)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) (hY : (1 - C.map star * C).det ≠ 0) :
    (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧
      ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im =
        (hermForm M₀ z w).im := by
  set Y := 1 - C.map star * C with hYdef
  set M := M₀ * Y⁻¹ with hMdef
  have f2 := conj_transpose_intertwine M₀ C hH hS
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have hYh : Yᴴ = 1 - (C.map star)ᵀ * Cᵀ := by
    rw [hYdef, conjTranspose_sub, conjTranspose_one, conjTranspose_mul]
    congr 2
    · ext i j; simp
  have hYt : Yᵀ = 1 - Cᵀ * (C.map star)ᵀ := by
    rw [hYdef, transpose_sub, transpose_one, transpose_mul]

  have ha : Mᴴ = M := by
    rw [hMdef, conjTranspose_mul, conjTranspose_nonsing_inv, hH]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYh, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, f2, Matrix.mul_assoc]
    · rw [det_conjTranspose]; exact star_ne_zero.mpr hY

  have hMbar : M.map star = Mᵀ := by
    ext i j
    have := congrFun (congrFun ha j) i
    simpa [conjTranspose_apply] using this
  have hb : M.map star * C = Cᵀ * M := by
    rw [hMbar, hMdef, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, f1, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYt, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc Cᵀ (C.map star)ᵀ, ← Matrix.mul_assoc (C.map star)ᵀ, f2]
      simp only [Matrix.mul_assoc]
    · rw [det_transpose]; exact hY

  have hc : M = M₀ + (C.map star)ᵀ * M.map star * C := by
    have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, hMdef, ← Matrix.mul_assoc, f2]
    have h0 : M₀ = M₀ * Y * Y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
    calc M₀ * Y⁻¹ = (M₀ * Y + M₀ * C.map star * C) * Y⁻¹ := by
          rw [Matrix.mul_assoc M₀ (C.map star), ← Matrix.mul_add, hYdef, sub_add_cancel, Matrix.mul_one]
      _ = M₀ * Y * Y⁻¹ + M₀ * C.map star * C * Y⁻¹ := Matrix.add_mul _ _ _
      _ = _ := by rw [← h0]
  refine ⟨ha, fun z w => ?_⟩
  have e : hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w) =
      z ⬝ᵥ M *ᵥ star w + z ⬝ᵥ (M * C.map star) *ᵥ w + star z ⬝ᵥ (Cᵀ * M) *ᵥ star w
        + star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w := by
    simp only [hermForm, star_add, star_mulVec', star_star, add_dotProduct, mulVec_add, dotProduct_add,
      dot_left, mulVec_mulVec, Matrix.mul_assoc]
    ring
  have e2 : star (z ⬝ᵥ (M * C.map star) *ᵥ w) = star z ⬝ᵥ (Cᵀ * M) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_map_star', hb]
  have e4 : star (star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w) = z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_mul', map_star_map_star', star_star, transpose_map]
  have e1 : z ⬝ᵥ M *ᵥ star w = hermForm M₀ z w + z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    conv_lhs => rw [hc]
    rw [hermForm, add_mulVec, dotProduct_add]
  rw [e, e1, ← e2, ← e4]
  simp only [Complex.add_im, Complex.star_def, Complex.conj_im]
  ring

end GlobalTheory.PeriodCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigOneAddMul
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

section Additive

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
  [Algebra R₀ R₁]

theorem sig_mem_map (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (y : R₁ ⊗[R₀] B₀) :
    σ y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem x))
  | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy

theorem sig_unique (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (hσ' : α.IsSig p σ') (y : R₁ ⊗[R₀] B₀) : σ y = σ' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sig_one_add_mul (hI : I ^ 2 = 0) (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (z z' : R₁ ⊗[R₀] B₀) : (1 + σ z) * (1 + σ z') = 1 + σ (z + z') := by
  have h0 : σ z * σ z' = 0 := by
    have hm := Ideal.mul_mem_mul (sig_mem_map α p hp σ hσ z) (sig_mem_map α p hp σ hσ z')
    rw [← Ideal.map_mul, ← sq, hI, Ideal.zero_eq_bot, Ideal.map_bot] at hm
    exact (Submodule.mem_bot _).1 hm
  rw [map_add (f := _)]
  linear_combination h0

end Additive

theorem isObU_mul : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u' c' → IsObU L α (fun T T' a ↦ u T T' a * u' T T' a) (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  refine ⟨fun T T' a ↦ v T T' a * v' T T' a, σ, z + z', fun T T' a ↦ ?_, hσ, (map_add _ _ _).symm,
    fun T T' T'' a b ↦ ⟨?_, ?_⟩⟩
  · simp only [Units.val_mul, map_mul, hv, hv']
  · have h1 := (hz T T' T'' a b).1
    have h2 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at h1 h2 ⊢
    change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (z.1 T T' T'' a b + z'.1 T T' T'' a b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  · have e := (hz T T' T'' a b).2
    have e' := (hz' T T' T'' a b).2
    have hs : σ' T'' (z'.1 T T' T'' a b) = σ T'' (z'.1 T T' T'' a b) :=
      sig_unique α (L.p T'') (L.surj T'') _ _ (hσ' T'') (hσ T'') _
    rw [hs] at e'
    change _ = (1 + σ T'' (z.1 T T' T'' a b + z'.1 T T' T'' a b)) * _
    rw [← sig_one_add_mul hI α (L.p T'') (L.surj T'') (σ T'') (hσ T'')]
    simp only [Units.val_mul, map_mul]
    calc L.ρ b (v T T' a : L.B T') * L.ρ b (v' T T' a : L.B T') * ((v T' T'' b : L.B T'') * (v' T' T'' b : L.B T''))
        = (L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'')) *
            (L.ρ b (v' T T' a : L.B T') * (v' T' T'' b : L.B T'')) := by ring
      _ = _ := by rw [e, e']; ring

end GlobalTheory.LBObs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

theorem app_presheaf_map {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem presheaf_map_map {Y : Scheme.{0}} {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h₂).op).hom ((Y.presheaf.map (homOfLE h₁).op).hom y) =
      (Y.presheaf.map (homOfLE (h₂.trans h₁)).op).hom y := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isBasis_smallG (hi : IsThick I s i) (hL : L.IsLB) : IsBasis (smallG i L) := by
  haveI := hi.closed
  have hind : Topology.IsInducing i.base := i.isClosedEmbedding.isInducing
  have cov : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : (Small i L)ᵒᵖ,
      x ∈ ((smallG i L).obj t).unop.1 ∧ ((smallG i L).obj t).unop.1 ≤ U := by
    intro x U hx
    obtain ⟨x₀, rfl⟩ := hi.surj.surj x
    have hx₀ : x₀ ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx₀
    obtain ⟨V, hV, hVe⟩ := hind.isOpen_iff.1 (L.U j).isOpen
    have hxV : i.base x₀ ∈ (⟨V, hV⟩ : X.Opens) ⊓ U := ⟨show x₀ ∈ i.base ⁻¹' V from hVe ▸ hj, hx⟩
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hxV
    have hsm : i ⁻¹ᵁ W ≤ L.U j := fun y hy ↦ by
      show y ∈ (L.U j : Set X₀)
      rw [← hVe]
      exact (hWle hy).1
    exact ⟨Opposite.op ⟨(⟨W, hW⟩, j), hsm⟩, hxW, fun y hy ↦ (hWle hy).2⟩
  refine ⟨cov, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  obtain ⟨t₃, hx₃, hle⟩ := cov x (U ⊓ ((smallG i L).obj t₁).unop.1 ⊓ ((smallG i L).obj t₂).unop.1)
    ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨t₃, ⟨(homOfLE (show t₃.unop ≤ t₁.unop from fun y hy ↦ (hle hy).1.2)).op⟩,
    ⟨(homOfLE (show t₃.unop ≤ t₂.unop from fun y hy ↦ (hle hy).2)).op⟩, hx₃, fun y hy ↦ (hle hy).1.1⟩

theorem exists_isLift (hi : IsThick I s i) : ∃ u, IsLift s i L u :=
  ⟨fun p q a ↦ (hi.app_surj q.unop.1.1 (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val).choose,
    fun p q a ↦ (hi.app_surj q.unop.1.1 _).choose_spec⟩

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift
variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} {L : LB X₀}

theorem isUnit_of_sqZero {A A₀ : Type} [CommRing A] [CommRing A₀] (p : A →+* A₀)
    (hp : Function.Surjective p) (K : Ideal A) (hK : K ^ 2 = ⊥) (hker : ∀ a, p a = 0 → a ∈ K)
    (x : A) (hx : IsUnit (p x)) : IsUnit x := by
  obtain ⟨v, hv⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := hp v
  have hn : x * y - 1 ∈ K := hker _ (by simp [hv])
  have hsq : (x * y - 1) * (x * y - 1) = 0 := by
    have : (x * y - 1) * (x * y - 1) ∈ K ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hn hn
    rw [hK] at this; simpa using this
  have hnil : IsNilpotent (x * y - 1) := ⟨2, by rw [pow_two, hsq]⟩
  have : IsUnit (x * y) := by simpa using hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left this

theorem lift_isUnit (hI : I ^ 2 = ⊥) (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (p q : (Small i L)ᵒᵖ) (a : p ⟶ q) : IsUnit (u p q a) := by
  have hK : ∀ (A : Type) [CommRing A] [Algebra R A], (I.map (algebraMap R A)) ^ 2 = ⊥ := fun A _ _ ↦ by
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  exact isUnit_of_sqZero (A := Γ(X, q.unop.1.1.1)) (i.app q.unop.1.1.1).hom (hi.app_surj q.unop.1.1)
    (I.map (algebraMap R (Sec s q.unop.1.1.1))) (hK (Sec s q.unop.1.1.1)) (fun b hb ↦ (hi.ker q.unop.1.1 b).1 hb) (u p q a)
    ((hu p q a).symm ▸ Units.isUnit _)

theorem lift_mdef (hi : IsThick I s i) (hL : L.IsLB) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u) :
    In2 I _ (mdef _ u) := by
  intro t t' t'' a b
  refine (hi.ker t''.unop.1.1 _).1 ?_
  have hb : t''.unop.1.1.1 ≤ t'.unop.1.1.1 := leOfHom b.unop
  have h2 : i ⁻¹ᵁ t''.unop.1.1.1 ≤ L.U t.unop.1.2 ⊓ L.U t'.unop.1.2 ⊓ L.U t''.unop.1.2 :=
    le_inf ((i.preimage_mono hb).trans (Small.le_inf a)) t''.unop.2
  have hc := congrArg (fun w ↦ (X₀.presheaf.map (homOfLE h2).op).hom w.val)
    (hL.cocycle t.unop.1.2 t'.unop.1.2 t''.unop.1.2)
  simp only [Units.val_mul, map_mul, res, Units.coe_map, MonoidHom.coe_coe,
    presheaf_map_map] at hc
  have k : ∀ (x : Γ(X, t'.unop.1.1.1)) (y z : Γ(X, t''.unop.1.1.1)),
      (i.app t'.unop.1.1.1).hom x = (res (Small.le_inf a) (L.g t.unop.1.2 t'.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom y = (res (Small.le_inf b) (L.g t'.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom z = (res (Small.le_inf (a ≫ b)) (L.g t.unop.1.2 t''.unop.1.2)).val →
      (i.app t''.unop.1.1.1).hom ((X.presheaf.map (homOfLE hb).op).hom x * y - z) = 0 := by
    intro x y z hx hy hz
    rw [map_sub, map_mul, app_presheaf_map, hx, hy, hz, sub_eq_zero]
    simp only [res, Units.coe_map, MonoidHom.coe_coe, presheaf_map_map]
    exact hc
  exact k _ _ _ (hu t t' a) (hu t' t'' b) (hu t t'' (a ≫ b))

theorem isLiftOfTransitionUnits_of_ideal_cochain_change (hi : IsThick I s i) {u : C1 (smallG i L ⋙ OAff s)} (hu : IsLift s i L u)
    (u' : C1 (smallG i L ⋙ OAff s)) (h : In1 I _ (u' - u)) : IsLift s i L u' := by
  intro p q a
  have h0 := (hi.ker q.unop.1.1 _).2 (h p q a)
  have e : u' p q a = u p q a + (u' - u) p q a := by simp
  rw [e]
  exact (map_add (i.app q.unop.1.1.1).hom (u p q a) ((u' - u) p q a)).trans
    ((congrArg₂ (· + ·) (hu p q a) h0).trans (add_zero _))

end GlobalTheory.LBLift

namespace GlobalTheory.LBLift

theorem small_basis_lift : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀), IsThick I s i → L.IsLB → IsBasis (smallG i L) ∧ (∃ u, IsLift s i L u) ∧ ∀ u, IsLift s i L u → (∀ t t' a, IsUnit (u t t' a)) ∧ In2 I _ (mdef _ u) ∧ ∀ u', In1 I _ (u' - u) → IsLift s i L u' := by
  intro R _ I hI X X₀ s i L hi hL
  exact ⟨isBasis_smallG hi hL, exists_isLift hi, fun u hu ↦
    ⟨lift_isUnit hI hi hu, lift_mdef hi hL hu, fun u' h ↦ isLiftOfTransitionUnits_of_ideal_cochain_change hi hu u' h⟩⟩

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOp
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smoothAffineCurve_degreeTwo_class_dies_on_principalOpen : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
    ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧
      pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq i x
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · have hSH : SH B := GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB
    haveI : Subsingleton (Ht q (sp B) 2 i) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B hSH (tw q i) 2 (by norm_num)
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Subsingleton.elim x 0, map_zero]
  · obtain ⟨inst, halg⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    letI := inst
    haveI := halg
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    haveI : Subsingleton (Ht q (sp (FractionRing B)) 2 i) :=
      GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK 2 i le_rfl
    obtain ⟨f, hf, -, hx⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB 2 i x (Subsingleton.elim _ _)
    exact ⟨f, hf, hx⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesCardAndResidueLe
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem typePlaces_card_and_residue_le : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → R.Pg.card = 2 * D.R.f ∧ ∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h
  obtain ⟨_, plg, iso, -⟩ := h
  refine ⟨?_, fun PP hPP => ?_⟩
  · rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Nat.card_congr plg, Nat.card_sigma]
    have hk : ∀ k : Fin 2, Nat.card (D.nd.PlG k) = D.R.f := fun k => by
      rw [← D.nd.card_PlG k]
      exact @Nat.card_eq_fintype_card _ (_)
    simp only [hk, Fin.sum_univ_two, two_mul]
  · obtain ⟨kv, hkv⟩ := plg.surjective ⟨PP, hPP⟩
    have h1 : Nat.card (kP (plg kv).1) = D.host.g kv.1 := by
      rw [← Nat.card_congr (iso kv).toEquiv, Nat.card_zmod]
    rw [hkv] at h1
    change _ ≤ Nat.card (kP (⟨PP, hPP⟩ : R.Pg).1)
    rw [h1]
    generalize kv.1 = k
    fin_cases k
    · exact min_le_left _ _
    · exact min_le_right _ _

end GlobalTheory
end

