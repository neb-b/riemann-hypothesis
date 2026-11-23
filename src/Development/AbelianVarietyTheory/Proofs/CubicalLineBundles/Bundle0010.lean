module

public import Mathlib
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetDvdEquivariantFramePolynomial
section
set_option autoImplicit false

open MvPolynomial Formalism.L2.LamCM

namespace GlobalTheory.FrameDet

open GlobalTheory.BorelAlg

theorem exists_lower {K : Type} [Field K] {n : ℕ} (x y : Matrix (Fin n) (Fin n) K) (l : Fin n) (hl : ∀ i, i ≤ l)
    (hx : x.det ≠ 0) (h : ∀ i, i ≠ l → y i = x i) :
    ∃ b : Matrix (Fin n) (Fin n) K, y = b * x ∧ (∀ i j, i < j → b i j = 0) ∧ (∀ i, i ≠ l → b i i = 1) ∧
      b.det = b l l := by
  have hrow : ∀ i, i ≠ l → ∀ j, (y * x⁻¹) i j = (1 : Matrix _ _ K) i j := by
    intro i hi j
    rw [← Matrix.mul_nonsing_inv _ hx.isUnit]
    simp only [Matrix.mul_apply, h i hi]
  have hb : ∀ i j, i < j → (y * x⁻¹) i j = 0 := fun i j hij => by
    rw [hrow i (hij.trans_le (hl j)).ne, Matrix.one_apply_ne hij.ne]
  refine ⟨y * x⁻¹, ?_, hb, fun i hi => by rw [hrow i hi, Matrix.one_apply_eq], ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hx.isUnit, Matrix.mul_one]
  · rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hb i j hij), Finset.prod_eq_single l]
    · intro i _ hi; rw [hrow i hi, Matrix.one_apply_eq]
    · simp

theorem det_dvd_of_equivariant : ∀ (K : Type) [Field K] [Infinite K] (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ), (∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) K), (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id → evalFr P (Function.update X b (X b * t)) = (∏ i, t i i ^ (a b i)) * evalFr P X) → ∀ b : B, (∀ i, 1 ≤ a b i) → ∃ Q : MvPolynomial (FrVar m) K, P = (Matrix.of fun i k : Fin (m b) => (MvPolynomial.X ⟨b, (k, i)⟩ : MvPolynomial (FrVar m) K)).det * Q := by
  intro K _ _ B _ _ m P a hP τ₀ ha
  have hT : (Matrix.of fun i k : Fin (m τ₀) => (MvPolynomial.X ⟨τ₀, (k, i)⟩ : MvPolynomial (FrVar m) K)).det =
      (gen m K τ₀).det := by
    rw [← Matrix.det_transpose]; rfl
  rw [hT]
  change (gen m K τ₀).det ∣ P
  by_cases h0 : m τ₀ = 0
  · haveI : IsEmpty (Fin (m τ₀)) := by rw [h0]; infer_instance
    rw [Matrix.det_isEmpty]; exact one_dvd _
  let l : Fin (m τ₀) := ⟨m τ₀ - 1, by omega⟩
  have hl : ∀ i, i ≤ l := fun i => by
    have := i.2
    simp only [Fin.le_def, l]; omega
  obtain ⟨hM0, hrel⟩ := minor_isRelPrime' (R := K) _ (inj_block m τ₀) l hl
  change ((gen m K τ₀).updateRow l (Pi.single l 1)).det ≠ 0 at hM0
  change IsRelPrime ((gen m K τ₀).updateRow l (Pi.single l 1)).det (gen m K τ₀).det at hrel
  set M := (gen m K τ₀).updateRow l (Pi.single l 1) with hM
  let x₀ : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) K) :=
    Function.update (gen m K) τ₀ M
  let P₀ : MvPolynomial (Lt m) K := eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2) P
  let D : MvPolynomial (Lt m) K := (∏ τ, (gen m K τ).det) * M.det
  have hD : D ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => gen_det_ne_zero m K τ) hM0
  have k3 : P * M.det ^ a τ₀ l = (gen m K τ₀).det ^ a τ₀ l * P₀ := by
    apply mul_left_cancel₀ hD
    apply MvPolynomial.funext
    intro z
    by_cases hz : eval z D = 0
    · rw [map_mul, map_mul (eval z) D, hz, zero_mul, zero_mul]
    rw [map_mul, map_mul (eval z) D]
    congr 1
    let g : MvPolynomial (Lt m) K →+* K := eval z
    let x := fun τ => g.mapMatrix (x₀ τ)
    let y := fun τ => g.mapMatrix (gen m K τ)
    have hxd : ∀ τ, (x τ).det = g (x₀ τ).det := fun τ => (RingHom.map_det _ _).symm
    have hyd : ∀ τ, (y τ).det = g (gen m K τ).det := fun τ => (RingHom.map_det _ _).symm
    have hxM : (x τ₀).det = g M.det := by rw [hxd]; simp [x₀]
    have hz' : (∏ τ, g (gen m K τ).det) * g M.det ≠ 0 := by
      rw [← map_prod, ← map_mul]; exact hz
    have hy : ∀ τ, (y τ).det ≠ 0 := fun τ =>
      hyd τ ▸ Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hz') τ (Finset.mem_univ _)
    have hne : ∀ τ, τ ≠ τ₀ → y τ = x τ := fun τ h => by simp [x, y, x₀, h]
    have hx : ∀ τ, (x τ).det ≠ 0 := fun τ => by
      by_cases h : τ = τ₀
      · subst h; rw [hxM]; exact right_ne_zero_of_mul hz'
      · rw [← hne τ h]; exact hy τ
    have hl' : ∀ i, i ≠ l → y τ₀ i = x τ₀ i := fun i h => by
      ext j; simp [x, y, x₀, M, Matrix.updateRow_ne h]
    obtain ⟨b, hxy, hb, hb1, hdet⟩ := exists_lower (x τ₀) (y τ₀) l hl (hx τ₀) hl'
    have hs : (y τ₀).det = b l l * (x τ₀).det := by rw [← hdet, ← Matrix.det_mul, ← hxy]
    have key := hP (fun τ => (x τ).transpose) τ₀ b.transpose
      (fun τ => by rw [Matrix.det_transpose]; exact hx τ)
      (by rw [Matrix.det_transpose, hdet]; exact left_ne_zero_of_mul (hs ▸ hy τ₀))
      (fun i j hij => hb j i hij)
    have e0 : Function.update (fun τ => (x τ).transpose) τ₀ ((x τ₀).transpose * b.transpose) =
        fun τ => (y τ).transpose := by
      funext τ
      by_cases h : τ = τ₀
      · subst h; rw [Function.update_self, ← Matrix.transpose_mul, ← hxy]
      · rw [Function.update_of_ne h, hne τ h]
    have e1 : evalFr P (fun τ => (y τ).transpose) = g P := by
      unfold evalFr
      congr 2
      funext v
      simp [y, g, gen]
    have e2 : evalFr P (fun τ => (x τ).transpose) = g P₀ := by
      have : (eval (fun v : FrVar m => (x v.1).transpose v.2.2 v.2.1) : MvPolynomial (Lt m) K →+* K) =
          g.comp (eval₂Hom C (fun p : Lt m => x₀ p.1 p.2.1 p.2.2)) := by
        ext <;> simp [x, g]
      unfold evalFr
      rw [this]; rfl
    have hc : (∏ i, b.transpose i i ^ a τ₀ i) = b l l ^ a τ₀ l := by
      rw [Finset.prod_eq_single l]
      · rfl
      · intro i _ hi; rw [Matrix.transpose_apply, hb1 i hi, one_pow]
      · simp
    rw [e0, e1, e2, hc] at key
    change g _ = g _
    rw [map_mul, map_mul, map_pow, map_pow, ← hxM, ← hyd, key, hs]
    ring
  have hd : (gen m K τ₀).det ^ a τ₀ l ∣ P :=
    (hrel.symm.pow (m := a τ₀ l) (n := a τ₀ l)).dvd_of_dvd_mul_right ⟨_, k3⟩
  exact (dvd_pow_self _ (by have := ha l; omega)).trans hd

end GlobalTheory.FrameDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HomLinear

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}


omit [GrpObj A] [GrpObj A'] in
theorem valAt'_comp_left (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (f : A ⟶ A') (U : A'.left.Opens) (s : Γ(A'.left, U)) :
    valAt' (x ≫ f).left U s = valAt' x.left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
  (valAt'_comp x.left f.left U s).symm


omit [GrpObj A'] in
theorem isHolTo_ex_comp (u : HolUnif A L g) (f : A ⟶ A') :
    IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (u.ex z ≫ f).left) := by
  intro U s
  have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
    ext w
    simp
  have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
      fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) :=
    funext fun w => valAt'_comp_left _ f U s
  rw [hset, hfun]
  exact u.hol _ _

theorem isTangent_comp {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f]
    {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem top_le_ex_zero (u : HolUnif A L g) {v : epsR ℂ ⟶ A} (hv : IsTangent v) (U : A.left.Opens)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
  have h0 : u.ex 0 = η[A] := by
    rw [(u.ker 0).mpr u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  rw [h0, ← hv]
  intro a _
  exact h (Set.mem_univ _)

theorem isDiff_comp (u : HolUnif A L g) (u' : HolUnif A' L' g') (f : A ⟶ A') [IsMonHom f]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z ≫ f) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A}
    (hv : IsTangent v) (hd : u.IsDiff w v) : u'.IsDiff (F w) (v ≫ f) := by
  intro U h s
  have h1 := hd (f.left ⁻¹ᵁ U) h ((f.left.app U).hom s)
  have e : ((v ≫ f).left.appLE U ⊤ h).hom s =
      (v.left.appLE (f.left ⁻¹ᵁ U) ⊤ h).hom ((f.left.app U).hom s) := by
    have := Scheme.Hom.comp_appLE v.left f.left U ⊤ h
    exact congrArg (fun φ => φ.hom s) this
  have hdiff : DifferentiableAt ℂ (fun z => valAt' (u'.ex z).left U s) 0 :=
    (u'.hol U s).2.differentiableAt ((u'.hol U s).1.mem_nhds (top_le_ex_zero u' (isTangent_comp f hv) U h))
  have hfun : (fun z => valAt' (u.ex z).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s)) =
      (fun z => valAt' (u'.ex z).left U s) ∘ LinearMap.toContinuousLinearMap F := by
    funext z
    rw [← valAt'_comp_left, ← hF]
    rfl
  have hch := (HasFDerivAt.comp (0 : Fin g → ℂ) (f := LinearMap.toContinuousLinearMap F)
    (by rw [map_zero]; exact hdiff.hasFDerivAt) (LinearMap.toContinuousLinearMap F).hasFDerivAt).fderiv
  rw [hfun, hch] at h1
  rw [e]
  exact h1

theorem exists_linear_of_isMonHom :
    ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' →
  ∀ (L : LB A.left) (L' : LB A'.left) (g g' : ℕ) (u : HolUnif A L g) (u' : HolUnif A' L' g'),
  (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) →
  ∀ f : A ⟶ A', IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ z, u'.ex (F z) = u.ex z ≫ f) ∧
    (∀ l ∈ u.Λ, F l ∈ u'.Λ) ∧ (∀ w v, IsTangent v → u.IsDiff w v → IsTangent (v ≫ f) ∧ u'.IsDiff (F w) (v ≫ f)) ∧
    ∀ f' : A ⟶ A', (∀ z, u'.ex (F z) = u.ex z ≫ f') → f' = f := by
  intro A A' _ _ hA hA' L L' g g' u u' h1 h2 f hf
  obtain ⟨F, hF, -⟩ := _root_.GlobalTheory.existsUnique_linear_lift_of_isHolTo A' hA' L' g' g u' h1 h2 (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) (isHolTo_ex_comp u f)
  refine ⟨F, hF, fun l hl => ?_, fun w v hv hd => ⟨isTangent_comp f hv, isDiff_comp u u' f F hF hv hd⟩,
    fun f' hf' => ?_⟩
  · rw [← u'.ker, hF, (u.ker l).mpr hl]
    exact MonObj.one_comp f
  · have hs : Smooth A.hom := hA.smooth
    have hp : IsProper A'.hom := hA'.proper
    have hr : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hs
    refine ComplexPoints.over_hom_ext_of_complexPoints fun x => ?_
    obtain ⟨z, rfl⟩ := u.ex_onto x
    rw [← hf', hF]

end GlobalTheory.HomLinear
end

