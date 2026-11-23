module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivisibleHom

variable {S : Scheme.{0}}


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective {X Y Z : Over S} (e : X ⟶ Y) [Flat e.left]
    [Surjective e.left] {f g : Y ⟶ Z} (h : e ≫ f = e ≫ g) : f = g := by
  haveI := Flat.epi_of_flat_of_surjective e.left
  ext1
  rw [← cancel_epi e.left]
  simpa using congrArg CommaMorphism.left h


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.exists_lift_point {A A' T : Over S} (m : A' ⟶ A) [Flat m.left]
    [Surjective m.left] (y : T ⟶ A) :
    ∃ (T' : Over S) (e : T' ⟶ T) (x : T' ⟶ A'), Flat e.left ∧ Surjective e.left ∧
      x ≫ m = e ≫ y := by
  refine ⟨Over.mk (pullback.snd m.left y.left ≫ T.hom), Over.homMk (pullback.snd m.left y.left) rfl,
    Over.homMk (pullback.fst m.left y.left) ?_, ?_, ?_, ?_⟩
  · show pullback.fst m.left y.left ≫ A'.hom = pullback.snd m.left y.left ≫ T.hom
    rw [← Over.w m, ← Category.assoc, pullback.condition, Category.assoc, Over.w y]
  · show Flat (pullback.snd m.left y.left)
    infer_instance
  · show Surjective (pullback.snd m.left y.left)
    infer_instance
  · ext1
    simp [pullback.condition]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points {G H : Over S} [GrpObj G] [GrpObj H] (e : G ⟶ H)
    (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h
    simpa using h
  have hG : (η : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hH : (η : 𝟙_ (Over S) ⟶ H) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h := mul (G ⊗ G) (fst G G) (snd G G)
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.mul_def] at h
  have ht : lift (fst G G ≫ e) (snd G G ≫ e) = e ⊗ₘ e := by ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [hG, hH, hone]
  · rw [h, ht]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.comp_mulA {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) :
    x ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n = x ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [comp_pow, Category.comp_id]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.mulA_comp {A B : Over S} [GrpObj A] [GrpObj B] (u : A ⟶ B) [IsMonHom u]
    (n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n ≫ u = u ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [pow_comp, Category.id_comp]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.exists_factor {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] (M : ℕ)
    [QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (u : A ⟶ B) [IsMonHom u] (hu : ∀ (T : Over S) (x : T ⟶ A), x ^ M = 1 → x ≫ u = 1) :
    ∃ φ : A ⟶ B, _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ = u := by
  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left),
      g₁ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left = g₂ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left → g₁ ≫ u.left = g₂ ≫ u.left := by
    intro Z g₁ g₂ hg
    have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
      rw [← Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M), ← Category.assoc, ← hg, Category.assoc]
    let x₁ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₁ rfl
    let x₂ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₂ hw
    have hx : x₁ ^ M = x₂ ^ M := by
      rw [← _root_.GlobalTheory.DivisibleHom.comp_mulA, ← _root_.GlobalTheory.DivisibleHom.comp_mulA]
      ext1
      simpa [x₁, x₂] using hg
    have h1 : (x₁ * x₂⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hx, mul_inv_cancel]
    have h3 : IsMonHom.monoidHom u _ (x₁ * x₂⁻¹) = 1 := hu _ _ h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    simpa [x₁, x₂] using congrArg CommaMorphism.left h3
  refine ⟨Over.homMk (EffectiveEpi.desc _ _ key) ?_, ?_⟩
  · rw [← cancel_epi (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left, ← Category.assoc, EffectiveEpi.fac, Over.w u,
      Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M)]
  · ext1
    simp [EffectiveEpi.fac]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    (M : ℕ) [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (φ : A ⟶ B) [IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ)] : IsMonHom φ := by
  have hmm : ∀ (T : Over S) (a b : T ⟶ A),
      (a * b) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M = (a ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) * (b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) := by
    intro T a b
    simp only [_root_.GlobalTheory.DivisibleHom.comp_mulA, mul_pow]
  apply _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points
  intro T x y
  obtain ⟨T₁, e₁, x', he₁, hs₁, hx'⟩ := _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) x
  haveI := he₁
  haveI := hs₁
  obtain ⟨T₂, e₂, y', he₂, hs₂, hy'⟩ :=
    _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) (e₁ ≫ y)
  haveI := he₂
  haveI := hs₂
  haveI : Flat (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  haveI : Surjective (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  have hxe : (e₂ ≫ e₁) ≫ x = (e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hx', Category.assoc]
  have hye : (e₂ ≫ e₁) ≫ y = y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hy']
  apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (e₂ ≫ e₁)
  calc (e₂ ≫ e₁) ≫ (x * y) ≫ φ = (((e₂ ≫ e₁) ≫ x) * ((e₂ ≫ e₁) ≫ y)) ≫ φ := by
        rw [← Category.assoc (e₂ ≫ e₁), comp_mul]
    _ = (((e₂ ≫ x') * y') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) ≫ φ := by rw [hxe, hye, hmm]
    _ = ((e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) * (y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) := by
        rw [Category.assoc, mul_comp]
    _ = (e₂ ≫ e₁) ≫ ((x ≫ φ) * (y ≫ φ)) := by
        rw [comp_mul, ← Category.assoc (e₂ ≫ e₁) x, ← Category.assoc (e₂ ≫ e₁) y, hxe, hye]
        simp only [Category.assoc]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧ Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
        Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
          (IsUnit (n : Γ(S, ⊤)) → Etale (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left)) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (B : Over S) [GrpObj B]
      [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u →
        (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) →
          (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1) := by
  intro H S _ P B _ _ M hM u hu hkill
  obtain ⟨hfin, hflat, hsurj, -⟩ := H S P M hM
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  haveI := hu
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.DivisibleHom.exists_factor M u hkill
  haveI : IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M ≫ φ) := by rw [hφ]; infer_instance
  haveI := _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor M φ
  refine ⟨⟨φ, inferInstance, ?_⟩, fun h => ?_⟩
  · rw [← hφ, _root_.GlobalTheory.DivisibleHom.mulA_comp]
  · apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M)
    rw [_root_.GlobalTheory.DivisibleHom.mulA_comp, h, comp_one]

end GlobalTheory.DivisibleHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mul_eq_smul_one_of_mulVec_injective {R K : Type} [CommRing R] [Field K]
    (g : R →+* K) {m l : Type} [Fintype m] [Fintype l] [DecidableEq l] (M : Matrix m l R)
    (hM : ∀ x : l → K, (M.map g).mulVec x = 0 → x = 0) :
    ∃ (r : R) (T : Matrix l m R), g r ≠ 0 ∧ T * M = r • (1 : Matrix l l R) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun i : m => (M.map g) i)
  have : Fintype κ := Fintype.ofInjective a ha
  have h1 : Fintype.card κ ≤ Fintype.card l := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have h2 : Fintype.card l ≤ Fintype.card κ := by
    have hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      apply hM
      funext i
      have hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)),
          y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact congrFun hx k
        | zero => simp
        | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
        | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
      exact key _ hi
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  let e : l ≃ κ := Fintype.equivOfCardEq (le_antisymm h2 h1)
  let N : Matrix l l R := M.submatrix (a ∘ e) id
  have hN : IsUnit (N.map g) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e e.injective
  refine ⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hN
    have : g N.det = (N.map g).det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hN.ne_zero
  · rw [Matrix.mul_assoc]
    have : (1 : Matrix m m R).submatrix (a ∘ e) id * M = N := by
      ext i j
      simp [N, Matrix.mul_apply, Matrix.one_apply]
    rw [this, Matrix.adjugate_mul]

theorem exists_kernel_certificate {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by
  classical
  obtain ⟨κ, s, hs, hspan, hli⟩ := exists_linearIndependent' K (fun j : a => (D₀.map g).col j)
  have : Fintype κ := Fintype.ofInjective s hs
  let S : Matrix a κ R := (1 : Matrix a a R).submatrix id s
  have hDS : D₀ * S = D₀.submatrix id s := by
    ext i j
    simp [S, Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x =
      ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k := by
    intro x
    funext i
    simp [hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨r₀, T₀, hr₀, hT₀⟩ := exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by
    intro x hx
    rw [hsum] at hx
    funext k
    exact Fintype.linearIndependent_iff.1 hli x hx k)
  obtain ⟨r₁, T₁, hr₁, hT₁⟩ := exists_mul_eq_smul_one_of_mulVec_injective g
    (Matrix.fromRows T₀ D₁) (by
    intro w hw
    have hw1 : (T₀.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inl k)
    have hw2 : (D₁.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inr k)
    obtain ⟨v, hv⟩ := hex w hw2
    have hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s)) := by
      rw [hspan, ← hv]
      have : (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [← hsum] at hu
    rw [← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀] at hw1
    have hu0 : u = 0 := by
      funext k
      have := congrFun hw1 k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this
      rcases this with h | h
      · exact absurd h hr₀
      · exact h
    rw [← hu, hu0, Matrix.mulVec_zero])
  let Q : Matrix a a R := r₀ • (1 : Matrix a a R) - S * T₀ * D₀
  have hQS : Q * S = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hDQ : r₁ • (D₀ * Q) = 0 := by
    have h1 : T₀ * (D₀ * Q) = 0 := by
      have : T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀) := by
        simp only [Matrix.mul_assoc]
      simp only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : D₁ * (D₀ * Q) = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    have h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0 := by
      rw [Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]
    calc r₁ • (D₀ * Q) = (T₁ * Matrix.fromRows T₀ D₁) * (D₀ * Q) := by
          rw [hT₁, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  let t := {j : a // j ∉ Set.range s}
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → a := fun i => (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfs : ∀ i k, f i ≠ s k := fun i k h => (e i).2 ⟨k, h.symm⟩
  let E : Matrix a (Fin (Fintype.card t)) R := (1 : Matrix a a R).submatrix id f
  have hEE : E.transpose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hES : E.transpose * S = 0 := by
    ext i j
    simp [E, S, Matrix.mul_apply, Matrix.one_apply, hfs]
  have hQE : Q * E * E.transpose = Q := by
    ext i j
    have hQE' : Q * E = Q.submatrix id f := by
      ext i j
      simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hQE']
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k, rfl⟩ := hj
      have : Q i (s k) = (Q * S) i k := by
        simp [S, Matrix.mul_apply, Matrix.one_apply]
      rw [this, hQS]
      simp [E, Matrix.mul_apply, Matrix.one_apply, hfs]
    · obtain ⟨k, hk⟩ : ∃ k, f k = j := ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
      subst hk
      simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  refine ⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hr₁ hr₀
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]
  · have : E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E) := by
      simp only [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul,
      sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]
    simp only [Q, sub_add_cancel]

theorem exists_matrix_basis_ker_of_exact_at_point :
    ∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v := by
  intro R K _ _ g₀ a b c D₀ D₁ h0 hex
  obtain ⟨r, n, B, C, H, hr, hB, hCB, hBC⟩ := exists_kernel_certificate g₀ D₀ D₁ h0 hex
  refine ⟨r, n, B, hr, hB, ?_⟩
  intro R' _ g hu v hv
  obtain ⟨u, hu⟩ := hu
  have hone : ∀ (m : ℕ) (x : Fin m → R'),
      ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x := by
    intro m x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]
  have h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]
  have h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v := by
    rw [hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      add_zero]
  refine ⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩
  · show (B.map g).mulVec _ = v
    rw [Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]
  · intro z hz
    rw [← hz, h1, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.HasEnoughRootsOfUnityGlobalSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_pairing_eq_character {H M : Type} [CommGroup H] [CommMonoid M] (N : ℕ)
    [NeZero N] [HasEnoughRootsOfUnity M N] [hfin : Finite {x : H // x ^ N = 1}]
    (W : H → H → Mˣ → Prop)
    (hex : ∀ x y : H, x ^ N = 1 → y ^ N = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hskew : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x : H, x ^ N = 1 → (∀ y : H, y ^ N = 1 → W x y 1) → x = 1)
    (χ : {x : H // x ^ N = 1} → Mˣ)
    (hχ : ∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) :
    ∃! b : H, b ^ N = 1 ∧ ∀ x : {x : H // x ^ N = 1}, W x.1 b (χ x) := by
  classical
  let G : Subgroup H := (powMonoidHom N : H →* H).ker
  have hG : ∀ x : G, (x : H) ^ N = 1 := fun x => x.2
  haveI : Finite G := hfin
  choose e he huniq using fun x y : G => hex x y (hG x) (hG y)
  have hel : ∀ x x' y : G, e (x * x') y = e x y * e x' y := fun x x' y =>
    (huniq _ _ _ (hmul _ _ _ _ _ (he x y) (he x' y))).symm
  have hes : ∀ x y : G, e y x = (e x y)⁻¹ := fun x y =>
    (huniq _ _ _ (hskew _ _ _ (he x y))).symm
  have her : ∀ x y y' : G, e x (y * y') = e x y * e x y' := fun x y y' => by
    rw [hes (y * y') x, hel, hes y x, hes y' x, mul_inv]
  let Φ : G →* (G →* Mˣ) := MonoidHom.mk' (fun b => MonoidHom.mk' (fun x => e x b)
    (fun x x' => hel x x' b)) (fun b b' => MonoidHom.ext fun x => her x b b')
  have hΦ : ∀ b x, Φ b x = e x b := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    refine Subtype.ext (hnd b (hG b) fun y hy => ?_)
    have h1 : e ⟨y, hy⟩ b = 1 := by rw [← hΦ, hb]; rfl
    have h2 := he b ⟨y, hy⟩
    rwa [hes, h1, inv_one] at h2
  haveI : HasEnoughRootsOfUnity M (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd M (n := N)
      (Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hG g))
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M
  haveI : Finite (G →* Mˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  let χ' : G →* Mˣ := MonoidHom.mk' (fun x => χ ⟨x.1, hG x⟩)
    (fun x y => hχ ⟨x.1, hG x⟩ ⟨y.1, hG y⟩)
  obtain ⟨b, hb⟩ := hbij.2 χ'
  refine ⟨b, ⟨hG b, fun x => ?_⟩, ?_⟩
  · have h1 : e ⟨x.1, x.2⟩ b = χ x := by rw [← hΦ, hb]; rfl
    rw [← h1]
    exact he ⟨x.1, x.2⟩ b
  · rintro b' ⟨hb', h⟩
    have : (⟨b', hb'⟩ : G) = b := by
      apply hinj
      rw [hb]
      ext1 x
      rw [hΦ]
      exact (huniq x ⟨b', hb'⟩ _ (h ⟨x.1, hG x⟩)).symm
    exact congrArg Subtype.val this

theorem finite_torsion_of_isFinite_mul (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ) [IsFinite (mulA P.A N).left] :
    Finite {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} := by
  haveI := P.isAb.proper
  let p := IsLocalRing.closedPoint K
  let o : P.A.left := (1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p
  have hfib := Scheme.Hom.finite_preimage_singleton (mulA P.A N).left o
  haveI := hfib.to_subtype
  refine Finite.of_injective (β := (mulA P.A N).left ⁻¹' {o}) (fun x => ⟨x.1.left p, ?_⟩) ?_
  · have h : x.1 ≫ mulA P.A N = 1 := by rw [mulA, MonObj.comp_pow, Category.comp_id, x.2]
    change (x.1 ≫ mulA P.A N).left p = o
    rw [h]
  · intro x y hxy
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact ext_of_apply_closedPoint_eq P.A.hom (Over.w x.1) (Over.w y.1) (congrArg Subtype.val hxy)

theorem hasEnoughRootsOfUnity_globalSections (K : Type) [Field K] [IsAlgClosed K] (N : ℕ)
    (hN : (N : K) ≠ 0) :
    HasEnoughRootsOfUnity Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) N := by
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  let e : K ≃+* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  exact MulEquiv.hasEnoughRootsOfUnity (e.toMulEquiv.restrictRootsOfUnity N)

theorem charPair_of_weil :
    WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → CharPairSt := by
  intro hW hskew hnd hM K _ _ P N hN χ hχ
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  haveI := (hM _ P N (NeZero.one_le)).1
  haveI := finite_torsion_of_isFinite_mul K P N
  haveI := hasEnoughRootsOfUnity_globalSections K N hN
  obtain ⟨hex, hmul, -, -⟩ := hW _ P N (baseOver (Spec (CommRingCat.of K)))
  exact existsUnique_pairing_eq_character N (fun x y c => WeilIs P.A P.L N x y c) hex hmul
    (hskew _ P N _).2.1 (hnd K P N hN) χ hχ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UnramExtLaw
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem unramExt_law : UnramExtSt := unramExt

end GlobalTheory
end

