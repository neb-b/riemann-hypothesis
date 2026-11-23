module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOrEqNegOfPurelyImaginaryOfNormEq
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem eq_or_eq_neg_of_purelyImaginary_of_norm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ ξ' : E) (τ : E →+* ℂ),
      cc ξ = -ξ → cc ξ' = -ξ' → ‖τ ξ‖ = ‖τ ξ'‖ → ξ' = ξ ∨ ξ' = -ξ := by
  intro E _ _ _ ξ ξ' τ h h' hn
  have key : ∀ x : E, cc x = -x → τ (x ^ 2) = -((‖τ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    have h1 : τ (cc x) = (starRingEnd ℂ) (τ x) := IsCMField.complexEmbedding_complexConj E τ x
    rw [hx, map_neg] at h1
    have h2 := Complex.mul_conj' (τ x)
    rw [← h1] at h2
    rw [map_pow]
    push_cast
    linear_combination -h2
  have h3 : τ (ξ' ^ 2) = τ (ξ ^ 2) := by rw [key ξ h, key ξ' h', hn]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (τ.injective h3)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosNatMemFractionalIdeal
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem exists_pos_nat_mem_fractionalIdeal {E : Type} [Field E] [NumberField E]
    {a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (ha : a ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (n : E) ∈ a := by
  obtain ⟨x, hx0, hx⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger ha
  have hI : (Ideal.span {x} : Ideal (𝓞 E)) ≠ ⊥ := by simpa using hx0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {x}))
  refine ⟨Ideal.absNorm (Ideal.span {x}),
    Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
  have h := (a : Submodule (𝓞 E) E).smul_mem e hx
  rw [Algebra.smul_def, ← map_mul, he, map_natCast] at h
  exact h

theorem fractionalIdeal_smul_eq_span {E : Type} [Field E] [NumberField E] {r : ℕ}
    (a : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (L : Submodule (𝓞 E) (Fin r → E)) :
    (a : Submodule (𝓞 E) E) • L =
      Submodule.span (𝓞 E) {v | ∃ α ∈ a, ∃ u ∈ L, v = α • u} := by
  refine le_antisymm (Submodule.smul_le.2 fun α hα u hu => Submodule.subset_span ⟨α, hα, u, hu, rfl⟩)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨α, hα, u, hu, rfl⟩
  exact Submodule.smul_mem_smul hα hu

theorem exists_dataX_of_perfect_traceForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔄 𝔄b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (k : ℝ) (g : ℕ), (∀ a : E, a ∈ 𝔄b ↔ cc a ∈ 𝔄) → FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 * 𝔄 * 𝔄b * (differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 1 → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = k) → k ≤ 1 → (∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ n : ℤ, EFf X.ξ0 X.Gm x y = n) → (∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y) → 0 < g → (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ) → ∃ Xx : DataX E r, Xx.toData = X ∧ Xx.g = g ∧ Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro E _ _ _ r X 𝔄 𝔄b k g hb hone habs hk hint hperf hg hcong
  have hbc : 𝔄b = conjFrac 𝔄 := by
    ext a; rw [mem_conjFrac]; exact hb a
  subst hbc
  have hA : 𝔄 ≠ 0 := by
    rintro rfl
    simp at hone
  have hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hd := (perfect_iff_hermDual_eq X.ξ0_ne X.Gm_det hΛ).1 ⟨hint, hperf⟩
  have hself : hermDual X.Gm (((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) • X.Λ) =
      ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ := by
    rw [hermDual_smul (inv_ne_zero hA), conjFrac_inv, inv_inv, hd, ← fractionalIdeal_mul_smul]
    congr 2
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hone]; ring
  obtain ⟨hi, hdual⟩ := hermDual_eq_self_iff.1 hself
  obtain ⟨NA, hNA, hNA'⟩ := exists_pos_nat_mem_fractionalIdeal (inv_ne_zero hA)
  obtain ⟨NC, hNC, hNC'⟩ := exists_pos_nat_mem_fractionalIdeal hA
  have hk0 : 0 < k := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← habs τ, norm_pos_iff]
    exact (map_ne_zero τ).2 X.ξ0_ne
  refine ⟨{ toData := X
            k0 := 2 * k
            minWeight_pos := by positivity
            k0_le := by linarith
            ξ0_abs := fun τ => by rw [habs]; ring
            EF_int := hint
            EF_perf := hperf
            L' := ((𝔄⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) • X.Λ
            L'_fg := (isLattice_fractionalIdeal_smul (inv_ne_zero hA) hΛ).1
            L'_int := hi
            L'_dual := hdual
            NA := NA
            NC := NC
            NA_pos := hNA
            NC_pos := hNC
            NA_sub := fun x hx => Submodule.smul_mem_smul hNA' hx
            NC_sub := fun x hx => ?_
            g := g
            g_pos := hg
            cong := hcong }, rfl, rfl, ?_⟩
  · have h := Submodule.smul_mem_smul (show (NC : E) ∈ (𝔄 : Submodule (𝓞 E) E) from hNC') hx
    rwa [fractionalIdeal_smul_inv_smul hA] at h
  · change X.Λ = _
    rw [← fractionalIdeal_smul_eq_span, fractionalIdeal_smul_inv_smul hA]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RootOfUnityEqOneOfConjCongruence
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem isIntegral_eigenvalue_sub_one_div {E : Type} [Field E] [NumberField E] {r M : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ)
    (hM : (M : ℂ) ≠ 0) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hγ : ∀ x ∈ Λ, ∃ y ∈ Λ, γ *ᵥ x - x = (M : E) • y)
    (w : Fin r → ℂ) (hw : w ≠ 0) (l : ℂ) (hl : w ᵥ* γ.map τ = l • w) :
    IsIntegral ℤ ((l - 1) / M) := by
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun x => w ⬝ᵥ (τ ∘ x)
      map_zero' := by simp [dotProduct]
      map_add' := fun x y => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ x, φ x = w ⬝ᵥ (τ ∘ x) := fun _ => rfl
  have hsm : ∀ (c : E) x, φ (c • x) = τ c * φ x := by
    intro c x
    simp only [hφ, dotProduct, Finset.mul_sum, Function.comp, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmul : ∀ x, φ (γ *ᵥ x) = l * φ x := by
    intro x
    have : τ ∘ (γ *ᵥ x) = γ.map τ *ᵥ (τ ∘ x) := funext fun i => RingHom.map_mulVec τ γ x i
    rw [hφ, this, Matrix.dotProduct_mulVec, hl, smul_dotProduct, hφ, smul_eq_mul]
  refine isIntegral_of_smul_mem_submodule
    ((Λ.restrictScalars ℤ).map φ.toIntLinearMap) ?_ (hfg.restrictScalars.map _) _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := by
      intro x hx
      have : φ.toIntLinearMap x ∈ (Λ.restrictScalars ℤ).map φ.toIntLinearMap :=
        Submodule.mem_map_of_mem hx
      rw [h0] at this
      simpa using this
    have h2 : ∀ x ∈ Submodule.span E (Λ : Set (Fin r → E)), φ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul c x _ hx => rw [hsm, hx, mul_zero]
    apply hw
    funext i
    have h3 := h2 (Pi.single i 1) (hsp ▸ Submodule.mem_top)
    have h4 : τ ∘ (Pi.single i 1 : Fin r → E) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hφ, h4] at h3
    simpa using h3
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hγ x hx
    refine ⟨y, hy, ?_⟩
    have h := congrArg φ hxy
    rw [map_sub, hmul, hsm, map_natCast] at h
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
    field_simp
    linear_combination -h

theorem root_of_unity_eq_one_of_isIntegral_div {E : Type} [Field E] [NumberField E] {M n : ℕ}
    (hM : 3 ≤ M) (hn : 0 < n) {u : E} (hu : u ^ n = 1) (h : IsIntegral ℤ ((u - 1) / M)) :
    u = 1 := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hlt : ∀ φ : E →+* ℂ, ‖φ ((u - 1) / M)‖ < 1 := by
    intro φ
    have h1 : ‖φ u‖ = 1 := by
      have : ‖φ u‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h2 : ‖φ u - 1‖ ≤ 2 := by
      have := norm_sub_le (φ u) 1
      rw [h1, norm_one] at this
      linarith
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    linarith
  by_contra hne
  have hx : (u - 1) / M ≠ 0 := div_ne_zero (sub_ne_zero.2 hne) hM0
  obtain ⟨k, hk, hk1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx h
    fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : ‖φ ((u - 1) / M)‖ ^ k = 1 := by rw [← norm_pow, ← map_pow, hk1, map_one, norm_one]
  exact (hlt φ).ne ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3)

theorem root_of_unity_eq_one_of_conj_congruence :
    ∀ (E : Type) [Field E] [NumberField E] (r M n : ℕ) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (γ δ : Matrix (Fin r) (Fin r) E) (u : E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), 0 < r → 3 ≤ M → 0 < n → u ^ n = 1 → Λ.FG → Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → (∀ x ∈ Λ', ∃ y ∈ Λ', Matrix.mulVec (δ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → Q.det ≠ 0 → (u • γ).map τ * Q = Q * δ.map τ → u = 1 := by
  intro E _ _ r M n Λ Λ' γ δ u τ Q hr hM hn hu hfg hfg' hsp hsp' hγ hδ hQ hconj
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (γ.map τ)ᵀ)
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hw1 : w ᵥ* γ.map τ = l • w := by
    have := hw.apply_eq_smul
    rwa [Matrix.toLin'_apply, Matrix.mulVec_transpose] at this
  have hwQ : w ᵥ* Q ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_vecMul_eq_zero hQ h)
  have hs : (u • γ).map τ = τ u • γ.map τ := by
    ext i j; simp
  have hw2 : (w ᵥ* Q) ᵥ* δ.map τ = (τ u * l) • (w ᵥ* Q) := by
    rw [Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul, hs, Matrix.vecMul_smul, hw1,
      smul_smul, Matrix.smul_vecMul]
  have ha := isIntegral_eigenvalue_sub_one_div Λ γ τ hM0 hfg hsp hγ w hw0 l hw1
  have hb := isIntegral_eigenvalue_sub_one_div Λ' δ τ hM0 hfg' hsp' hδ _ hwQ _ hw2
  have hui : IsIntegral ℤ (τ u) := by
    apply IsIntegral.of_pow hn
    rw [← map_pow, hu, map_one]
    exact isIntegral_one
  have hc : τ ((u - 1) / M) = (τ u * l - 1) / M - τ u * ((l - 1) / M) := by
    rw [map_div₀, map_sub, map_one, map_natCast]
    field_simp
    ring
  refine root_of_unity_eq_one_of_isIntegral_div hM hn hu ?_
  refine (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 ?_
  change IsIntegral ℤ (τ ((u - 1) / M))
  rw [hc]
  exact hb.sub (hui.mul ha)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SymmetricLineBundleOfRegularSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SymOfZeroDivisor

theorem appLE_mem_nonZeroDivisors {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (V : X.Opens) (h : V ≤ W), resG X h a ∈ nonZeroDivisors Γ(X, V))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) : (f.appLE W V h).hom a ∈ nonZeroDivisors Γ(Y, V) := by
  have h' : f ''ᵁ V ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact h hy
  have e : (f.appLE W V h).hom a = (f.appIso V).hom.hom (resG X h' a) := by
    rw [Scheme.Hom.appIso_hom']
    change _ = (X.presheaf.map (homOfLE h').op ≫ f.appLE _ _ _).hom a
    rw [Scheme.Hom.map_appLE]
  rw [e]
  rw [← MulEquivClass.map_nonZeroDivisors (f.appIso V).commRingCatIsoToRingEquiv]
  exact Submonoid.mem_map_of_mem _ (ha _ h')

theorem inv_eq_zero_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Scheme.{0}} (t : T ⟶ A.left) :
    t ≫ (GrpObj.inv : A ⟶ A).left = (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A ↔
      t = t ≫ A.hom ≫ eSec A := by
  have h1 : (GrpObj.inv : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  have h2 : eSec A ≫ (GrpObj.inv : A ⟶ A).left = eSec A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have h3 : (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A =
      (t ≫ A.hom ≫ eSec A) ≫ (GrpObj.inv : A ⟶ A).left := by
    rw [Category.assoc, reassoc_of% h1]
    simp only [Category.assoc]
    exact congrArg (fun u => t ≫ A.hom ≫ u) h2.symm
  rw [h3]
  exact cancel_mono _

theorem sym_of_regular_section : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (θ : L.Sec), L.IsLB → (∀ (i : L.ι) (V : Scheme.Opens A.left) (h : V ≤ L.U i), resG A.left h (θ.f i) ∈ nonZeroDivisors Γ(A.left, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ A.left) (i : L.ι) (h : ⊤ ≤ t ⁻¹ᵁ L.U i), (t.appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ t = t ≫ A.hom ≫ eSec A) → Out.Sym A L := by
  intro S A _ L θ hL hreg hz s
  refine ⟨⊤, trivial, ?_⟩
  haveI : IsIso (GrpObj.inv : A ⟶ A).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (GrpObj.inv : A ⟶ A)))
  refine GlobalTheory.T.isoLineBundle_of_regularPullbacks_sameZeroScheme A.left _ L θ _ _ hL
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [hz, hz, ← Category.assoc t]
  exact inv_eq_zero_iff A _

end GlobalTheory.SymOfZeroDivisor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceFormIntegralPerfectOfIsUnf
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem traceForm_integral_perfect_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ k, (∀ x ∈ (U.X k).Λ, ∀ y ∈ (U.X k).Λ, ∃ n : ℤ, EFf (U.X k).ξ0 (U.X k).Gm x y = n) ∧ ∀ φ : (U.X k).Λ →+ ℤ, ∃ x ∈ (U.X k).Λ, ∀ y : (U.X k).Λ, (φ y : ℚ) = EFf (U.X k).ξ0 (U.X k).Gm x y := by
  intro E _ _ _ H Dw l Xo c σ r U hU k
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hφ, -⟩ := hU
  refine ⟨fun x hx y hy => ?_, fun ψ => ?_⟩
  · refine ⟨(F.Di (ik k)).EF ((φ k).symm ⟨x, hx⟩) ((φ k).symm ⟨y, hy⟩), ?_⟩
    rw [hφ k]
    simp only [LinearEquiv.apply_symm_apply, EFf]
  · obtain ⟨a, ha⟩ := (F.Di (ik k)).unimod.2
      (ψ.comp (φ k).toLinearMap.toAddMonoidHom).toIntLinearMap
    refine ⟨φ k a, (φ k a).2, fun y => ?_⟩
    have h := hφ k a ((φ k).symm y)
    rw [ha] at h
    simpa [EFf] using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TraceMulConjIntIffMemOfMulDifferentEqOne
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing

namespace GlobalTheory

open NumberField in
open scoped Matrix in
private theorem fractionalIdeal_eq_one_of_smul_submodule_eq_self {E : Type} [Field E] [NumberField E]
    {r : ℕ} {c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hc : c ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} (hL : L ≠ ⊥) (hfg : L.FG)
    (h : (↑c : Submodule (𝓞 E) E) • L = L) : c = 1 := by
  have key : ∀ d : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      (↑d : Submodule (𝓞 E) E) • L = L → d ≤ 1 := by
    intro d hd a ha
    have hint : IsIntegral (𝓞 E) a :=
      isIntegral_of_smul_mem_submodule L hL hfg a fun n hn =>
        hd ▸ Submodule.smul_mem_smul ha hn
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact (FractionalIdeal.mem_one_iff _).2 ⟨y, rfl⟩
  have h1 : c ≤ 1 := key c h
  have h2 : c⁻¹ ≤ 1 := key c⁻¹ (by
    conv_rhs => rw [← _root_.GlobalTheory.fractionalIdeal_inv_smul_smul hc L]
    rw [h])
  refine le_antisymm h1 ?_
  calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = c * c⁻¹ := (mul_inv_cancel₀ hc).symm
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c


open NumberField in
open scoped Matrix in
theorem _root_.GlobalTheory.trace_xi_mul_conj_int_iff_mem :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 0 < r → 𝔄 ≠ 0 → X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u} → ∀ x : E, (∀ y ∈ 𝔄, ∃ n : ℤ, Algebra.trace ℚ E (X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y) = n) ↔ x ∈ 𝔄 := by
  intro E _ _ _ r X 𝔄 hr h𝔄 hΛ x
  haveI : NeZero r := ⟨hr.ne'⟩
  have hξ : X.ξ0 ≠ 0 := X.ξ0_ne
  have hlat : _root_.ReciprocityTheory.MultiplicativeHeights.IsLattice X.Λ := ⟨X.Λ_fg, X.Λ_span⟩
  have hself : _root_.GlobalTheory.traceFormDual X.ξ0 X.Gm X.Λ = X.Λ :=
    (_root_.GlobalTheory.perfect_iff_traceFormDual_eq hξ X.Gm_det hlat).1 ⟨X.EF_int, X.EF_perf⟩
  have hL : _root_.GlobalTheory.hermDual X.Gm X.L' = X.L' :=
    _root_.GlobalTheory.hermDual_eq_self_iff.2 ⟨X.L'_int, X.L'_dual⟩
  have hΛ' : X.Λ = (↑𝔄 : Submodule (𝓞 E) E) • X.L' := by
    rw [hΛ]
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro v ⟨a, ha, u, hu, rfl⟩
      exact Submodule.smul_mem_smul ha hu
    · exact Submodule.smul_le.2 fun a ha u hu => Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
  have hLne : X.L' ≠ ⊥ := by
    intro hbot
    have hspan := X.Λ_span
    rw [hΛ', hbot, Submodule.smul_bot, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    exact bot_ne_top hspan
  set 𝔇 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      ↑(differentIdeal ℤ (𝓞 E)) with h𝔇
  have hconj0 : _root_.GlobalTheory.conjFrac 𝔄 ≠ 0 := _root_.GlobalTheory.conjFrac_ne_zero h𝔄
  have hsp0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ
  have hd0 := _root_.GlobalTheory.coe_different_ne_zero (E := E)
  have h𝔇0 : 𝔇 ≠ 0 := mul_ne_zero hsp0 hd0
  have heq : (↑𝔄 : Submodule (𝓞 E) E) • X.L' =
      (↑(𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹) : Submodule (𝓞 E) E) • X.L' := by
    rw [← hΛ', ← hself, _root_.GlobalTheory.traceFormDual_eq hξ, hΛ',
      _root_.GlobalTheory.hermDual_smul h𝔄, hL, _root_.GlobalTheory.fractionalIdeal_mul_smul]
  have h𝔅 : 𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹ = 𝔄 := by
    have hc := fractionalIdeal_eq_one_of_smul_submodule_eq_self
      (c := 𝔄⁻¹ * (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹))
      (mul_ne_zero (inv_ne_zero h𝔄) (mul_ne_zero (inv_ne_zero h𝔇0) (inv_ne_zero hconj0)))
      hLne X.L'_fg (by
        rw [_root_.GlobalTheory.fractionalIdeal_mul_smul, ← heq,
          _root_.GlobalTheory.fractionalIdeal_inv_smul_smul h𝔄])
    calc _ = 𝔄 * (𝔄⁻¹ * (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹)) := by
          rw [← mul_assoc, mul_inv_cancel₀ h𝔄, one_mul]
      _ = 𝔄 := by rw [hc, mul_one]
  have hmain : 𝔄 * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      _root_.GlobalTheory.conjFrac 𝔄) = (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
    rw [show 𝔄 * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
        _root_.GlobalTheory.conjFrac 𝔄) = (𝔇⁻¹ * (_root_.GlobalTheory.conjFrac 𝔄)⁻¹) *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
        _root_.GlobalTheory.conjFrac 𝔄) by rw [h𝔅], h𝔇, mul_inv]
    calc _ = (↑(differentIdeal ℤ (𝓞 E)))⁻¹ *
          ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0)⁻¹ *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0) *
          ((_root_.GlobalTheory.conjFrac 𝔄)⁻¹ * _root_.GlobalTheory.conjFrac 𝔄) := by
          first | ring | simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = _ := by rw [inv_mul_cancel₀ hsp0, inv_mul_cancel₀ hconj0, mul_one, mul_one]
  have hcc : ∀ w : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc w) = w := by
    intro w
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    simp
  constructor
  · intro hx
    set K := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) X.ξ0 *
      _root_.GlobalTheory.conjFrac 𝔄 with hK
    have hK0 : K ≠ 0 := mul_ne_zero hsp0 hconj0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * K ≤
        (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
      rw [hK, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [_root_.GlobalTheory.mem_inv_different_iff]
      intro a ha
      have h1 : (z : E) * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        _root_.GlobalTheory.mem_one_fractionalIdeal_iff.2 ((RingOfIntegers.isIntegral_coe z).mul ha)
      have hw : (z : E) * a * j ∈ _root_.GlobalTheory.conjFrac 𝔄 := by
        have := FractionalIdeal.mul_mem_mul h1 hj
        rwa [one_mul] at this
      obtain ⟨n, hn⟩ := hx (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((z : E) * a * j)) (_root_.GlobalTheory.mem_conjFrac.1 hw)
      refine ⟨n, ?_⟩
      rw [← hn, hcc]
      congr 1
      change (z : E) * (x * X.ξ0) * j * a = _
      ring
    have hsub : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x ≤ 𝔄 := by
      calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x
          = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * K * K⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hK0, mul_one]
        _ ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ * K⁻¹ := by gcongr
        _ = 𝔄 := by rw [← hmain, mul_assoc, mul_inv_cancel₀ hK0, mul_one]
    exact FractionalIdeal.spanSingleton_le_iff_mem.1 hsub
  · intro hx y hy
    have hmem : X.ξ0 * x * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y ∈ (↑(differentIdeal ℤ (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ := by
      rw [← hmain]
      have := FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mul_mem_mul
        (FractionalIdeal.mem_spanSingleton_self _ X.ξ0)
        (_root_.GlobalTheory.cc_mem_conjFrac.2 hy))
      convert this using 1
      ring
    obtain ⟨k, hk⟩ := (_root_.GlobalTheory.mem_inv_different_iff.1 hmem) 1 isIntegral_one
    exact ⟨k, by simpa using hk⟩

end GlobalTheory
end

