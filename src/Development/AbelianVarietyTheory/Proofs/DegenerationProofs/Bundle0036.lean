module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLaws
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ z x y := by rw [h.s12, h.s01]

theorem cub_four (h : IsCub θ) (p q r s z : A) :
    θ (p * q) (r * s) z * θ p q z * θ r s z = θ (p * r) (q * s) z * θ p r z * θ q s z := by
  have a := h.coc (p * q) r s z
  have b := h.coc (p * r) q s z
  have c := h.coc q p r z
  rw [mul_right_comm p r q] at b
  rw [mul_comm q p, h.s01 q p, h.s01 q (p * r)] at c
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b c ⊢
  linear_combination (norm := abel) b - a + c

theorem cubN_mul_point (h : IsCub θ) (a : ℕ) (x y z : A) :
    cubN θ a 1 (x * y) z * θ x y z ^ a = cubN θ a 1 x z * cubN θ a 1 y z * θ (x ^ a) (y ^ a) z := by
  induction a with
  | zero => simp [cubN, h.face]
  | succ a ih =>
    have f := cub_four h (x ^ a) (y ^ a) x y z
    simp only [CubeBalance.cubN_succ, mul_pow, pow_succ]
    replace ih := congrArg Additive.ofMul ih
    replace f := congrArg Additive.ofMul f
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at ih f ⊢
    linear_combination (norm := abel) ih + f

theorem mulq_succ (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) :
    mulq θ σ (n + 1) x = mulq θ σ n x * (cubN θ n 1 x x / dbl θ σ x ^ n) := by
  rw [mulq, Finset.prod_range_succ, mulq]

theorem mulq_add (h : IsCub θ) (σ : A → U) (m n : ℕ) (x : A) :
    mulq θ σ (m + n) x * dbl θ σ x ^ (m * n) =
      mulq θ σ m x * mulq θ σ n x * (cubN θ m 1 x (x ^ n) * cubN θ n 1 x x ^ m) := by
  induction m with
  | zero => simp [mulq, cubN]
  | succ m ih =>
    have c := CubeBalance.cubN_add h m n x x
    rw [h.s12] at c
    rw [Nat.add_right_comm, mulq_succ, mulq_succ, CubeBalance.cubN_succ]
    replace ih := congrArg Additive.ofMul ih
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih c ⊢
    linear_combination (norm := module) ih + c

end Cube

namespace NumB
variable {O : Type} [CommRing O] (B : NumB O)

theorem θ_mul_inv_inv (x y : B.A) : B.θ (x * y) x⁻¹ y⁻¹ * B.θ x x⁻¹ y = B.θ y y⁻¹ x⁻¹ := by
  have a := B.cub.coc x y y⁻¹ x⁻¹
  rwa [mul_inv_cancel, B.cub.face₂, one_mul, B.cub.s12, B.cub.s12 x y] at a

theorem σ_mul_symm (x y : B.A) : B.σ (x * y) * B.θ (x * y) x⁻¹ y⁻¹ = B.σ x * B.σ y := by
  have a := B.θ_mul_inv_inv y x
  have b := B.σ_mul x y
  rw [mul_comm y x, B.cub.s12] at a
  rw [← a, ← mul_assoc] at b
  exact mul_right_cancel b

theorem dbl_mul (x y : B.A) :
    dbl B.θ B.σ (x * y) * (B.θ (x * y) x y * B.θ x x y * B.θ y x y) =
      dbl B.θ B.σ x * dbl B.θ B.σ y := by
  have c := B.cub.coc x y (x * y)⁻¹ (x * y)
  have d := B.cub.coc y y⁻¹ x⁻¹ (x * y)
  rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm, inv_mul_cancel_right], cub_rot B.cub x y] at c
  rw [mul_inv_cancel, B.cub.face, mul_comm y⁻¹, ← mul_inv, B.cub.s01 y⁻¹, cub_rot B.cub x⁻¹ y⁻¹] at d
  have a := B.cub.compat x x⁻¹ x y
  have b := B.cub.compat y y⁻¹ x y
  rw [mul_inv_cancel, B.cub.face, B.cub.s01 x⁻¹ x y] at a
  rw [mul_inv_cancel, B.cub.face, B.cub.s12 y⁻¹ x y, B.cub.s01 y⁻¹ y x] at b
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have a := E a; have b := E b; have c := E c; have d := E d; have s := E (B.σ_mul_symm x y)
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_one] at a b c d s ⊢
  linear_combination (norm := abel) c - d - a - b - s

theorem dbl_pow (a : ℕ) (x : B.A) :
    dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) =
      dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 := by
  induction a with
  | zero => simp [dbl, mulq, cubN, B.cub.face, B.σ_one]
  | succ a ih =>
    have d := B.dbl_mul (x ^ a) x
    rw [B.cub.s01 x (x ^ a), ← cub_rot B.cub (x ^ a) x] at d
    have n := B.cub.N_add a 1 x (x ^ a) x
    rw [B.cub.face, mul_one, one_mul, B.cub.s01 x (x ^ a)] at n
    rw [mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have n := E n
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d n ⊢
    linear_combination (norm := module) ih + d + n

theorem mulq_mul (a b : ℕ) (x : B.A) :
    mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) := by
  induction a with
  | zero => simp [mulq]
  | succ a ih =>
    have m := mulq_add B.cub B.σ (a * b) b x
    have c := CubeBalance.cubN_mul B.cub a b x (x ^ b)
    have d := B.dbl_pow b x
    rw [Nat.succ_mul, mulq_succ]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have m := E m; have c := E c; have d := E d
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih m c d ⊢
    linear_combination (norm := module) ih + m + c + a • d

theorem mulq_mul_point (a : ℕ) (x y : B.A) :
    mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y *
      (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) := by
  induction a with
  | zero => simp [mulq, cubN]
  | succ a ih =>
    have d := B.dbl_mul x y
    have f := cubN_mul_point B.cub a x y (x * y)
    have n₁ := B.cub.N_add a 1 x x y
    have n₂ := B.cub.N_add a 1 y x y
    have n₃ := B.cub.N_add a 1 x (y ^ a) y
    rw [B.cub.face, mul_one, one_mul] at n₁ n₂ n₃
    rw [cub_rot B.cub x y] at f
    rw [← cub_rot B.cub (y ^ a) y x] at n₃
    have c₁ := B.cub.compat (x ^ a) (y ^ a) x y
    have c₂ := B.cub.coc (x ^ a) (y ^ a) y x
    rw [B.cub.s12 (x ^ a * y ^ a), B.cub.s12 (x ^ a) (y ^ a * y)] at c₂
    rw [mulq_succ, mulq_succ, mulq_succ, CubeBalance.cubN_succ, CubeBalance.cubN_succ, pow_succ y]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have d := E d; have f := E f; have n₁ := E n₁; have n₂ := E n₂; have n₃ := E n₃
    have c₁ := E c₁; have c₂ := E c₂
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at ih d f n₁ n₂ n₃ c₁ c₂ ⊢
    linear_combination (norm := module) ih + f + n₁ + n₂ - n₃ - a • d - c₁ + c₂

theorem cubN_inv_inv (a : ℕ) (x : B.A) :
    cubN B.θ a 1 x⁻¹ x⁻¹ * B.θ x x⁻¹ x ^ a * (B.σ x * B.σ (x ^ a)) =
      cubN B.θ a 1 x x * B.θ x⁻¹ x x⁻¹ ^ a * B.σ (x ^ a * x) := by
  induction a with
  | zero => simp [cubN, B.σ_one]
  | succ a ih =>
    have s := B.σ_cub (x ^ a) x x
    have t := B.σ_cub x x x⁻¹
    have u := B.σ_inv x
    rw [inv_inv, mul_inv_cancel, mul_inv_cancel_right, B.σ_one, B.cub.s12 x⁻¹, B.cub.s12 x] at t
    rw [CubeBalance.cubN_succ, CubeBalance.cubN_succ, inv_pow, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have s := E s; have t := E t; have u := E u
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_one] at ih s t u ⊢
    linear_combination (norm := module) ih + s - t - u

theorem mulq_inv (a : ℕ) (x : B.A) :
    mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) := by
  induction a with
  | zero => simp [mulq, B.σ_one]
  | succ a ih =>
    have g := B.cubN_inv_inv a x
    have u := B.σ_inv x
    rw [mulq_succ, mulq_succ, pow_succ x]
    have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
    have ih := E ih; have g := E g; have u := E u
    apply Additive.ofMul.injective
    simp only [dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at ih g u ⊢
    linear_combination (norm := module) ih + g + a • u

end NumB

theorem mulq_laws : ∀ (O : Type) [CommRing O] (B : NumB O) (a b : ℕ) (x y : B.A), mulq B.θ B.σ (a * b) x = mulq B.θ B.σ a (x ^ b) * mulq B.θ B.σ b x ^ (a ^ 2) ∧ mulq B.θ B.σ a (x * y) = mulq B.θ B.σ a x * mulq B.θ B.σ a y * (cubN B.θ a 1 x (y ^ a) * cubN B.θ a 1 y x ^ a) ∧ dbl B.θ B.σ (x ^ a) * (cubN B.θ a 1 x (x ^ a) * cubN B.θ a 1 x x ^ a) = dbl B.θ B.σ x ^ (a ^ 2) * mulq B.θ B.σ a x ^ 2 ∧ mulq B.θ B.σ a x⁻¹ * B.σ x ^ (a ^ 2) = mulq B.θ B.σ a x * B.σ (x ^ a) :=
  fun _ _ B a b x y => ⟨B.mulq_mul a b x, B.mulq_mul_point a x y, B.dbl_pow a x, B.mulq_inv a x⟩

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosure
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGrpPullback_of_dominant {W S Z : Scheme.{0}} (j : W ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {H : Over S} [GrpObj H] [Flat H.hom] {G : Over Z} [GrpObj G]
    [IsSeparated G.hom] {y : S ⟶ Z} {f : H.left ⟶ G.left} (hf : IsPullback f H.hom G.hom y)
    (h : IsGrpPullback ((Over.pullback j).obj H) G (j ≫ y) (pullback.fst H.hom j ≫ f)) :
    IsGrpPullback H G y f := by
  let e : H ≅ (Over.pullback y).obj G :=
    Over.isoMk hf.isoPullback hf.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom y = f := hf.isoPullback_hom_fst
  have hs : IsSeparated ((Over.pullback y).obj G).hom := by
    change IsSeparated (pullback.snd G.hom y)
    infer_instance
  have h₁ : IsGrpPullback ((Over.pullback j).obj H) ((Over.pullback y).obj G) j
      (pullback.fst H.hom j ≫ e.hom.left) :=
    (isGrpPullback_pullback G y).cancel (h.congr rfl (by rw [Category.assoc, he]))
      (by rw [Category.assoc, Over.w]; exact pullback.condition)
  have h₂ : IsMonHom e.hom :=
    ExtUnique.isMonHom_of_isGrpPullback (isGrpPullback_pullback H j) h₁ (𝟙 _) e.hom
      (by rw [Over.id_left, Category.id_comp])
  exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G y)).congr (Category.id_comp _) he

theorem Core.nonempty_law : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  rintro C hsm hcart ⟨m, hm⟩ ⟨i, hi⟩
  have := C.proper
  have hsep : IsSeparated C.GG.hom := by
    change IsSeparated (C.G.ι ≫ C.P.hom)
    infer_instance
  have hsmooth : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have hne : Nonempty C.U.toScheme := C.ne.to_subtype
  have hpb : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
    have w : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by
      rw [← C.cart.w, Category.assoc]; rfl
    refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by rw [Category.assoc]; exact s.condition))
      (fun s => ?_) (fun s => C.cart.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
    · rw [← cancel_mono C.G.ι, Category.assoc]
      exact C.cart.lift_fst _ _ _
    · apply C.cart.hom_ext
      · rw [C.cart.lift_fst, ← h₁, Category.assoc]
      · rw [C.cart.lift_snd, h₂]
  let e : 𝟙_ (Over C.Z) ⟶ C.GG := Over.homMk C.e C.e_sec
  obtain ⟨grp, -, hη, -, comm, pull⟩ :=
    grpObj_of_dense_open C.Z C.U.toScheme C.U.ι C.GG C.A C.a hpb m i e hm hi C.e_zero
  refine ⟨{ smooth := hsm, zero := congrArg (fun z => z.left) hη, pull := pull, test := fun p _ y τ => ?_ }⟩
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing τ.V (FractionRing τ.V)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  exact isGrpPullback_of_dominant (Out.jK τ.V) (hcart p y τ) ((τ.φ_cart.comp pull).congr τ.yK_fac τ.φ_f)

end GlobalTheory.ZJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfSmoothThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothThickenings

theorem mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (I : Ideal V) (hI : I ≠ ⊤)
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V I e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW' : IsAffineOpen W := hW
  have hWle : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  set ψ := f.appLE ⊤ W hWle with hψ
  set φ : CommRingCat.of V ⟶ Γ(X, W) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ ψ with hφ
  let : Algebra V Γ(X, W) := φ.hom.toAlgebra
  have hjf : hW'.fromSpec ≫ f = Spec.map φ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW' hWle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, hφ, Spec.map_comp]
  have : Algebra.FiniteType V Γ(X, W) := by
    have h1 : ψ.hom.FiniteType := f.finiteType_appLE (isAffineOpen_top _) hW' hWle
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).2
    exact h1.comp h2
  set p := hW'.primeIdealOf ⟨x, hxW⟩
  have hpx : hW'.fromSpec p = x := hW'.fromSpec_primeIdealOf ⟨x, hxW⟩
  have hcomap : p.asIdeal.comap (algebraMap V Γ(X, W)) = IsLocalRing.maximalIdeal V := by
    have h3 : (Spec.map φ) p = IsLocalRing.closedPoint V := by
      rw [← hjf]
      exact (congrArg f hpx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h3
  have hsm : ∀ e : ℕ, Algebra.Smooth (V ⧸ I ^ (e + 1))
      (TensorProduct V (V ⧸ I ^ (e + 1)) Γ(X, W)) := by
    intro e
    have hg : thick V I e = Spec.map (CommRingCat.ofHom (algebraMap V (V ⧸ I ^ (e + 1)))) := by
      unfold thick
      rw [Ideal.Quotient.algebraMap_eq]
    have := h e
    have h3 : Smooth (pullback.snd (Spec.map φ) (thick V I e)) := by
      rw [← hjf, ← pullbackRightPullbackFstIso_inv_snd_snd f (thick V I e) hW'.fromSpec]
      have hA : IsOpenImmersion (pullback.snd hW'.fromSpec (pullback.fst f (thick V I e))) :=
        inferInstance
      exact MorphismProperty.comp_mem @Smooth _ _ inferInstance
        (MorphismProperty.comp_mem @Smooth _ _ inferInstance this)
    have h4 : Smooth ((pullbackSpecIso V Γ(X, W) (V ⧸ I ^ (e + 1))).inv ≫ pullback.snd _ _) := by
      have : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V Γ(X, W))))
          (Spec.map (CommRingCat.ofHom (algebraMap V (V ⧸ I ^ (e + 1)))))) := by
        rw [← hg]
        exact h3
      infer_instance
    rw [pullbackSpecIso_inv_snd] at h4
    have h5 := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp h4
    have h6 := RingHom.Smooth.propertyIsLocal.respectsIso.1 _
      (Algebra.TensorProduct.comm V Γ(X, W) (V ⧸ I ^ (e + 1))).toRingEquiv h5
    have heq : algebraMap (V ⧸ I ^ (e + 1)) (TensorProduct V (V ⧸ I ^ (e + 1)) Γ(X, W)) =
        (Algebra.TensorProduct.comm V Γ(X, W) (V ⧸ I ^ (e + 1))).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : (V ⧸ I ^ (e + 1)) →ₐ[V] _).toRingHom := by
      ext t
      simp
    rw [← RingHom.smooth_algebraMap, heq]
    exact h6
  have hq : Algebra.IsSmoothAt V p.asIdeal := _root_.GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow V I hI Γ(X, W) hsm p.asIdeal hcomap
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) W hW' hWle hxW]
  let : Algebra Γ(Spec (CommRingCat.of V), ⊤) Γ(X, W) := ψ.hom.toAlgebra
  show Algebra.FormallySmooth Γ(Spec (CommRingCat.of V), ⊤) (Localization.AtPrime p.asIdeal)
  rw [← RingHom.formallySmooth_algebraMap]
  rw [Algebra.IsSmoothAt, ← RingHom.formallySmooth_algebraMap] at hq
  have e2 := RingHom.FormallySmooth.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv hq
  convert e2 using 1
  ext a
  rw [RingHom.comp_apply,
    IsScalarTower.algebraMap_apply Γ(Spec (CommRingCat.of V), ⊤) Γ(X, W) (Localization.AtPrime p.asIdeal),
    IsScalarTower.algebraMap_apply V Γ(X, W) (Localization.AtPrime p.asIdeal)]
  congr 1
  show ψ a = φ ((Scheme.ΓSpecIso (CommRingCat.of V)).hom a)
  rw [hφ, CommRingCat.comp_apply, Iso.hom_inv_id_apply]

theorem smooth_of_smooth_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (B : Over (Spec (CommRingCat.of R))), IsProper B.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, Smooth (Y e).hom) → Smooth B.hom := by
  intro R _ _ _ I hI B _ Y b hpb hY
  have : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B.hom.smoothLocus := by
    by_contra! H
    exact hne (eq_top_iff.mpr fun z _ => H z)
  have hcl : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨z', hz', hz'c⟩ :=
    (IsLocalRing.specializes_closedPoint (B.hom z)).mem_closed hcl ⟨z, hz, rfl⟩
  apply hz'
  refine mem_smoothLocus I hI B.hom (fun e => ?_) z' hz'c
  rw [← (hpb e).isoPullback_inv_snd]
  have := hY e
  infer_instance

end GlobalTheory.SmoothThickenings
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_vt_QT_le (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) (χ : N.X) :
    ‖N.vt p.1.2 χ‖ ≤ Real.exp (-((q (p.1.1.toAdd + k • χ) - q p.1.1.toAdd) / (k : ℝ) ^ 2)) := by
  rw [NumD.vt]
  simp only [Units.val_mul, norm_mul, h.ψ, h.norm_rep_generators_eq_exp p hk]
  refine (mul_le_of_le_one_right (by positivity) (h.th _)).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  have e : q (p.1.1.toAdd + k • χ) =
      q p.1.1.toAdd + (k : ℝ) ^ 2 * q χ + k * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (k • χ) = k * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (k • χ) = (k : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [e]
  field_simp
  ring

theorem tendsto_vt_QT (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) :
    Filter.Tendsto (N.vt p.1.2) Filter.cofinite (nhds 0) := by
  have inj : Function.Injective fun χ : N.X => p.1.1.toAdd + k • χ := fun a b e => by
    have e' : k • a = k • b := add_left_cancel e
    rw [← natCast_zsmul, ← natCast_zsmul] at e'
    exact smul_right_injective N.X (Int.natCast_ne_zero.2 hk) e'
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have kp : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) 2
  have t₂ := (Filter.tendsto_atTop_add_const_right _ (-q p.1.1.toAdd) t₁).atTop_div_const kp
  have t₃ := Real.tendsto_exp_neg_atTop_nhds_zero.comp t₂
  refine squeeze_zero_norm (h.norm_vt_QT_le hk p) ?_
  simpa only [Function.comp_def, sub_eq_add_neg] using t₃

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem summable_vt_QT : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) :=
  fun _ _ _ _ _ _ h _ hk p =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (h.tendsto_vt_QT hk p)
end GlobalTheory.Ex
end

