module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_subfamily_unique_repr_of_spanning_localRing
    (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ) :
    Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M,
      (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) →
      ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  rintro ⟨b⟩ w hw
  haveI : Module.Finite R M := Module.Finite.of_basis b
  let V := IsLocalRing.ResidueField R ⊗[R] M
  let v : Fin g → V := fun a => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] w a
  have hsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c m =>
      obtain ⟨cf, rfl⟩ := hw m
      have : c ⊗ₜ[R] (∑ a, cf a • w a) = c • ∑ a, cf a • v a := by
        simp only [v, TensorProduct.tmul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', smul_comm c (cf a) (1 : IsLocalRing.ResidueField R),
          smul_eq_mul, _root_.mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField R) v
  let bk : Module.Basis κ (IsLocalRing.ResidueField R) V :=
    Module.Basis.mk hli (by rw [hspa, hsp])
  let bV : Module.Basis (Fin d) (IsLocalRing.ResidueField R) V :=
    Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  let eq : Fin d ≃ κ := bV.indexEquiv bk
  refine ⟨a ∘ eq, ?_⟩
  have hspR : Submodule.span R (Set.range (w ∘ a ∘ eq)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (w ∘ a ∘ eq) (bk.reindex eq.symm) (fun i => by
      simp [bk, v])
  let f : (Fin d → R) →ₗ[R] M := Fintype.linearCombination R (w ∘ a ∘ eq)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspR
  have hfi : Function.Injective f :=
    OrzechProperty.injective_of_surjective_of_injective b.equivFun.symm.toLinearMap f
      b.equivFun.symm.injective hf
  intro u
  obtain ⟨cf, hcf⟩ := hf u
  refine ⟨cf, ?_, ?_⟩
  · rw [← hcf]; simp [f, Fintype.linearCombination_apply]
  · intro cf' hcf'
    apply hfi
    rw [hcf]; simp [f, Fintype.linearCombination_apply, hcf']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquare
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.ThetaSquare
open GlobalTheory.SymLiftOdd GlobalTheory.UT.SymFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem eq_liftFun_mul (hL : L.IsLB) {k : ℤ} (s s' : LB.Sec (LPow A L k T)) (a : Γ(T.left, ⊤))
    (h : ∀ y J, Good L y J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y J =
        gs (fst T A).left y ⊤ a * sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y J)
    (j) : s'.f j = liftFun A _ a * s.f j := by
  refine fn_ext fun y hy => ?_
  choose I hI using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
  have e₁ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₂ := sec_trans (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s (𝟙 _) y hy (Good.mem hI _ (𝟙 _))
  have e₃ : gs (𝟙 _) y _ (liftFun A ((LPow A L k T).U j) a) = gs (fst T A).left y ⊤ a :=
    (gs_res (𝟙 _) y le_top hy _).trans ((gs_pull (𝟙 _) (fst T A).left y ⊤ trivial a).trans (by rw [Category.id_comp]))
  refine e₁.trans (Eq.trans ?_ ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) e₃ e₂)).symm)
  exact (congrArg _ (h y I hI)).trans (mul_left_comm _ _ _)

theorem indep (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {P v} (h : GRep L (T ⊗ A) P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), P U h = 1) (m m' : T ⊗ A ⟶ A)
    (y : (T ⊗ A).left) (J) (hJ : Good L y J) : v _ (lift (fst T A) m) y J = v _ (lift (fst T A) m') y J := by
  obtain ⟨K, _, φ, ε, s, hs, p, hv⟩ := h
  obtain ⟨a, ha⟩ := exists_constT hG hA hL (fun U _ h => (p U h).trans (hP U h)) hs
  exact (hv _ _ y J hJ).symm.trans ((ha m y J hJ).trans ((ha m' y J hJ).symm.trans (hv _ _ y J hJ)))

theorem grep_sigma {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    {Y : Over S} (w : Y ⟶ A) :
    GRep L Y (fun _ _ h => h (w⁻¹).left * (h w.left)⁻¹) (fun _ r z J => val σ (r ≫ w).left z J) :=
  (grep_gen σ hσ w.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (w⁻¹).left ^ (1 : ℤ) * h (w.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
      rw [Category.comp_id, zpow_one, zpow_neg_one])
    (fun _ _ _ _ _ => rfl)

theorem grep_two {n : T ⊗ A ⟶ A} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, n.left] ![a, b])} (hα : α.IsGen) (w : T ⊗ A ⟶ A) :
    GRep L (T ⊗ A) (fun _ _ h => h w.left ^ a * h (lift (fst T A) w ≫ n).left ^ b)
      (fun _ r z J => val α (r ≫ lift (fst T A) w).left z J) :=
  (grep_gen α hα (lift (fst T A) w).left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (lift (fst T A) w ≫ snd T A).left ^ a * h (lift (fst T A) w ≫ n).left ^ b = _
      rw [lift_snd])
    (fun _ _ _ _ _ => rfl)

theorem square_val (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {σ : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])} (hσ : σ.IsGen)
    (hσ₁ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ σ (eSec A)) (LB.oneGen L))
    (θ : ThetaGrp A L ((4 : ℕ) : ℤ) T) (hx : θ.pt ^ 4 = 1) (nu : LB.Gen (negLB A L ((4 : ℕ) : ℤ) T))
    (hnu : ∀ y J, Good L y J → ∀ m, negVal nu y J m = (val σ m.left y J ^ 4)⁻¹)
    (hs : LB.Gen.Corr L _ _ _ _ (symGen A L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen L))
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ 2).left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])}
    (hα : α.IsGen) (y : (T ⊗ A).left) (J) (hJ : Good L y J) :
    thetaVal θ y J (snd T A) * (thetaVal θ y J ((fst T A ≫ θ.pt) * snd T A) *
      val α (lift (fst T A) ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))).left y J) =
      val σ ((fst T A ≫ θ.pt) ^ 2).left y J * val α (lift (fst T A) (snd T A)).left y J := by
  have := hA.comm
  have hX : (fst T A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have s₁ : val σ (1 : T ⊗ A ⟶ A).left y J = 1 :=
    (val_pull hJ σ (eSec A) (T ⊗ A).hom).symm.trans ((val_corr hJ hσ₁ _).trans (val_one _))
  have sy := (val_symGen θ nu rfl hJ 1).symm.trans ((val_corr hJ hs _).trans (val_one _))
  rw [hnu y J hJ, hnu y J hJ, s₁, _root_.mul_one, inv_one] at sy
  have gθ := fun w => grep_two (L := L) (n := translPt A θ.pt) (a := ((4 : ℕ) : ℤ)) (b := -((4 : ℕ) : ℤ))
    (α := θ.φ) θ.isGen w
  have cl : ∀ m w : T ⊗ A ⟶ A, lift (fst T A) m ≫ lift (fst T A) w = lift (fst T A) (lift (fst T A) m ≫ w) :=
    fun m w => by rw [comp_lift, lift_fst]
  have H₁ := indep hG hA hL (((gθ (snd T A)).mul ((gθ ((fst T A ≫ θ.pt) * snd T A)).mul
    (grep_two hα ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A))))).mul (grep_two hα (snd T A)).inv)
    (fun U _ h => by
      have e : ((fst T A ≫ θ.pt) * ((fst T A ≫ θ.pt) * snd T A)) ^ 2 = snd T A ^ 2 := by
        rw [← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
      simp only [lift_translPt, MonObj.comp_pow, lift_snd, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module) (snd T A) (fst T A ≫ θ.pt)⁻¹ y J hJ
  have H₂ := indep hG hA hL ((((grep_sigma hσ (snd T A)⁻¹).pow 4).inv.mul ((grep_two hα (snd T A)).mul
    (grep_two hα (snd T A)⁻¹).inv)).mul (grep_sigma hσ (snd T A ^ 2)).inv)
    (fun U _ h => by
      simp only [MonObj.comp_pow, lift_snd, inv_inv, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module) (fst T A ≫ θ.pt) 1 y J hJ
  simp only [cl, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, lift_snd, lift_fst_assoc, mul_inv_cancel, _root_.mul_one,
    inv_one, one_pow, s₁] at H₁ H₂
  replace H₁ := congrArg Additive.ofMul H₁
  replace H₂ := congrArg Additive.ofMul H₂
  replace sy := congrArg Additive.ofMul sy
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, thetaVal] at H₁ H₂ sy ⊢
  linear_combination (norm := module) H₁ + H₂ + sy

theorem exists_symmetric_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  intro R _ _ A F _ _ _ x hx σ hσ hσ₁
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hL := A.isLB
  have := A.isAb.comm
  obtain ⟨θ₀, h₀⟩ := GlobalTheory.ThetaLift.exists_theta_of_field (FractionRing R) A (TFK (R := R) F) F (Iso.refl _) 4 x hx
  obtain ⟨nu, hnu, vn⟩ := ((grep_sigma hσ (snd (TFK (R := R) F) A.A)).pow 4).inv.out hL
    ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ≫ ι[A.A]).left] ![((4 : ℕ) : ℤ), -((4 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (snd (TFK (R := R) F) A.A).left ^ ((4 : ℕ) : ℤ) * h ((snd (TFK (R := R) F) A.A)⁻¹).left ^ (-((4 : ℕ) : ℤ))
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
  have vn' : ∀ y J, Good A.L y J → ∀ m, negVal (L := A.L) (k := ((4 : ℕ) : ℤ)) nu y J m = (val σ m.left y J ^ 4)⁻¹ :=
    fun y J hJ m => (vn _ _ y J hJ).trans (by beta_reduce; rw [lift_snd])
  obtain ⟨a, ha⟩ := exists_symConst hG A.isAb hL θ₀ (nu := nu) hnu
  obtain ⟨b, hb⟩ : ∃ b : Γ((TFK (R := R) F).left, ⊤)ˣ, a = b ^ 2 := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (k := F) (e a.val) two_pos
    have e₁ : (e.symm r) ^ 2 = a.val := by rw [← map_pow, hr, RingEquiv.symm_apply_apply]
    have u : IsUnit (e.symm r) := (isUnit_pow_iff two_ne_zero).1 (e₁ ▸ a.isUnit)
    exact ⟨u.unit, Units.ext e₁.symm⟩
  obtain ⟨θ, hpt, hv⟩ := exists_scale hL θ₀ b⁻¹
  have hθ : θ.pt = x := hpt.trans h₀
  have hs : LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L) := corr_of_val hL fun y J hJ => by
    have e₁ := (val_symGen θ₀ nu h₀ hJ (snd _ _)).symm.trans (ha _ y J hJ)
    rw [val_one, id_eq_lift, val_symGen θ nu hθ hJ, hv y J hJ, hv y J hJ, map_inv]
    rw [hb, map_pow] at e₁
    apply Additive.ofMul.injective
    replace e₁ := congrArg Additive.ofMul e₁
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at e₁ ⊢
    linear_combination (norm := module) e₁
  obtain ⟨K, _, φ, ε, s, hs', p, vs⟩ := grep_sigma hσ (x ^ 2)
  obtain ⟨c, hc⟩ := H1.exists_const A.L hL (𝟙 _) (fun v => ⟨v, by simp⟩) s hs' (fun U _ h => (p U h).trans (by
    have e : (x ^ 2)⁻¹ = x ^ 2 := by rw [inv_eq_iff_mul_eq_one, ← pow_add]; exact hx
    beta_reduce
    rw [e, mul_inv_cancel]))
  have ec : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c) = c :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply c
  refine ⟨θ, hθ, ⟨nu, hnu, hs⟩, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom c, fun z J hJ => ?_, ?_⟩
  · have e₁ := vs _ (𝟙 _) z J hJ
    have e₂ := hc _ (𝟙 _) z J hJ
    beta_reduce at e₁
    rw [Category.id_comp, Over.id_left] at e₁
    rw [Category.id_comp] at e₂
    exact (congrArg Units.val e₁).symm.trans (e₂.trans (congrArg (gs _ z ⊤) ec.symm))
  · rintro ψ m hm hψ rfl α hα t t₁ t₂ t₃ h₁ h₂ h₃ j
    rw [ec]
    refine eq_liftFun_mul hL t₁ t₃ c (fun y J hJ => ?_) j
    subst hθ
    have key := square_val hG A.isAb hL hσ hσ₁ θ hx nu vn' hs hα y J hJ
    have e₁ := vs _ (fst _ A.A) y J hJ
    have e₂ := hc _ (fst _ A.A).left y J hJ
    beta_reduce at e₁
    rw [MonObj.comp_pow] at e₁
    rw [Category.comp_id, e₁] at e₂
    have hX : (fst (TFK (R := R) F) A.A ≫ θ.pt) ^ 4 = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have eψ : lift (fst (TFK (R := R) F) A.A) ((fst _ _ ≫ θ.pt) * ((fst _ _ ≫ θ.pt) * snd _ _)) ≫ ψ =
        lift (fst _ _) (snd _ _) ≫ ψ := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, hψ, lift_fst, lift_fst]
      · rw [Category.assoc, Category.assoc, hm, MonObj.comp_pow, MonObj.comp_pow, lift_snd, lift_snd,
          ← _root_.mul_assoc, mul_pow, ← sq, ← pow_mul, hX, _root_.one_mul]
    rw [← e₂, id_eq_lift, ThetaLin.sval_of_isTwistPull A.A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₂ _ y hJ,
      ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ, ThetaLin.sval_of_isTwistPull A.A h₁ _ y hJ]
    simp only [← Over.comp_left]
    rw [lift_translT, lift_translT, eψ]
    have alg : ∀ {M : Type} [CommMonoid M] (a b c d e : Mˣ) (w : M), a * (b * c) = d * e →
        a.val * (b.val * (c.val * w)) = d.val * (e.val * w) := fun a b c d e w h => by
      have h' := congrArg (fun u => Units.val u * w) h
      simpa only [Units.val_mul, _root_.mul_assoc] using h'
    exact alg _ _ _ _ _ _ key

end GlobalTheory.ThetaSquare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensPolAV
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

def siegLamData (hG : Out.GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    SiegPre 0 1 (1 : R) (𝟙 (Sp R)) where
  A := Q.B
  ab := Q.isAb
  P := abelian₂ Q.B Q.M.L
  isLB := LB.isLB_linComb Q.M.isLB _ _
  rig₁ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull Q.M.isLB _ _ (by simp [diff₂])
  symm := lbIso_lam_pull Q.M.isLB _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact GlobalTheory.EighthPowerFactor.weilIs_one_one hG Q.isAb (pull_isLB (LB.isLB_linComb Q.M.isLB _ _) _) _

theorem lbIso_diag_data {R : Type} [CommRing R] [IsDomain R] (Q : Data R) :
    LBIso ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left)
      (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
  have hL := Q.M.isLB
  have hT : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  have hc := fun x y z => diff₃_ptCls (T := Q.B) hL hT x y z
  have hrM : Out.Rigidified Q.B Q.M.L := ⟨Q.M.rig, Q.M.rigGen⟩
  have p1 : ptCls Q.M.L Q.B 1 = 1 := ptCls_one hL hrM Q.B
  have einv : GrpObj.inv (X := Q.B) = (𝟙 Q.B)⁻¹ := by simp [Hom.inv_def]
  have key : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B) =
      ptCls Q.M.L Q.B (𝟙 Q.B) * ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹ := by
    have a := diff₂_mul_right hc (𝟙 Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹
    rw [mul_inv_cancel] at a
    have b : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) 1 = 1 := by
      simp only [diff₂, _root_.mul_one, p1, inv_one, mul_inv_cancel]
    have c : diff₂ (ptCls Q.M.L Q.B) (𝟙 Q.B) (𝟙 Q.B)⁻¹ =
        1 * (ptCls Q.M.L Q.B (𝟙 Q.B))⁻¹ * (ptCls Q.M.L Q.B (𝟙 Q.B)⁻¹)⁻¹ * 1 := by
      rw [diff₂, mul_inv_cancel, p1]
    rw [b, c] at a
    exact GlobalTheory.AdjPolLocal.le_val_one_add_pow_sub a
  refine lbIso_nested hL _ _ _ _ _ _ ?_
  rw [Fintype.prod_unique, zpow_one, Fin.prod_univ_two]
  refine (prod_lam _ _ (cls Q.M.L)).trans ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one]
  refine key.trans ?_
  rw [einv]
  rfl

theorem relAmple_diag {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (Q : Data R)
    (hD : ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left).IsLB) :
    RelAmple Q.B ((abelian₂ Q.B Q.M.L).pull (lift (𝟙 Q.B) (𝟙 Q.B)).left) := by
  have := Q.isAb.proper
  have hMa : IsAmpleLB Q.M.L := isAmpleLB_of_relAmple_of_isAffine Q.B Q.M.isLB Q.ample
  have hN : IsAmpleLB (LB.LinComb Q.M.L (K := Fin 2) ![𝟙 Q.B.left, (GrpObj.inv (X := Q.B)).left] ![1, 1]) := by
    have := GlobalTheory.GraphVolume.isAmpleLB_graph hMa (GrpObj.inv (X := Q.B)).left (N := 1) le_rfl
    rwa [Nat.cast_one] at this
  have hDa := hN.of_lbIso hD (lbIso_diag_data Q)
  refine relAmple_of_isAmpleLB Q.B hD fun U hU => ?_
  have : CompactSpace (Q.B.hom ⁻¹ᵁ U) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := Q.B.hom) _ U.isOpen hU.isCompact)
  exact hDa.pull_of_isOpenImmersion _

end GlobalTheory.MumFam.TensPol

namespace GlobalTheory.MumFam.TensPol

open GlobalTheory.CechPic GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm GlobalTheory.PrimNormPol GlobalTheory.SiegelPower

end GlobalTheory.MumFam.TensPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentials
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Theory

variable {p : ℕ} [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def redVToRange (G : PDivGroup p k) : T.M G →+ LinearMap.range G.rigOfOmega :=
  AddMonoidHom.codRestrict ((T.red G).toAddMonoidHom.comp (T.V G).toAddMonoidHom)
    (LinearMap.range G.rigOfOmega) fun m =>
      ((GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).1 (T.red G (T.V G m))).1 ⟨m, rfl⟩

def theta (G : PDivGroup p k) : T.M G →+ G.omega :=
  (LinearEquiv.ofInjective G.rigOfOmega (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2).symm.toLinearMap.toAddMonoidHom.comp
    (T.redVToRange G)

theorem rigOfOmega_theta (G : PDivGroup p k) (m : T.M G) :
    G.rigOfOmega (T.theta G m) = T.red G (T.V G m) := by
  have inj := (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2
  exact LinearEquiv.ofInjective_symm_apply G.rigOfOmega (h := inj) (T.redVToRange G m)

theorem theta_spec (G : PDivGroup p k) :
    (∀ m, G.rigOfOmega (T.theta G m) = T.red G (T.V G m)) ∧ Function.Surjective (T.theta G) ∧
      (∀ m, T.theta G m = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ (a : WittVector p k) (m : T.M G), T.theta G (WittVector.frobenius a • m) =
        WittVector.constantCoeff a • T.theta G m) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.theta G (T.map f m) = omegaMap G H f (T.theta H m) := by
  have hG := GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G
  have inj := hG.2.2.2
  refine ⟨T.rigOfOmega_theta G, fun w => ?_, fun m => ?_, fun a m => ?_, fun H f m => ?_⟩
  · obtain ⟨m, hm⟩ := (hG.1 (G.rigOfOmega w)).2 ⟨w, rfl⟩
    exact ⟨m, inj ((T.rigOfOmega_theta G m).trans hm)⟩
  · calc
      T.theta G m = 0 ↔ G.rigOfOmega (T.theta G m) = 0 :=
        ⟨fun h => (congrArg G.rigOfOmega h).trans (map_zero G.rigOfOmega),
          fun h => inj (h.trans (map_zero G.rigOfOmega).symm)⟩
      _ ↔ ∃ n, m = T.F G n := (congrArg (· = 0) (T.rigOfOmega_theta G m)).to_iff.trans (hG.2.1 m)
  · apply inj
    have hV : T.V G (WittVector.frobenius a • m) = a • T.V G m := by
      rw [(T.V G).map_smulₛₗ]
      change (WittVector.frobeniusEquiv p k).symm (WittVector.frobeniusEquiv p k a) • T.V G m = _
      rw [RingEquiv.symm_apply_apply]
    simpa only [T.rigOfOmega_theta, G.rigOfOmega.map_smul, hV] using!
      (T.red G).map_smulₛₗ a (T.V G m)
  · apply inj
    have hV := (_root_.GlobalTheory.Dieu.theory_V_verschiebung p T k G).2.2.2.2 H f m
    have hred : T.red G (T.map f (T.V H m)) = rigExtMap f (T.red H (T.V H m)) :=
      T.base.red_map trivial trivial f (T.V H m)
    rw [T.rigOfOmega_theta, ← hV, hred, ← T.rigOfOmega_theta H m, rigExtMap_rigOfOmega]

end GlobalTheory.Dieu.Theory

theorem GlobalTheory.Dieu.theta_exists :
    ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type)
      [Field k] [CharP k p] [PerfectRing k p],
      ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega, ∀ G : PDivGroup p k,
        (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧ Function.Surjective (θ G) ∧
        (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧
        (∀ (a : WittVector p k) (m : T.M G),
          θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧
        ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
          θ G (T.map f m) = omegaMap G H f (θ H m) :=
  fun _ _ T _ _ _ _ => ⟨fun G => T.theta G, fun G => T.theta_spec G⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualNumberThickeningOpenDecomp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpThickening

open GlobalTheory.RelConstThickening

theorem existsUnique_affine {R : Type} [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R))
    (p₂ : P ⟶ Z) (H : IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))))
    {V : Z.Opens} (hV : IsAffineOpen V) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := R) (constHom h V) (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    simp
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]

theorem existsUnique_decomp : ∀ (R : Type) [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R)) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))) → ∀ (O : Z.Opens) (F : Γ(P, p₂ ⁻¹ᵁ O)), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun _ _ _ _ h p₁ p₂ H O F =>
    existsUnique_comb (W := ⊤) (fun _ hV _ F => existsUnique_affine h p₁ p₂ H hV F) O le_top F

end GlobalTheory.SpThickening

end
end

