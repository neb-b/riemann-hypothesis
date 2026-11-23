module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionRingInjectiveInvariantsOfModule
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.InvAlg

section CompletionTransfer

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A)

theorem pow_smul_top_eq_restrictScalars (n : ℕ) :
    (J ^ n • ⊤ : Submodule A B) =
      ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  ext x
  simp [smul_eq_mul, Ideal.mul_top]

def levelEquiv (n : ℕ) :
    (B ⧸ (J ^ n • ⊤ : Submodule A B)) ≃ₗ[A] (B ⧸ ((J.map (algebraMap A B)) ^ n • ⊤ : Submodule B B)) :=
  (Submodule.quotEquivOfEq _ _ (pow_smul_top_eq_restrictScalars J n)).trans
    (Submodule.Quotient.restrictScalarsEquiv A _)

theorem levelEquiv_transitionMap {m n : ℕ} (hmn : m ≤ n) (q : B ⧸ (J ^ n • ⊤ : Submodule A B)) :
    levelEquiv J m (AdicCompletion.transitionMap J B hmn q) =
      AdicCompletion.transitionMap (J.map (algebraMap A B)) B hmn (levelEquiv J n q) := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

def complEquivFun (x : AdicCompletion J B) : AdicCompletion (J.map (algebraMap A B)) B :=
  ⟨fun n => levelEquiv J n (x.val n), fun {m n} hmn => by
    rw [← levelEquiv_transitionMap, x.property hmn]⟩

theorem complEquivFun_val (x : AdicCompletion J B) (n : ℕ) :
    (complEquivFun J x).val n = levelEquiv J n (x.val n) := rfl

theorem complEquivFun_injective : Function.Injective (complEquivFun (B := B) J) := by
  intro x y h
  refine AdicCompletion.ext fun n => (levelEquiv J n).injective ?_
  have := congrArg (fun z : AdicCompletion (J.map (algebraMap A B)) B => z.val n) h
  simpa only [complEquivFun_val] using this

theorem complEquivFun_surjective : Function.Surjective (complEquivFun (B := B) J) := by
  intro z
  refine ⟨⟨fun n => (levelEquiv J n).symm (z.val n), fun {m n} hmn => ?_⟩, ?_⟩
  · apply (levelEquiv J m).injective
    rw [levelEquiv_transitionMap, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact z.property hmn
  · refine AdicCompletion.ext fun n => ?_
    exact LinearEquiv.apply_symm_apply (levelEquiv J n) (z.val n)

end CompletionTransfer

theorem val_eq_mk_of_evalₐ {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b) :
    y.val n = Submodule.Quotient.mk b := by
  have hle : I ^ n ≤ (I ^ n • ⊤ : Ideal R) := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.eval_apply, ← AdicCompletion.factor_evalₐ_eq_eval I y hle, h]
  rfl

theorem evalₐ_eq_mk_of_val {R : Type} [CommRing R] (I : Ideal R) (y : AdicCompletion I R) (n : ℕ) (b : R)
    (h : y.val n = Submodule.Quotient.mk b) :
    AdicCompletion.evalₐ I n y = Ideal.Quotient.mk _ b := by
  have hle : (I ^ n • ⊤ : Ideal R) ≤ I ^ n := by rw [smul_eq_mul, Ideal.mul_top]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I y hle, AdicCompletion.eval_apply, h]
  rfl

theorem cmap_transfer : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (J : Ideal A) (Γ : Type) (g : Γ → (B →ₐ[A] B)),
    Function.Injective (AdicCompletion.map J (Algebra.linearMap A B)) →
    (∀ y, y ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) ↔
      ∀ σ, AdicCompletion.map J (g σ).toLinearMap y = y) →
    Function.Injective (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ∧
    ∀ y, y ∈ Set.range (GlobalTheory.InvAlg.cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl) ↔
      ∀ σ, GlobalTheory.InvAlg.cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (GlobalTheory.InvAlg.map_algebraMap_le (g σ) J) y = y := by
  intro A B _ _ _ J Γ g hinj hrange
  have h1 : ∀ x, complEquivFun J (AdicCompletion.map J (Algebra.linearMap A B) x) =
      cmap (algebraMap A B) J (J.map (algebraMap A B)) le_rfl x := by
    intro x
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← ha]
    symm
    apply val_eq_mk_of_evalₐ
    rw [evalₐ_cmap, evalₐ_eq_mk_of_val J x n a ha.symm, Ideal.quotientMap_mk]
    rfl
  have h2 : ∀ σ z, complEquivFun J (AdicCompletion.map J (g σ).toLinearMap z) =
      cmap (g σ).toRingHom (J.map (algebraMap A B)) (J.map (algebraMap A B))
        (map_algebraMap_le (g σ) J) (complEquivFun J z) := by
    intro σ z
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (z.val n)
    rw [complEquivFun_val, AdicCompletion.map_val_apply, ← hb]
    symm
    apply val_eq_mk_of_evalₐ
    refine (evalₐ_cmap _ _ _ _ n _).trans ?_
    rw [evalₐ_eq_mk_of_val _ (complEquivFun J z) n b
      (by rw [complEquivFun_val, ← hb]; rfl), Ideal.quotientMap_mk]
    rfl
  refine ⟨fun x y hxy => hinj (complEquivFun_injective J (by rw [h1, h1, hxy])), fun y => ?_⟩
  obtain ⟨z, rfl⟩ := complEquivFun_surjective J y
  constructor
  · rintro ⟨x, hx⟩ σ
    have hz : z ∈ LinearMap.range (AdicCompletion.map J (Algebra.linearMap A B)) :=
      ⟨x, complEquivFun_injective J (by rw [h1, hx])⟩
    rw [← h2, (hrange z).1 hz σ]
  · intro h
    obtain ⟨x, hx⟩ := (hrange z).2 fun σ => complEquivFun_injective J (by rw [h2, h σ])
    exact ⟨x, by rw [← h1, hx]⟩

end GlobalTheory.InvAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Mum

variable {X Y Z : Scheme.{0}} {L : LB X} {k k' : ℕ}

abbrev secGerm (u : Y ⟶ X) (y : Y) (s : H0 L k) (i : Fin 1 → L.ι) : Y.presheaf.stalk y :=
  gs u y (secChart L i) (s.f i)

theorem secRatioEq_iff_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} :
    SecRatioEq L u v s₁ s₂ t₁ t₂ ↔ ∀ (y : Y) (i i' : Fin 1 → L.ι), u y ∈ secChart L i → v y ∈ secChart L i' →
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i' := by
  have key : ∀ (y : Y) (i i' : Fin 1 → L.ι) (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s : H0 L k)
      (t : H0 L k'), gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
    intro y i i' hi hi' s t
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
    rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
    exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)
  refine ⟨fun h y i i' hi hi' => ?_, fun h i i' => fn_ext fun y hy => ?_⟩
  · rw [← key y i i' hi hi', ← key y i i' hi hi', h i i']
  · rw [key y i i' hy.1 hy.2, key y i i' hy.1 hy.2]
    exact h y i i' hy.1 hy.2

theorem exists_unit_secGerm (k : ℕ) (u : Y ⟶ X) (y : Y) {i j : Fin 1 → L.ι} (hi : u y ∈ secChart L i)
    (hj : u y ∈ secChart L j) :
    ∃ c : (Y.presheaf.stalk y)ˣ, ∀ s : H0 L k, secGerm u y s i = c.val * secGerm u y s j := by
  have hy : u y ∈ secChart L i ⊓ secChart L j := ⟨hi, hj⟩
  refine ⟨gm u y (secChart L i ⊓ secChart L j)
    ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g i j), fun s => ?_⟩
  have h := congrArg (gs u y (secChart L i ⊓ secChart L j)) (s.compat i j)
  refine (gs_res u y inf_le_left hy _).symm.trans (h.trans ((gs_mul u y _ hy _ _).trans ?_))
  exact congrArg₂ (· * ·) (gs_unit u y _ hy _) (gs_res u y inf_le_right hy _)

theorem secRatioEq_of_exists_germ {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'}
    (h : ∀ y : Y, ∃ i i' : Fin 1 → L.ι, u y ∈ secChart L i ∧ v y ∈ secChart L i' ∧
      secGerm u y s₁ i * secGerm v y t₂ i' = secGerm u y s₂ i * secGerm v y t₁ i') :
    SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun y j j' hj hj' => ?_
  obtain ⟨i, i', hi, hi', e⟩ := h y
  obtain ⟨c, hc⟩ := exists_unit_secGerm k u y hj hi
  obtain ⟨c', hc'⟩ := exists_unit_secGerm k' v y hj' hi'
  rw [hc, hc, hc', hc']
  linear_combination (c.val * c'.val) * e

theorem secGerm_comp (w : Z ⟶ Y) (u : Y ⟶ X) (z : Z) (s : H0 L k) {i : Fin 1 → L.ι} (hi : u (w z) ∈ secChart L i) :
    secGerm (w ≫ u) z s i = (w.stalkMap z).hom (secGerm u (w z) s i) := by
  have key : ∀ a : Γ(X, secChart L i), gs (w ≫ u) z _ a = (w.stalkMap z).hom (gs u (w z) _ a) := fun a => by
    rw [gs_eq u (w z) _ hi, ← gs_pull w u z _ hi, gs_eq w z _ hi]
    exact (Scheme.Hom.germ_stalkMap_apply w _ z hi _).symm
  exact key _

theorem SecRatioEq.comp {u v : Y ⟶ X} {s₁ s₂ : H0 L k} {t₁ t₂ : H0 L k'} (h : SecRatioEq L u v s₁ s₂ t₁ t₂)
    (w : Z ⟶ Y) : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂ := by
  refine secRatioEq_iff_germ.2 fun z i i' hi hi' => ?_
  rw [secGerm_comp w u z _ hi, secGerm_comp w u z _ hi, secGerm_comp w v z _ hi', secGerm_comp w v z _ hi',
    ← map_mul, ← map_mul, secRatioEq_iff_germ.1 h (w z) i i' hi hi']

theorem app_injective_of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] (W : Y.Opens) :
    Function.Injective (w.app W).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_basicOpen_eq_bot
  by_contra hne
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨z, hz⟩ := w.denseRange.exists_mem_open (Y.basicOpen a).isOpen ⟨y, hy⟩
  have hz' : z ∈ w ⁻¹ᵁ Y.basicOpen a := hz
  rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero] at hz'
  exact hz'

theorem SecRatioEq.of_isDominant [IsReduced Y] (w : Z ⟶ Y) [IsDominant w] {u v : Y ⟶ X} {s₁ s₂ : H0 L k}
    {t₁ t₂ : H0 L k'} (h : SecRatioEq L (w ≫ u) (w ≫ v) s₁ s₂ t₁ t₂) : SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  intro i i'
  apply app_injective_of_isDominant w
  refine fn_ext fun z hz => ?_
  have hz' : w z ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := hz
  rw [gs_pull (𝟙 Z) w z _ hz', gs_pull (𝟙 Z) w z _ hz', Category.id_comp, gs_mul _ _ _ hz', gs_mul _ _ _ hz',
    gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz', gs_res _ _ _ hz']
  exact (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).trans
    ((secRatioEq_iff_germ.1 h z i i' hz'.1 hz'.2).trans
      (congrArg₂ (· * ·) (gs_pull w u z _ hz'.1 _) (gs_pull w v z _ hz'.2 _)).symm)

def VeryAmpleAlong {K : Type} [CommRing K] {A : Scheme.{0}} (p : A ⟶ Spec (CommRingCat.of K)) (π : A ⟶ X)
    (L : LB X) {k m : ℕ} (σ : Fin (m + 1) → H0 L k) : Prop :=
  (⨆ i, π ⁻¹ᵁ nonzeroLocus (σ i) = ⊤) ∧ ∀ i, IsAffineOpen (π ⁻¹ᵁ nonzeroLocus (σ i)) ∧
    ∃ r : Fin (m + 1) → Γ(A, π ⁻¹ᵁ nonzeroLocus (σ i)),
      (∀ (j : Fin (m + 1)) (c : Fin 1 → L.ι) (a : A), π a ∈ nonzeroLocus (σ i) → π a ∈ secChart L c →
        secGerm π a (σ j) c = gs (𝟙 A) a (π ⁻¹ᵁ nonzeroLocus (σ i)) (r j) * secGerm π a (σ i) c) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightNonnegVerticalOfNefOnFibres
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VertHeight

theorem charZero_residueField_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    (RingHom.charZero_iff (Z.germToFunctionField_injective ⊤)).1 hc
  exact (RingHom.charZero_iff (Z.residue (genericPoint Z)).hom.injective).1 h₁

theorem height_nonneg_of_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (C : HermLB p) (h : X → ℝ), NefFib C →
    C.IsArithHeight h → ∀ z : X, ¬ CharZero (X.residueField z) → 0 ≤ h z := by
  intro k _ X _ p D hX C h hC H z hz
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨a⟩⟩ | ⟨hc, -⟩
  · letI := a
    haveI := hX.finite
    obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    rw [H.vertical Z i (ZMod ℓ) d hd, Nat.card_zmod]
    refine mul_nonneg ?_ (Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_le))
    have hN := GlobalTheory.FibreNef.isNef_pull_of_nefOver ℓ i C
      ((GlobalTheory.VertForm.nefFib_iff C).1 hC ℓ Fact.out)
    rw [topSelf_def]
    exact_mod_cast GlobalTheory.nefNumerics_outright.1.interNum_nonneg
      (GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver ℓ i) hd fun _ => hN
  · haveI := charZero_residueField_genericPoint Z hc
    exact absurd ((i.residueFieldMap (genericPoint Z)).hom.charZero) hz

end GlobalTheory.VertHeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtension
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem axesE1_of_axesO1 : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  intro hO R₀ R₁ _ _ _ q hq A _ g hab hsm c h₁ h₂
  obtain ⟨B, hB, pr, pr', habB, hsmB, hp, hp', -, -, -, hl, hr⟩ :=
    _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R₀ R₁ A g hab hsm
  letI : GrpObj B := hB
  obtain ⟨e, he⟩ := _root_.GlobalTheory.Obs.BC.extO1 R₀ R₁ q hq
  set c₁ := (e _ _ _ _ _ hp').symm c with hc₁
  have hc : e _ _ _ _ _ hp' c₁ = c := by simp [hc₁]
  have hl' : IsPullO (overW (lift (𝟙 B) 1)) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift (𝟙 A) 1)) (overW (lift (𝟙 B) 1)) hl c₁ 0 ?_
    rw [hc, map_zero]; exact h₁
  have hr' : IsPullO (overW (lift 1 (𝟙 B))) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift 1 (𝟙 A))) (overW (lift 1 (𝟙 B))) hr c₁ 0 ?_
    rw [hc, map_zero]; exact h₂
  have h0 : c₁ = 0 := hO R₁ B g habB hsmB c₁ hl' hr'
  rw [← hc, h0, map_zero]

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedPosDefFiniteProjectiveLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UTrait

theorem balanced_posDef_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c), T.be ∈ balForms H.bar T.P.D.toPre.X ∧ (∀ y, y ≠ 0 → 0 < T.be y y) ∧ Module.Finite (𝓞 E) T.P.D.toPre.X ∧ Module.Projective (𝓞 E) T.P.D.toPre.X ∧ ∃ n : ℕ, Nonempty (T.P.D.toPre.X ≃ₗ[ℤ] (Fin n → ℤ)) := by
  intro E _ _ _ H Dw l Xo c T
  haveI hf : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  refine ⟨(balForms_eq_levelForms H T.P.D.toPre.X).ge T.lev, fun y hy => ?_, hf, ?_, _,
    ⟨(Module.finBasis ℤ T.P.D.toPre.X).equivFun⟩⟩
  · obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hy
    simpa using hi
  · exact GlobalTheory.Forms.projective_of_int (𝓞 E) _

end GlobalTheory.UPoinc.UTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ptAlg_apply_of_left {R D E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]
    (z : Pt (SpAlg R D) E) (f : D →+* E) (h : z.left = spMap f) (a : D) : ptAlg z a = f a := by
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom a = f a
  rw [h, Spec.preimage_map]
  rfl

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.bcPull_sumMul_fv : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left)
    (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left),
    q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π →
    ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π)
      (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))),
      bcPull w (sumMul d fun i ↦ fv (X := B) (β i)) =
        fv (X := B') (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  classical
  intro R D _ _ _ B B' q w π hfst hsnd mB J _ d β
  have w' : π ≫ B.hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← hsnd, Category.assoc, Over.w (snd (SpAlg R D) B), w]
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  funext E i1 i2 E' i3 i4 ψ y
  have hzero : fv (X := B') 0 E E' ψ y = 0 := by
    have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd 0 0)
    simp only [add_zero, Fn1.add] at h
    linear_combination -h
  have hsum : ∀ s : Finset J, fv (X := B') (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)) E E' ψ y =
      ∑ i ∈ s, algebraMap D E' (d i) * fv (X := B') (mB.coef.pullbackOneCocycle (β i)) E E' ψ y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd (d j • mB.coef.pullbackOneCocycle (β j)) (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)))
      simp only [Fn1.add] at h
      rw [h, ih, hsmul]
  rw [hsum]
  simp only [bcPull, sumMul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [_root_.GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase R D (algebraMap R D) B B' π w' mB (β i)]
  congr 1
  · let _ : Algebra R E := algVia (algebraMap R D) E
    have hl : (ptVia w y ≫ fst (SpAlg R D) B).left = spMap (algebraMap D E) := by
      rw [Over.comp_left]
      change (y.left ≫ q) ≫ (fst (SpAlg R D) B).left = _
      rw [Category.assoc, hfst]
      exact Over.w y
    rw [ptAlg_apply_of_left _ _ hl]
    exact ψ.commutes (d i)
  · simp only [bcPull]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (y.left ≫ q) ≫ (snd (SpAlg R D) B).left = y.left ≫ π
    rw [Category.assoc, hsnd]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaPos
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem Trait.beta_pos : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F)
    (a : T.D.toPre.X), a ≠ 0 → 0 < T.β a a := by
  intro g n o _ ζ F T a ha
  obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal T.V).ne_top ha
  fin_cases i
  simpa using hi

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CFxi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.MumFam.FactorAdj

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem c_xp (F : Factor D D') (y : D'.X) : D.c (F.xp y) = D'.c y ≫ F.pr := by
  have h : D.c (F.xp y) ≫ F.inc = D'.c y ≫ F.pr ≫ F.inc := by
    rw [← F.c_xi, F.xi_xp, F.o.c_lin, F.pr_inc]
  have h2 := congrArg (· ≫ F.pr) h
  simp only [Category.assoc, F.inc_pr, Category.comp_id] at h2
  exact h2

theorem c_fxi (F : Factor D D') (y : D.X) : D'.c (F.f • F.xi y) = D.c y ≫ F.inc ≫ F.o.onB.act F.f := by
  rw [F.o.c_lin, F.c_xi, Category.assoc]

end GlobalTheory.MumFam.FactorAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] [Algebra R C] (JC : Ideal C) (δC : DividedPowers JC) (π : C →ₐ[R] B) (w : C →+ K1 R δ), (∀ x y, w (x * y) = π x • w y + π y • w x) → (∀ r, w (algebraMap R C r) = 0) → (∀ n, ∀ a ∈ JC, w (δC.dpow (n + 1) a) = π (δC.dpow n a) • w a) → ∃ ρ : DR R C → DR R B, (∀ x y, ρ (x + y) - ρ x - ρ y ∈ rel R δ) ∧ (∀ x y, ρ (x * y) - ρ x * ρ y ∈ rel R δ) ∧ (∀ c, ρ (algebraMap C (DR R C) c) - algebraMap B (DR R B) (π c) ∈ rel R δ) ∧ (∀ c ω, Submodule.Quotient.mk ω = w c → ρ (ι1 (D R C c)) - ι1 ω ∈ rel R δ) ∧ (∀ x ∈ rel R δC, ρ x ∈ rel R δ) ∧ (∀ x, ∃ ω, ρ (ι1 x) - ι1 ω ∈ rel R δ) ∧ ∀ (j : ℕ), ∀ x ∈ ⋀[C]^j Ω[C⁄R], ∃ y ∈ ⋀[B]^j Ω[B⁄R], ρ x - y ∈ rel R δ := by
  first | exact @GlobalTheory.PDForm.exists_lift_of_pdDerivation | exact GlobalTheory.PDForm.exists_lift_of_pdDerivation | (intros; apply GlobalTheory.PDForm.exists_lift_of_pdDerivation <;> assumption)
end

