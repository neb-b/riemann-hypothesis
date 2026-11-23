module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructure
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.RingFacts

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

theorem monic_Q (a : S → O) : (∏ s, (X - Polynomial.C (a s)) : O[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

theorem lin_eq (a : S → O) (s : S) :
    lin a s = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X]) (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem cofac_eq (a : S → O) (τ : S) :
    cofac a τ = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X])
      (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => lin_eq a s

theorem ev_mk (a : S → O) (τ : S) (f : O[X]) :
    ev a τ (AdjoinRoot.mk _ f) = f.eval (a τ) := by
  simp [ev]

theorem exists_lin_mul_of_ev_eq_zero (a : S → O) (τ : S) (r : RS a) (hr : ev a τ r = 0) :
    ∃ r', r = lin a τ * r' := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [ev_mk] at hr
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hr
  exact ⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩

theorem eq_algebraMap_add_lin_mul (a : S → O) (τ : S) (r : RS a) :
    ∃ g, r = algebraMap O (RS a) (ev a τ r) + lin a τ * g := by
  obtain ⟨g, hg⟩ := exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r))
    (by rw [map_sub, AlgHom.commutes]; simp)
  exact ⟨g, by rw [← hg]; ring⟩

theorem lin_mul_cofac (a : S → O) (τ : S) : lin a τ * cofac a τ = 0 := by
  rw [cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl
    (fun s _ => lin_eq a s), ← map_prod]
  exact AdjoinRoot.mk_self

theorem ev_cofac (a : S → O) (τ : S) :
    ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => ev_lin a τ s

theorem eq_smul_cofac_of_lin_mul_eq_zero [IsDomain O] (a : S → O) (τ : S) (r : RS a)
    (hr : lin a τ * r = 0) : ∃ c : O, r = algebraMap O (RS a) c * cofac a τ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero] at hr
  obtain ⟨g, hg⟩ := hr
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc] at hg
  have hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g :=
    mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg
  obtain ⟨h, hh⟩ := eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)
  refine ⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩
  have hc := lin_mul_cofac a τ
  calc AdjoinRoot.mk _ f = cofac a τ * AdjoinRoot.mk _ g := by rw [hf, map_mul, cofac_eq]
    _ = cofac a τ * (algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) + lin a τ * h) := by
        rw [← hh]
    _ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ
        + (lin a τ * cofac a τ) * h := by ring
    _ = _ := by rw [hc]; simp

theorem ring_facts : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S]
    (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧
    lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧
    (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧
    (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧
    (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  intro O _ _ S _ _ a τ
  let pb := AdjoinRoot.powerBasis' (monic_Q a)
  exact ⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ,
    exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ),
    eq_smul_cofac_of_lin_mul_eq_zero a τ⟩

end GlobalTheory.RingFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEqStatement
section
open MeasureTheory
open scoped ENNReal Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D : Set X), MeasurableSet D → IsFundamentalDomain Γ D μ → ∀ (E : Set S), IsFundamentalDomain Γ E ν → ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  first | exact @GlobalTheory.CovolIndep.ae_measure_slice_eq | exact GlobalTheory.CovolIndep.ae_measure_slice_eq | (intros; apply GlobalTheory.CovolIndep.ae_measure_slice_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalSurjectiveOfCotangentSpanTop
section
open GlobalTheory
open scoped Pointwise

namespace GlobalTheory.NakAug

theorem surj : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (q : O), q ∈ IsLocalRing.maximalIdeal O → ∀ (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A), (∀ i, ε (x i) = 0) → (∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N) → Submodule.span O (Set.range fun i => AugCot.d ε (x i)) = ⊤ → Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O →ₐ[O] A) := by
  first
  | exact @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective
  | (apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerIdealSurjectivity.aeval_surjective ..)

end GlobalTheory.NakAug
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapBasicOpenBijective
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem bijective_linearCombination_iff_localizedModule_map {R R' S S' : Type} [CommRing R]
    [CommRing R'] [CommRing S] [CommRing S'] [Algebra R R'] [Algebra R S] [Algebra R' S']
    [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] (f : R)
    [IsLocalization.Away f R'] [IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) S']
    {r : ℕ} (v : Fin r → S) :
    Function.Bijective (Fintype.linearCombination R' (fun k => algebraMap S S' (v k))) ↔
      Function.Bijective (LocalizedModule.map (Submonoid.powers f) (Fintype.linearCombination R v)) := by
  let gM : (Fin r → R) →ₗ[R] (Fin r → R') :=
    LinearMap.pi (fun k => (Algebra.linearMap R R') ∘ₗ LinearMap.proj k)
  haveI : IsLocalizedModule (Submonoid.powers f) gM :=
    IsLocalizedModule.pi (Submonoid.powers f) (fun _ : Fin r => Algebra.linearMap R R')
  let gS : S →ₗ[R] S' := (IsScalarTower.toAlgHom R S S').toLinearMap
  haveI : IsLocalizedModule (Submonoid.powers f) gS := inferInstance
  let φ : (Fin r → R') →ₗ[R] S' :=
    (Fintype.linearCombination R' (fun k => algebraMap S S' (v k))).restrictScalars R
  have hcomm : φ ∘ₗ gM = gS ∘ₗ Fintype.linearCombination R v := by
    ext c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [φ, gM, gS, Fintype.linearCombination_apply, Algebra.smul_def, map_sum, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have hmap : IsLocalizedModule.map (Submonoid.powers f) gM gS (Fintype.linearCombination R v) = φ := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers f) gM gS
    rw [IsLocalizedModule.map_comp, hcomm]
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective gM gS, hmap]
  rfl

end GlobalTheory.HilbAff

namespace GlobalTheory.HilbAff

theorem coord_basicOpen_bijective_iff : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (f : Γ(Z, W)),
    Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (Z.basicOpen f)) ↔
      Function.Bijective (LocalizedModule.map (Submonoid.powers f) (GlobalTheory.HilbAff.coord A B e σ y W)) := by
  intro A B _ _ _ N r e σ Z y W f
  haveI : IsFinite (subStr A B y) := y.2.2.1
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage _
  have hle : subStr A B y ⁻¹ᵁ Z.basicOpen f ≤ subStr A B y ⁻¹ᵁ (W : Z.Opens) :=
    fun _ h => Z.basicOpen_le f h
  have hpre : subStr A B y ⁻¹ᵁ Z.basicOpen f =
      y.2.1.subscheme.basicOpen ((subStr A B y).app W f) := Scheme.preimage_basicOpen _ f
  letI i1 : Algebra Γ(Z, W) Γ(Z, Z.basicOpen f) :=
    (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
  letI i2 : Algebra (Sec A B y W) (Sec A B y (Z.basicOpen f)) :=
    (y.2.1.subscheme.presheaf.map (homOfLE hle).op).hom.toAlgebra
  letI i3 : Algebra Γ(Z, W) (Sec A B y (Z.basicOpen f)) :=
    ((algebraMap (Sec A B y W) (Sec A B y (Z.basicOpen f))).comp
      (algebraMap Γ(Z, W) (Sec A B y W))).toAlgebra
  haveI : IsScalarTower Γ(Z, W) (Sec A B y W) (Sec A B y (Z.basicOpen f)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, W) Γ(Z, Z.basicOpen f) (Sec A B y (Z.basicOpen f)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (congr($((subStr A B y).naturality (homOfLE (Z.basicOpen_le f)).op) a)).symm)
  haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) :=
    W.2.isLocalization_of_eq_basicOpen f (homOfLE (Z.basicOpen_le f)) rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (Sec A B y W) (Submonoid.powers f))
      (Sec A B y (Z.basicOpen f)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hV.isLocalization_of_eq_basicOpen _ (homOfLE hle) hpre
  have hgen : ∀ b, gen A B y (Z.basicOpen f) b =
      algebraMap (Sec A B y W) (Sec A B y (Z.basicOpen f)) (gen A B y W b) := by
    intro b
    have h := Scheme.Hom.appLE_map (y.2.1.subschemeι ≫ pullback.fst _ y.1) (U := ⊤)
      (V := subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp) (homOfLE hle).op
    simp only [gen]
    rw [← h]
    rfl
  have hc : coord A B e σ y (Z.basicOpen f) = Fintype.linearCombination Γ(Z, Z.basicOpen f)
      (fun k => algebraMap (Sec A B y W) (Sec A B y (Z.basicOpen f)) (gen A B y W (e (σ k)))) := by
    simp only [coord, hgen]
  rw [hc]
  exact bijective_linearCombination_iff_localizedModule_map f _

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapRestrictBijective
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem bijective_appLE_of_image_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (V : X.Opens) (h : f ''ᵁ V = U) (e : V ≤ f ⁻¹ᵁ U) :
    Function.Bijective (f.appLE U V e).hom := by
  subst h
  have : f.appLE (f ''ᵁ V) V e = (f.appIso V).hom := (Scheme.Hom.appIso_hom' f V).symm
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

theorem appLE_congr_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

theorem coord_restrict_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (U : Z.Opens) (W : U.toScheme.Opens),
    Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y (U.ι ''ᵁ W)) →
      Function.Bijective (GlobalTheory.HilbAff.coord A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) W) := by
  intro A B _ _ _ N r e σ Z y U W hb
  set a := U.ι with ha
  set y' := (functor A B r).map a.op y with hy'
  let f := bc A B y.1 a
  let J := y.2.1.comap f
  let φ : J.subscheme ⟶ y.2.1.subscheme := (y.2.1.comapIso f).hom ≫ pullback.snd f y.2.1.subschemeι
  have hbc_fst : f ≫ pullback.fst (str A B) y.1 = pullback.fst (str A B) (a ≫ y.1) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hbc_snd : f ≫ pullback.snd (str A B) y.1 = pullback.snd (str A B) (a ≫ y.1) ≫ a :=
    pullback.lift_snd _ _ _
  have hφι : φ ≫ y.2.1.subschemeι = J.subschemeι ≫ f := by
    simp only [φ, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have h1 : φ ≫ y.2.1.subschemeι ≫ pullback.fst _ y.1 = J.subschemeι ≫ pullback.fst _ (a ≫ y.1) := by
    rw [reassoc_of% hφι, hbc_fst]
  have h2 : φ ≫ y.2.1.subschemeι ≫ pullback.snd _ y.1 = (J.subschemeι ≫ pullback.snd _ (a ≫ y.1)) ≫ a := by
    rw [reassoc_of% hφι, hbc_snd, Category.assoc]
  have H : IsPullback (pullback.snd f y.2.1.subschemeι)
      (pullback.fst f y.2.1.subschemeι ≫ pullback.snd _ (a ≫ y.1))
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) a :=
    (IsPullback.of_hasPullback f y.2.1.subschemeι).flip.paste_vert (isPullback_bc A B y.1 a)
  have hpb : IsPullback (J.subschemeι ≫ pullback.snd _ (a ≫ y.1)) φ a
      (y.2.1.subschemeι ≫ pullback.snd _ y.1) :=
    H.flip.of_iso (y.2.1.comapIso f).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← Category.assoc,
        Scheme.IdealSheafData.comapIso_inv_subschemeι])
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; dsimp only [φ]; rw [Iso.inv_hom_id_assoc])
      (by simp) (by simp)
  haveI : IsOpenImmersion f :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B y.1 a).flip
      (inferInstanceAs (IsOpenImmersion U.ι))
  haveI : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  set X0 := a ''ᵁ W with hX0
  have hX : φ ''ᵁ ((subStr A B y') ⁻¹ᵁ W) = (subStr A B y) ⁻¹ᵁ X0 :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hpb W
  have hle : (subStr A B y') ⁻¹ᵁ W ≤ φ ⁻¹ᵁ ((subStr A B y) ⁻¹ᵁ X0) := by
    rw [← hX]; exact (Scheme.Hom.preimage_image_eq φ _).ge
  have hW : W ≤ a ⁻¹ᵁ X0 := (Scheme.Hom.preimage_image_eq a W).ge
  let β := φ.appLE _ _ hle
  let α := a.appLE X0 W hW
  have hβ : Function.Bijective β.hom := bijective_appLE_of_image_eq φ _ _ hX hle
  have hα : Function.Bijective α.hom := bijective_appLE_of_image_eq a _ _ rfl hW
  have hAm : (subStr A B y).app X0 ≫ β = α ≫ (subStr A B y').app W := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((appLE_congr_hom h2 _ _ _ _).trans
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm)
  have hA : ∀ x, β.hom (algebraMap Γ(Z, X0) (Sec A B y X0) x) =
      algebraMap Γ(U.toScheme, W) (Sec A B y' W) (α.hom x) := by
    intro x
    change ((subStr A B y).app X0 ≫ β).hom x = (α ≫ (subStr A B y').app W).hom x
    rw [hAm]; rfl
  have hG : ∀ b, β.hom (gen A B y X0 b) = gen A B y' W b := by
    intro b
    change ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ _ _ ≫ β).hom _ =
      ((J.subschemeι ≫ pullback.fst _ (a ≫ y.1)).appLE ⊤ _ _).hom _
    have hGm : (y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ X0) (by simp) ≫ β =
        (J.subschemeι ≫ pullback.fst _ (a ≫ y.1)).appLE ⊤ (subStr A B y' ⁻¹ᵁ W) (by simp) :=
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_congr_hom h1 _ _ _ _)
    rw [hGm]; rfl
  have hc : ∀ c : Fin r → Γ(Z, X0), β.hom (coord A B e σ y X0 c) =
      coord A B e σ y' W (fun k => α.hom (c k)) := by
    intro c
    rw [coord, coord, Fintype.linearCombination_apply, Fintype.linearCombination_apply]
    simp only [Algebra.smul_def]
    erw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    erw [map_mul, hA, hG]
    rfl
  have hαe : Function.Bijective (fun c : Fin r → Γ(Z, X0) => fun k => α.hom (c k)) :=
    hα.comp_left
  have hcomp : (coord A B e σ y' W) ∘ (fun c : Fin r → Γ(Z, X0) => fun k => α.hom (c k)) =
      β.hom ∘ (coord A B e σ y X0) := by
    funext c; exact (hc c).symm
  rw [← Function.Bijective.of_comp_iff _ hαe, hcomp]
  exact hβ.comp hb

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubschemeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbert_representing_universal_subscheme : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.universal) | (exact GlobalTheory.HilbAff.universal) | (intros; apply GlobalTheory.HilbAff.universal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeValuativeCriterionExistence
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_flat_ideal_extension (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X']
    (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X)
    (h : IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    (I : X'.IdealSheafData) : ∃ J : X.IdealSheafData, Flat (J.subschemeι ≫ p) ∧ J.comap b = I := by
  obtain ⟨J₀, hf, hJ⟩ := _root_.GlobalTheory.FlatHilbAff.exists_flat_ideal V K X X' p p' b h (I.ideal ⟨⊤, isAffineOpen_top X'⟩)
  have e : (Scheme.IdealSheafData.ofIdealTop J₀).ideal ⟨⊤, isAffineOpen_top X⟩ = J₀ :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J₀
  refine ⟨Scheme.IdealSheafData.ofIdealTop J₀, GlobalTheory.T.flat_subscheme_of_quotient_flat_affine V X p _ (by rw [e]; exact hf), ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [_root_.GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine, e, hJ]

theorem finrank_const_of_isLocalRing (V : Type) [CommRing V] [IsLocalRing V] (Z : Scheme.{0})
    (f : Z ⟶ Spec (CommRingCat.of V)) (h1 : IsFinite f) (h2 : Flat f) (x y : Spec (CommRingCat.of V)) :
    f.finrank x = f.finrank y := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have ef : f = Z.isoSpec.hom ≫ Spec.map φ := by rw [hφ]; simp
  have hf1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hf2 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hr1 := hf1
  have hr2 := hf2
  rw [IsFinite.SpecMap_iff] at hr1
  rw [Flat.SpecMap_iff] at hr2
  rw [ef, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hr1 hr2]
  algebraize [φ.hom]
  have : Module.Free V Γ(Z, ⊤) := Module.free_of_flat_of_isLocalRing
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_good_extension (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (r : ℕ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g)).IdealSheafData)
    (hI : Good A B r _ I) :
    ∃ J, Good A B r g J ∧ J.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  obtain ⟨J, hJf, hJ⟩ := exists_flat_ideal_extension V K _ _ (pullback.snd (str A B) g) (pullback.snd _ _) _
    (isPullback_bc A B g _) I
  have : IsFinite (str A B) := by
    rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr inferInstance
  have h1 : IsFinite (J.subschemeι ≫ pullback.snd (str A B) g) := inferInstance
  refine ⟨J, ⟨h1, hJf, fun y => ?_⟩, hJ⟩
  obtain ⟨_, _, h3⟩ := hI
  subst hJ
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  rw [finrank_const_of_isLocalRing V _ _ h1 hJf y (a pt)]
  have H : IsPullback (pullback.snd (bc A B g a) J.subschemeι)
      (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))
      (J.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) J.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (J.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (J.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) J.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H hJf
  have := h3 pt
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H pt]
    at this
  exact this

theorem valuativeExistence (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H) :
    ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  intro S
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), (R.homEquiv f).1 = f ≫ (R.homEquiv (𝟙 H)).1 := by
    intro T f
    have h := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at h
    rw [h]; rfl
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hι
  have gen : ∀ x : (functor A B r).obj (op (Spec (CommRingCat.of S.K))), x.1 = ι ≫ S.i₂ →
      ∃ y : (functor A B r).obj (op (Spec (CommRingCat.of S.R))),
        y.1 = S.i₂ ∧ (functor A B r).map ι.op y = x := by
    rintro ⟨g', I, hI⟩ hx
    dsimp only at hx
    subst hx
    obtain ⟨J, hJ, hJI⟩ := exists_good_extension A B r S.R S.K S.i₂ I hI
    subst hJI
    exact ⟨⟨S.i₂, J, hJ⟩, rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := gen (R.homEquiv S.i₁) ((key S.i₁).trans S.commSq.w)
  refine ⟨⟨{ l := R.homEquiv.symm y, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply R.homEquiv.injective
    rw [R.homEquiv_comp, Equiv.apply_symm_apply, hy2]
  · rw [← key, Equiv.apply_symm_apply, hy1]

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsFiniteFlat
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem sec_finite_flat (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) :
    Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  obtain ⟨h1, h2, -⟩ := y.2.2
  haveI : IsFinite (subStr A B y) := h1
  haveI : Flat (subStr A B y) := h2
  constructor
  · exact IsFinite.finite_app (subStr A B y) W W.2
  · have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage (subStr A B y)
    have h := Scheme.Hom.flat_appLE (subStr A B y) W.2 hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    exact h

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZero
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem _root_.GlobalTheory.ainf_isDomain_and_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hprim
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  refine ⟨by unfold _root_.GlobalTheory.Sandwich.Ainf; infer_instance, ?_⟩
  intro h
  unfold _root_.GlobalTheory.Sandwich.mu at h
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have hε : ε = 1 := by
    have := congrArg (fun x => WittVector.coeff x 0) h1
    simpa [WittVector.teichmuller_coeff_zero] using this
  have hroot : _root_.GlobalTheory.Sandwich.root ε = 1 := by
    unfold _root_.GlobalTheory.Sandwich.root
    rw [hε, map_one]
  rw [hroot, map_one] at hprim
  exact (Fact.out : p.Prime).one_lt.ne' (IsPrimitiveRoot.one_left_iff.mp hprim)

end GlobalTheory
end

