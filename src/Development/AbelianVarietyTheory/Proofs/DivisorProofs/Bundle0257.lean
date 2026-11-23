module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
public import ReciprocityTheory.Chebotarev.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharNegEqOne
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.LinSchur

theorem addChar_neg_eq_one {A : Type} [AddGroup A] (ψ : AddChar A ℂ) {x : A} (h : ψ x = 1) : ψ (-x) = 1 := by
  have e := AddChar.map_add_eq_mul ψ (-x) x
  rw [neg_add_cancel, AddChar.map_zero_eq_one, h, mul_one] at e
  exact e.symm

variable {k : Type} [Field k] [ValuativeRel k]

def latt (ψ0 : AddChar k ℂ) (n d : ℕ) (s : k) : AddSubgroup (Matrix (Fin n) (Fin d) k) where
  carrier := {Y | ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1}
  add_mem' := by
    intro a b ha hb i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.add_apply, mul_add, AddChar.map_add_eq_mul] at *
    rw [ha i j o ho, hb i j o ho, one_mul]
  zero_mem' := by
    intro i j o _
    simp
  neg_mem' := by
    intro a ha i j o ho
    simp only [Set.mem_ofPred_eq, Matrix.neg_apply, mul_neg] at *
    exact addChar_neg_eq_one ψ0 (ha i j o ho)

theorem mem_latt {ψ0 : AddChar k ℂ} {n d : ℕ} {s : k} {Y : Matrix (Fin n) (Fin d) k} :
    Y ∈ latt ψ0 n d s ↔ ∀ i j, ∀ o : k, ValuativeRel.valuation k o ≤ 1 → ψ0 (o * (s * Y i j)) = 1 := Iff.rfl


open Classical in
def cind {X : Type} [AddGroup X] (L : AddSubgroup X) (y : X) : X → ℂ := by
  classical
  exact fun Y => if Y - y ∈ L then 1 else 0

end GlobalTheory.LinSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertBaseChangeAppLECompSpecTensorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open GlobalTheory.HilbAff in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertBaseChange_appLE_comp_specTensor :
    ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
      (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.Opens),
      (letI := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
       ∀ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = secAlg C h U →
         ((bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
           ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U)
           (by simp)).hom.comp (psi A B C) =
         (theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).comp
           (Algebra.TensorProduct.map φ (AlgHom.id A B)).toRingHom) := by
  intro A B C _ _ _ _ _ Z h U
  let := (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra
  intro φ hφ
  have eL : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := C)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_fst, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have eR : (Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[A] C))).inv ≫ (pullbackSpecIso A B C).hom.appTop := by
    rw [← pullbackSpecIso_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  have hpsi : ∀ (c : C) (b : B), psi A B C (c ⊗ₜ[A] b) =
      (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
      (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c) := by
    intro c b
    have h1 := congrArg (fun F => F.hom b) eL
    have h2 := congrArg (fun F => F.hom c) eR
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
    rw [h1, h2, ← map_mul, ← map_mul]
    simp [psi]
  have eF : (pullback.fst (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      (pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    exact appLE_eq_of_eq ((pullback.lift_fst _ _ _).trans (Category.comp_id _)) _ _ _ _
  have eS : (pullback.snd (str A B) (Spec.map (CommRingCat.ofHom (algebraMap A C)))).appTop ≫
      (bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h).appLE ⊤
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) (by simp) =
      h.appLE ⊤ U (by simp) ≫
        (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans ?_
    refine (appLE_eq_of_eq (f₂ := pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ≫ h)
      (pullback.lift_snd _ _ _) _ _ _ (by simp)).trans ?_
    rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    have hF := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) eF
    have hS := congrArg (fun F => F.hom ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c)) eS
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hF hS
    have hc : φ c = secAlg C h U c := congrArg (fun f => f c) hφ
    rw [RingHom.comp_apply, hpsi, map_mul, hF, hS, RingHom.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      hc, mul_comm]
    have hθ : theta A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U
        (secAlg C h U c ⊗ₜ[A] b) =
        ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U).hom
          (secAlg C h U c) *
        ((pullback.fst (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).appLE ⊤
          ((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U)
          (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
      let : Algebra A Γ(pullback (str A B)
          (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))),
          (pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) ⁻¹ᵁ U) :=
        (((pullback.snd (str A B) (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))).app U).hom.comp
          (secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U)).toAlgebra
      exact Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [hθ]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertIdealSheafOfQuotientIdealTopStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertIdealSheafOfQuotient_ideal_top : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)), (GlobalTheory.HilbAff.xI A B C J).ideal ⟨⊤, isAffineOpen_top _⟩ = J.map (GlobalTheory.HilbAff.psi A B C) := by
  first | (exact @GlobalTheory.HilbAff.xI_ideal_top) | (exact GlobalTheory.HilbAff.xI_ideal_top) | (intros; apply GlobalTheory.HilbAff.xI_ideal_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeFunctorIsSheafZariski
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff
theorem glue_exists {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (J : ∀ i, (V i).IdealSheafData)
    (hJ : ∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') :
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i :=
  GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover V f hf hcov J hJ
theorem glue_ext {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' :=
  GlobalTheory.T.idealSheafData_ext_of_openCover' V f hf hcov I I' h
theorem good_local (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    {T : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ T)
    (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : T, ∃ i y, f i y = x)
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData)
    (h : ∀ i, GlobalTheory.HilbAff.Good A B r (f i ≫ g) (I.comap (GlobalTheory.HilbAff.bc A B g (f i)))) :
    GlobalTheory.HilbAff.Good A B r g I :=
  GlobalTheory.T.isFiniteFlatRankClosedSubscheme_of_openCover A B r V f hf hcov g I h

theorem snd_eq_of_sigma {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g₁ : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I₁ : (pullback (str A B) g₁).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g₁ I₁}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g₁, ⟨I₁, h₁⟩⟩) :
    ∃ h : g₀ = g₁, I₀ = I₁.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  have hg : g₀ = g₁ := congrArg Sigma.fst e
  refine ⟨hg, ?_⟩
  subst hg
  have h2 : I₀ = I₁ := by
    have := (Sigma.mk.inj_iff.mp e).2
    exact congrArg Subtype.val (eq_of_heq this)
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id, h2]

theorem fac_bc {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (φ : Z ⟶ pullback (str A B) g) :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      bc A B g (φ ≫ pullback.snd _ _) = φ := by
  apply pullback.hom_ext <;> simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem lift_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {T T' Z : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (g' : T' ⟶ Spec (CommRingCat.of A))
    (φ : Z ⟶ pullback (str A B) g) (φ' : Z ⟶ pullback (str A B) g')
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (hh : (φ ≫ pullback.snd _ _) ≫ g = (φ' ≫ pullback.snd _ _) ≫ g') :
    pullback.lift (φ ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) ≫
      pullback.map (str A B) ((φ ≫ pullback.snd _ _) ≫ g) (str A B) ((φ' ≫ pullback.snd _ _) ≫ g')
        (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hh]) =
    pullback.lift (φ' ≫ pullback.fst _ _) (𝟙 Z) (by
        rw [Category.id_comp, Category.assoc, pullback.condition, Category.assoc]) := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    exact e1
  · simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem comap_eq_of_map_eq {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    {X X' Z : Scheme.{0}} (y : (functor A B r).obj (op X)) (y' : (functor A B r).obj (op X'))
    (φ : Z ⟶ pullback (str A B) y.1) (φ' : Z ⟶ pullback (str A B) y'.1)
    (e1 : φ ≫ pullback.fst _ _ = φ' ≫ pullback.fst _ _)
    (e : (functor A B r).map (φ ≫ pullback.snd _ _).op y =
      (functor A B r).map (φ' ≫ pullback.snd _ _).op y') :
    y.2.1.comap φ = y'.2.1.comap φ' := by
  obtain ⟨hh, hI⟩ := snd_eq_of_sigma e
  simp only [Quiver.Hom.unop_op] at hh hI
  rw [← fac_bc y.1 φ, ← fac_bc y'.1 φ', Scheme.IdealSheafData.comap_comp, hI,
    Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp _ _ (pullback.map _ _ _ _ _ _ _ _ _),
    lift_map_eq y.1 y'.1 φ φ' e1 hh, ← Scheme.IdealSheafData.comap_comp]

theorem good_transport {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ} {T : Scheme.{0}}
    {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I : (pullback (str A B) g).IdealSheafData} (hI : Good A B r g I) :
    Good A B r g₀ (I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]))) := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact hI

theorem isOpenImmersion_bc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T T' : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) [IsOpenImmersion a] :
    IsOpenImmersion (bc A B g a) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_bc A B g a).flip inferInstance

theorem isSheaf_functor (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (functor A B r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, (functor A B r).obj (op (𝒰.X j))) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → (functor A B r).map a.op (x i) = (functor A B r).map a'.op (x j) := hx
  let g : Y ⟶ Spec (CommRingCat.of A) := 𝒰.glueMorphisms (fun j => (x j).1) fun i j =>
    congrArg Sigma.fst (hx i j _ _ _ pullback.condition)
  have hg : ∀ j, 𝒰.f j ≫ g = (x j).1 := fun j => 𝒰.ι_glueMorphisms _ _ j
  have hoi : ∀ j, IsOpenImmersion (bc A B g (𝒰.f j)) := fun j => isOpenImmersion_bc A B g (𝒰.f j)
  have hcov : ∀ p : ↥(pullback (str A B) g : Scheme.{0}), ∃ j q, bc A B g (𝒰.f j) q = p := by
    intro p
    obtain ⟨j, t, ht⟩ := 𝒰.exists_eq (pullback.snd (str A B) g p)
    have hr := (isPullback_bc A B g (𝒰.f j)).isoPullback_hom_fst
    have hmem : p ∈ Set.range (bc A B g (𝒰.f j)) := by
      rw [← hr, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso _).2, Set.image_univ,
        Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨q, hq⟩ := hmem
    exact ⟨j, q, hq⟩
  let J : ∀ j, (pullback (str A B) (𝒰.f j ≫ g)).IdealSheafData := fun j =>
    (x j).2.1.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hg j]))
  have hJ : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ pullback (str A B) (𝒰.f i ≫ g))
      (a' : Z ⟶ pullback (str A B) (𝒰.f j ≫ g)),
      a ≫ bc A B g (𝒰.f i) = a' ≫ bc A B g (𝒰.f j) → (J i).comap a = (J j).comap a' := by
    intro i j Z a a' e
    have f1 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.fst (str A B) g = pullback.fst _ _ := fun k =>
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    have f2 : ∀ k, bc A B g (𝒰.f k) ≫ pullback.snd (str A B) g = pullback.snd _ _ ≫ 𝒰.f k :=
      fun k => pullback.lift_snd _ _ _
    have p1 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have p2 : ∀ k (b : Z ⟶ pullback (str A B) (𝒰.f k ≫ g)),
        (b ≫ pullback.map (str A B) (𝒰.f k ≫ g) (str A B) (x k).1 (𝟙 _) (𝟙 _) (𝟙 _)
          (by simp) (by simp [hg k])) ≫ pullback.snd _ _ = b ≫ pullback.snd _ _ := by
      intro k b; simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
    have e1 : a ≫ pullback.fst _ _ = a' ≫ pullback.fst _ _ := by
      rw [← f1 i, ← f1 j, ← Category.assoc, e, Category.assoc]
    have e2 : (a ≫ pullback.snd _ _) ≫ 𝒰.f i = (a' ≫ pullback.snd _ _) ≫ 𝒰.f j := by
      rw [Category.assoc, Category.assoc, ← f2 i, ← f2 j, ← Category.assoc, e, Category.assoc]
    change ((x i).2.1.comap _).comap a = ((x j).2.1.comap _).comap a'
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    refine comap_eq_of_map_eq (x i) (x j) _ _ (by rw [p1, p1, e1]) ?_
    rw [p2, p2]
    exact hx i j Z _ _ e2
  obtain ⟨I, hI⟩ := glue_exists (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
    (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov J hJ
  have good : Good A B r g I := good_local A B r 𝒰.X 𝒰.f (fun j => inferInstance)
    (fun y => 𝒰.exists_eq y) g I (fun j => by rw [hI j]; exact good_transport (hg j) (x j).2.2)
  have amal : ∀ j, (functor A B r).map (𝒰.f j).op ⟨g, ⟨I, good⟩⟩ = x j := fun j =>
    sigma_eq A B r (hg j) (hI j) _ (x j).2.2
  refine ⟨⟨g, ⟨I, good⟩⟩, amal, fun y' hy' => ?_⟩
  replace hy' : ∀ j, (functor A B r).map (𝒰.f j).op y' = x j := hy'
  have e : y'.1 = g := 𝒰.hom_ext _ _ fun j => (congrArg Sigma.fst (hy' j)).trans (hg j).symm
  obtain ⟨g', I', hI'⟩ := y'
  change g' = g at e
  subst e
  have : I' = I := by
    refine glue_ext (fun j : 𝒰.I₀ => pullback (str A B) (𝒰.f j ≫ g))
      (fun j : 𝒰.I₀ => bc A B g (𝒰.f j)) hoi hcov I' I fun j => ?_
    have := (hy' j).trans (amal j).symm
    exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)
  subst this
  rfl

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPairStatement
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (a b : F), ((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  first | exact @GlobalTheory.GaussExt.norm_gEmb | exact GlobalTheory.GaussExt.norm_gEmb | (intros; apply GlobalTheory.GaussExt.norm_gEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingCofaceComplexOfFunctorDZeroOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.CartanStep
variable {T : Type 1} [Category.{0} T]

abbrev altCx (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) : CochainComplex AddCommGrpCat.{1} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ F)

theorem alternatingCofaceComplexOfFunctor_d_zero_one (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 0 1 y = F.map (X.δ (n := 0) 0) y - F.map (X.δ (n := 0) 1) y := by
  have h0 : (altCx X F).d 0 1 = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F) 0 :=
    CochainComplex.of_d (fun n ↦ (X ⋙ F).obj (SimplexCategory.mk n)) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X ⋙ F)) 0
  rw [h0]
  simp [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg, CosimplicialObject.δ]
  rfl

theorem altCx_nat (X : CosimplicialObject T) {F G : T ⥤ AddCommGrpCat.{1}} (φ : F ⟶ G) (n m : ℕ)
    (w : F.obj (X.obj (SimplexCategory.mk n))) :
    (altCx X G).d n m (φ.app _ w) = φ.app _ ((altCx X F).d n m w) := by
  have h := ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map (Functor.whiskerLeft X φ)).comm n m
  exact ConcreteCategory.congr_hom h w

theorem altCx_dd (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (y : F.obj (X.obj (SimplexCategory.mk 0))) :
    (altCx X F).d 1 2 ((altCx X F).d 0 1 y) = 0 :=
  ConcreteCategory.congr_hom ((altCx X F).d_comp_d 0 1 2) y

theorem altCx_exact1 (X : CosimplicialObject T) (F : T ⥤ AddCommGrpCat.{1}) (h : (altCx X F).ExactAt 1)
    (w : F.obj (X.obj (SimplexCategory.mk 1))) (hw : (altCx X F).d 1 2 w = 0) :
    ∃ v : F.obj (X.obj (SimplexCategory.mk 0)), (altCx X F).d 0 1 v = w := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp), ShortComplex.ab_exact_iff] at h
  exact h w hw

theorem aug_δ {U : T} {X : CosimplicialObject T} (a : (CosimplicialObject.const T).obj U ⟶ X) (j : Fin 2) :
    a.app (SimplexCategory.mk 0) ≫ X.δ j = a.app (SimplexCategory.mk 1) := by
  have h := a.naturality (SimplexCategory.δ j)
  simpa [CosimplicialObject.δ] using h.symm

theorem cartan_step : ∀ (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T) (a : (CosimplicialObject.const T).obj U ⟶ X) (Z M N : T ⥤ AddCommGrpCat.{1}) (i : Z ⟶ M) (d : M ⟶ N), (∀ V, Function.Injective (i.app V)) → (∀ V (y : M.obj V), d.app V y = 0 ↔ ∃ w, i.app V w = y) → WExact M a → WExact N a → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj (X ⋙ Z)).ExactAt 1 → ∀ (z : N.obj U) (y : M.obj (X.obj (SimplexCategory.mk (0)))), d.app _ y = N.map (a.app (SimplexCategory.mk (0))) z → ∃ x : M.obj U, d.app U x = z := by
  intro T _ U X a Z M N i d hi hd hM hN hZ z y hy
  have hu : d.app _ ((altCx X M).d 0 1 y) = 0 := by
    rw [alternatingCofaceComplexOfFunctor_d_zero_one, map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, hy,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← N.map_comp, ← N.map_comp,
      aug_δ a 0, aug_δ a 1, sub_self]
  obtain ⟨w, hw⟩ := (hd _ _).1 hu
  have hw2 : (altCx X Z).d 1 2 w = 0 := by
    have h1 : i.app _ ((altCx X Z).d 1 2 w) = 0 := by
      rw [← altCx_nat X i 1 2 w, hw, altCx_dd]
      rfl
    exact hi _ (h1.trans (map_zero _).symm)
  obtain ⟨v, hv⟩ := altCx_exact1 X Z hZ w hw2
  have hy' : M.map (X.δ (n := 0) 0) (y - i.app _ v) = M.map (X.δ (n := 0) 1) (y - i.app _ v) := by
    rw [← sub_eq_zero, map_sub, map_sub, sub_sub_sub_comm, ← alternatingCofaceComplexOfFunctor_d_zero_one, ← alternatingCofaceComplexOfFunctor_d_zero_one, altCx_nat X i 0 1, hv, hw]
    exact sub_self _
  obtain ⟨x, hx⟩ := hM.2.1 _ hy'
  refine ⟨x, hN.1 ?_⟩
  have e := ConcreteCategory.congr_hom (d.naturality (a.app (SimplexCategory.mk 0))) x
  simp only [ConcreteCategory.comp_apply] at e
  have e2 : d.app (X.obj (SimplexCategory.mk 0)) (y - i.app _ v) = N.map (a.app (SimplexCategory.mk 0)) z := by
    rw [map_sub, hy, (hd _ _).2 ⟨v, rfl⟩, sub_zero]
  rw [← hx] at e2
  exact e.symm.trans e2

end GlobalTheory.CartanStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaMatrixReduction.of_local) | (exact GlobalTheory.AzumayaMatrixReduction.of_local) | (intros; apply GlobalTheory.AzumayaMatrixReduction.of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveObjFiniteTypeInt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem widePushout_finiteType_int {J : Type} [Finite J] [Nonempty J] (A B : CommRingCat.{0})
    (g : A ⟶ B) (hB : Algebra.FiniteType ℤ B) :
    Algebra.FiniteType ℤ ((widePushout A (fun _ : J => B) (fun _ => g) : CommRingCat.{0})) := by
  classical
  obtain ⟨s, hs⟩ := hB.out
  set W := widePushout A (fun _ : J => B) (fun _ => g) with hW
  let T : Set W := ⋃ j : J, (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)
  have hTfin : T.Finite := Set.finite_iUnion fun j => s.finite_toSet.image _
  let S : Subring W := Subring.closure T
  have hB' : ∀ b : B, b ∈ Subring.closure (s : Set B) := by
    intro b
    have hb : b ∈ Algebra.adjoin ℤ (s : Set B) := hs ▸ Algebra.mem_top
    rw [Algebra.adjoin_int] at hb
    exact hb
  have hmem : ∀ (j : J) (b : B), (WidePushout.ι (fun _ : J => g) j).hom b ∈ S := by
    intro j b
    have hle : (Subring.closure (s : Set B)).map (WidePushout.ι (fun _ : J => g) j).hom ≤ S := by
      rw [RingHom.map_closure]
      exact Subring.closure_mono (Set.subset_iUnion (fun j => (WidePushout.ι (fun _ : J => g) j).hom '' (s : Set B)) j)
    exact hle ⟨b, hB' b, rfl⟩
  let ιS : J → (B ⟶ CommRingCat.of S) := fun j =>
    CommRingCat.ofHom ((WidePushout.ι (fun _ : J => g) j).hom.codRestrict S (hmem j))
  let j₀ : J := Classical.arbitrary J
  have hw : ∀ j : J, g ≫ ιS j = g ≫ ιS j₀ := by
    intro j
    ext a
    change (g ≫ WidePushout.ι (fun _ : J => g) j) a = (g ≫ WidePushout.ι (fun _ : J => g) j₀) a
    rw [WidePushout.arrow_ι (fun _ : J => g) j, WidePushout.arrow_ι (fun _ : J => g) j₀]
  let d : W ⟶ CommRingCat.of S := WidePushout.desc (g ≫ ιS j₀) ιS hw
  let incl : CommRingCat.of S ⟶ W := CommRingCat.ofHom S.subtype
  have hid : d ≫ incl = 𝟙 W := by
    apply WidePushout.hom_ext
    · intro j
      rw [← Category.assoc, WidePushout.ι_desc]
      ext b <;> rfl
    · rw [← Category.assoc, WidePushout.head_desc, ← WidePushout.arrow_ι (fun _ : J => g) j₀]
      ext a <;> rfl
  have htop : ∀ w : W, w ∈ S := by
    intro w
    have : (d ≫ incl) w = w := by rw [hid]; rfl
    rw [← this]
    exact (d w).2
  refine ⟨⟨hTfin.toFinset, ?_⟩⟩
  rw [Set.Finite.coe_toFinset, Algebra.adjoin_int]
  ext w
  simp only [Algebra.mem_top, iff_true]
  exact htop w

end GlobalTheory

theorem GlobalTheory.cechConerve_obj_finiteType_int : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), Algebra.FiniteType ℤ B →
    ∀ k : SimplexCategory, Algebra.FiniteType ℤ ((Arrow.mk g).cechConerve.obj k) := by
  intro A B g hB k
  exact GlobalTheory.widePushout_finiteType_int (J := Fin (k.len + 1)) A B g hB
end

