module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.CubeGen

open GlobalTheory.AbLaw.Cube

theorem surjective_appTop {X : Scheme.{0}} (P : Over X) (e : 𝟙_ (Over X) ⟶ P) (hs : Smooth P.hom)
    (hg : GeometricallyIntegral P.hom) (hr : IsReduced X) (hab : genericPoints X ⊆ abLocus P) :
    Function.Surjective P.hom.appTop.hom := by
  change ∀ u : Γ(P.left, P.hom ⁻¹ᵁ ⊤), ∃ a, (P.hom.app ⊤).hom a = u
  intro u
  have he : e.left ≫ P.hom = 𝟙 X := Over.w e
  have hle : (⊤ : X.Opens) ≤ e.left ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have key : ∀ (g : X ⟶ X) (hg : g = 𝟙 X) (h' : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) (c : Γ(X, ⊤)),
      (g.appLE ⊤ ⊤ h').hom c = c := by
    rintro g rfl h' c
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    change (X.presheaf.map (𝟙 (Opposite.op (⊤ : X.Opens)))).hom c = c
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hφψ : ∀ c : Γ(X, ⊤), (e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom ((P.hom.app ⊤).hom c) = c := fun c =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ c) (Scheme.Hom.comp_appLE e.left P.hom ⊤ ⊤ hle)).symm.trans
      (key _ he hle c)
  refine ⟨(e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u, ?_⟩
  have h1 := GlobalTheory.eq_one_of_appLE_section_eq_one X P e.left he hs hg ⟨hr, hab⟩ ⊤
    (1 + u - (P.hom.app ⊤).hom ((e.left.appLE (P.hom ⁻¹ᵁ ⊤) ⊤ hle).hom u)) hle
    (by rw [map_sub, map_add (f := _), map_one, hφψ]; ring)
  linear_combination -h1

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def cubicalOfNormalised (s₂ : Function.Surjective (A ⊗ A).hom.appTop.hom)
    (s₃ : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (s₄ : Function.Surjective (A ⊗ A ⊗ A ⊗ A).hom.appTop.hom)
    (M : RigLB A) (t : LB.Gen (Theta A M.L)) (ht : t.IsGen) (hn : IsNormalised t) : CubicalStr A M :=
  { t := t
    isGen := ht
    face := fun i => by
      have key : ∀ a b c : G2 A ⟶ A, lift 1 1 ≫ a = (1 : 𝟙_ (Over S) ⟶ A) → lift 1 1 ≫ b = (1 : 𝟙_ (Over S) ⟶ A) →
          lift 1 1 ≫ c = (1 : 𝟙_ (Over S) ⟶ A) → a = 1 ∨ b = 1 ∨ c = 1 →
          LB.Gen.Corr M.L _ _ (Y := (G2 A).left) _ _
            (LB.pullGen M.L (thφ A (x3 A)) thε t (lift a (lift b c)).left) (LB.oneGen M.L) := by
        intro a b c ha hb hc h
        refine corr_of_val_section M.isLB s₂ (lift 1 1) (fun V _ k => ?_) (DVR.pullGen_isGen _ _ _ _ ht _) oneGen_isGen
          (fun y J hJ => (hn.pull _ ha hb hc hJ).trans (val_one _).symm)
        refine (Fintype.prod_empty _).trans (Eq.trans ?_ (prod_cub a b c k).symm)
        apply Additive.ofMul.injective
        rcases h with rfl | rfl | rfl <;> simp only [_root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;> abel
      fin_cases i
      · exact key 1 (x2 A 0) (x2 A 1) (MonObj.comp_one _) (by simp [x2]) (by simp [x2]) (.inl rfl)
      · exact key (x2 A 0) 1 (x2 A 1) (by simp [x2]) (MonObj.comp_one _) (by simp [x2]) (.inr (.inl rfl))
      · exact key (x2 A 0) (x2 A 1) 1 (by simp [x2]) (by simp [x2]) (MonObj.comp_one _) (.inr (.inr rfl))
    cubeSymmetric_swap_first := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 1) (x3 A 0)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cubeSymmetric_swap_last := by
      refine corr_of_val_section M.isLB s₃ (lift 1 (lift 1 1)) (φ := thφ A (x3 A)) (ε := thε) (fun V _ k => ?_) ht
        (DVR.pullGen_isGen _ _ _ _ ht _) (fun y J hJ => (hn y J hJ).trans
          (hn.pull _ (by simp [x3]) (by simp [x3]) (by simp [x3]) hJ).symm)
      refine (prod_cub _ _ _ k).trans (Eq.trans ?_ ((prod_theta k).trans (prod_cub _ _ _ k)).symm)
      rw [_root_.mul_comm (x3 A 2) (x3 A 1), mul_right_comm (x3 A 0) (x3 A 2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    cocycle := by
      let e : 𝟙_ (Over S) ⟶ G4 A := lift 1 (lift 1 (lift 1 1))
      have e₀ : e ≫ x4 A 0 = 1 := by simp [e, x4]
      have e₁ : e ≫ x4 A 1 = 1 := by simp [e, x4]
      have e₂ : e ≫ x4 A 2 = 1 := by simp [e, x4]
      have e₃ : e ≫ x4 A 3 = 1 := by simp [e, x4]
      have f₀ : e ≫ padd A (x4 A 0) (x4 A 1) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
      have f₁ : e ≫ padd A (x4 A 1) (x4 A 2) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
      refine corr_of_val_section M.isLB s₄ e (fun V _ k => ?_)
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht _))
        (fun y J hJ => ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e f₀ e₂ e₃ hJ) (hn.pull e e₀ e₁ e₃ hJ))).trans ((val_mul hJ _ _ _).trans
          (congrArg₂ (· * ·) (hn.pull e e₀ f₁ e₃ hJ) (hn.pull e e₁ e₂ e₃ hJ))).symm)
      refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0) (x4 A 1 * x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 1) (x4 A 2) (x4 A 3) k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x4 A 0 * x4 A 1) (x4 A 2) (x4 A 3) k)
        (prod_cub (x4 A 0) (x4 A 1) (x4 A 3) k)).symm)
      apply Additive.ofMul.injective
      simp only [_root_.mul_assoc (x4 A 0), ofMul_mul, ofMul_inv]
      abel }

theorem exists_gen_of_lbIso {Z : Scheme.{0}} (L : LB Z) (f : Z ⟶ Z) (h : LBIso L (L.pull f)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![f, 𝟙 Z] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  refine gen_chartPull (A := (L.pull f).div L) (h := 𝟙 Z)
    { idx := fun j => (fun _ => j 0, j 1)
      le := fun j y hy => ?_
      g := fun y j j' hj hj' => ?_ } w hw
  · have h0 : f y ∈ L.U (j 0) := Set.mem_iInter.1 hy 0
    have h1 : y ∈ L.U (j 1) := Set.mem_iInter.1 hy 1
    exact ⟨mem_pull.2 h0, h1⟩
  · have a0 : f y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    have a1 : y ∈ L.U (j 1) := Set.mem_iInter.1 hj 1
    have b0 : f y ∈ L.U (j' 0) := Set.mem_iInter.1 hj' 0
    have b1 : y ∈ L.U (j' 1) := Set.mem_iInter.1 hj' 1
    refine (gm_linComb L _ _ (𝟙 Z) y j j' hj hj').trans ?_
    refine Eq.trans ?_ (gm_div L (L.pull f) (𝟙 Z) y _ _ ⟨⟨mem_pull.2 a0, a1⟩, mem_pull.2 b0, b1⟩).symm
    rw [gm_pull_g L f (𝟙 Z) y _ _ (mem_pull.2 a0) (mem_pull.2 b0)]
    simp [Fin.prod_univ_two]

theorem cubical_and_symmetric : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  intro X G _ _ L hsa hrg
  obtain ⟨hr, hab⟩ := hrg
  have hsm : Smooth G.hom := hsa.smooth
  have hgc : GeometricallyConnected G.hom := hsa.geomConnected
  have hgi : GeometricallyIntegral G.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth X G
  refine ⟨fun ⟨t, ht⟩ => ?_, fun hiso => ?_⟩
  · obtain ⟨t', ht', hn⟩ := exists_normalised L.isLB t ht
    obtain ⟨sm2, gi2, ab2⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G G hsm hsm hgi hgi
    obtain ⟨sm3, gi3, ab3⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G) hsm sm2 hgi gi2
    obtain ⟨sm4, gi4, ab4⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj X G (G ⊗ G ⊗ G) hsm sm3 hgi gi3
    have g2 : genericPoints X ⊆ abLocus (G ⊗ G) := fun x hx => ab2 ⟨hab hx, hab hx⟩
    have g3 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G) := fun x hx => ab3 ⟨hab hx, g2 hx⟩
    have g4 : genericPoints X ⊆ abLocus (G ⊗ G ⊗ G ⊗ G) := fun x hx => ab4 ⟨hab hx, g3 hx⟩
    exact ⟨cubicalOfNormalised (surjective_appTop (G ⊗ G) (lift 1 1) sm2 gi2 hr g2)
      (surjective_appTop (G ⊗ G ⊗ G) (lift 1 (lift 1 1)) sm3 gi3 hr g3)
      (surjective_appTop (G ⊗ G ⊗ G ⊗ G) (lift 1 (lift 1 (lift 1 1))) sm4 gi4 hr g4) L t' ht' hn⟩
  · exact GlobalTheory.PrimNorm.isSymmetric_of_hasGen L (exists_gen_of_lbIso L.L _ hiso)

end GlobalTheory.CubeGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqIffIsometry
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

def HomAlg : Prop :=
  ∀ (P P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) →
    ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F z) = u.ex z ≫ f

def WeilDet : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (P P' : Out.PolAV (Sp k)) (α : P.A ⟶ P'.A) (p d : ℕ), IsMonHom α →
    p.Prime → CharZero k → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c : kˣ), 0 < n → n.Coprime p → x ^ n = 1 →
      y ^ n = 1 → Out.WeilIs P.A P.L n x y (unitOn c) → Out.WeilIs P'.A P'.L n (x ≫ α) (y ≫ α) (unitOn (c ^ d))) →
    LBIso (abelian₂ P.A (lbPow P.L d)) (abelian₂ P.A (P'.L.pull α.left))

theorem exists_hom (hT : ThetaUnifAV) (hA : HomAlg) (Q Q' : Out.PolAV (Sp ℂ)) (hg : Q'.g = Q.g)
    {e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q.A)} {e' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Q'.A)}
    (he : ∀ (g₀ : ℕ) (u : HolUnif Q.A Q.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = u.ex z)
    (he' : ∀ (g₀ : ℕ) (u : HolUnif Q'.A Q'.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e' (h z) = u.ex z)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, e z = 1 → e' (F z) = 1) :
    ∃ α : Q.A ⟶ Q'.A, IsMonHom α ∧ ∀ z, e' (F z) = e z ≫ α := by
  obtain ⟨r, hr⟩ := Q.rigid
  obtain ⟨r', hr'⟩ := Q'.rigid
  obtain ⟨u, -⟩ := hT Q r hr
  obtain ⟨u₁, -⟩ := hT Q' r' hr'
  have u' : HolUnif Q'.A Q'.L Q.g := hg ▸ u₁
  obtain ⟨h, hh⟩ := he _ u
  obtain ⟨h', hh'⟩ := he' _ u'
  obtain ⟨α, hα, hu⟩ := hA Q Q' Q.g u u' (h'.symm.toLinearMap ∘ₗ F ∘ₗ h.toLinearMap) rfl hg fun z hz =>
    (u'.ker _).1 (by
      rw [← hh']
      show e' (h' (h'.symm (F (h z)))) = 1
      rw [h'.apply_symm_apply]
      exact hF _ ((hh z).trans ((u.ker z).2 hz)))
  refine ⟨α, hα, fun z => ?_⟩
  have k := hu (h.symm z)
  rw [← hh', ← hh, h.apply_symm_apply] at k
  rw [← k]
  show _ = e' (h' (h'.symm (F (h (h.symm z)))))
  rw [h'.apply_symm_apply, h.apply_symm_apply]

abbrev objPol {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (o : Obj D l b s) {n : ℕ} (h : IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension n o.t.G.hom ∧
      Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) : Out.PolAV S :=
  { A := o.t.G, isAb := h.1, g := n, smoothDim := h.2.1, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := h.2.2.1,
    sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem exists_sabMap (hT : ThetaUnifAV) (hG : Out.GlobalFnsSt) (hA : HomAlg) (hD : WeilDet) {D D₁ D₂ : Datum H}
    {l : Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ} (o₁ o₂ : Obj D l b s) {n : ℕ}
    (p₁ : IsAbelianScheme o₁.t.G ∧ SmoothOfRelativeDimension n o₁.t.G.hom ∧
      Out.Rigidified o₁.t.G o₁.t.PP.L ∧ Out.Sym o₁.t.G o₁.t.PP.L)
    (p₂ : IsAbelianScheme o₂.t.G ∧ SmoothOfRelativeDimension n o₂.t.G.hom ∧
      Out.Rigidified o₂.t.G o₂.t.PP.L ∧ Out.Sym o₂.t.G o₂.t.PP.L)
    {ty : Fin g → (E →+* ℂ)} {P₁ : D₁.La →+ (Fin g → ℂ)} {P₂ : D₂.La →+ (Fin g → ℂ)} (hP₁ : IsPeriod D₁ ty P₁)
    (hP₂ : IsPeriod D₂ ty P₂) {e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₁.t.G)}
    {e₂ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ o₂.t.G)} (a₁ : ∀ z w, e₁ (z + w) = e₁ z * e₁ w)
    (s₁ : Function.Surjective e₁) (s₂ : Function.Surjective e₂)
    (r₁ : ReadsPeriods o₁.t unitOn D₁ ty P₁ e₁) (r₂ : ReadsPeriods o₂.t unitOn D₂ ty P₂ e₂)
    (u₁ : ∀ (g₀ : ℕ) (u : HolUnif o₁.t.G o₁.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z)
    (u₂ : ∀ (g₀ : ℕ) (u : HolUnif o₂.t.G o₂.t.PP.L g₀),
      ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₂ (h z) = u.ex z)
    (gam : D₁.La ≃ₗ[𝓞 E] D₂.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hEF : ∀ a b, D₂.EF (gam a) (gam b) = D₁.EF a b) (hh : ∀ a, P₂ (gam a) = h (P₁ a)) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (e₁ z).left ≫ m.φ = (e₂ (h z)).left := by
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, e₂ (h z) = e₁ z ≫ α :=
    exists_hom hT hA (objPol o₁ p₁) (objPol o₂ p₂) rfl u₁ u₂ h.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₁.1 z).1 hz
      exact (r₂.1 _).2 ⟨gam a, hh a⟩
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, e₁ (h.symm z) = e₂ z ≫ β :=
    exists_hom hT hA (objPol o₂ p₂) (objPol o₁ p₁) rfl u₂ u₁ h.symm.toLinearMap fun z hz => by
      obtain ⟨a, rfl⟩ := (r₂.1 z).1 hz
      refine (r₁.1 _).2 ⟨gam.symm a, h.injective ?_⟩
      rw [← hh, gam.apply_symm_apply]
      exact (h.apply_symm_apply _).symm
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₁ x
        rw [← Category.assoc, ← hα', ← hβ', h.symm_apply_apply, Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := s₂ x
        rw [← Category.assoc, ← hβ', ← hα', h.apply_symm_apply, Category.comp_id] }
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have k : (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)) =
        LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ) := by
      refine LinearMap.ext_on_range hP₁.2.2.2.1 fun x => ?_
      show h (fun k => ty k (a : E) * P₁ x k) = fun k => ty k (a : E) * h (P₁ x) k
      rw [← funext (hP₁.1 a x), ← hh, ← hh, map_smul]
      exact funext (hP₂.1 a _)
    exact DFunLike.congr_fun k z
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := s₁ x
      rw [← Category.assoc, ← Category.assoc, ← r₁.2.1, ← hα', ← hα', ← r₂.2.1, hcomm]
  have hlam := hD ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hx
      obtain ⟨a', rfl⟩ := exists_div_of_pow a₁ s₁ r₁.1 hk hy
      have w := r₁.2.2 k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := r₂.2.2 k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      rw [hh, hh, ← map_smul h, ← map_smul h, hα', hα', hEF] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hG p₁.1 α o₁.t.cub o₂.t.cub (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

theorem exists_objMap {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : Nonempty (ObjMap o₁ o₂ (𝟙 S)) := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

def baseOfEmb {l : Level H} (σ : KA l →+* ℂ) : Base l ℂ where
  unit _ hn := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
  ρ := σ (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := σ (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective

end GlobalTheory.UnifPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAffineCoverOfQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.QuotientNorm

open TopologicalSpace

theorem exists_lb_of_cocycle {Y : Scheme.{0}} {K : Type} (V : K → Y.Opens) (hV : ⨆ i, V i = ⊤)
    (a : ∀ i, K → Γ(Y, V i)) (h₁ : ∀ i, a i i = 1) (hle : ∀ i j, Y.basicOpen (a i j) ≤ V j)
    (hc : ∀ i j k, resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i k) =
      resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j) * resG Y (inf_le_right : V i ⊓ V j ≤ V j) (a j k)) :
    ∃ (L : LB Y) (σ : K → LB.Sec L), L.IsLB ∧ ∀ j, Out.nonzeroLocus (σ j) = V j := by
  have hu (i j) : IsUnit (resG Y (inf_le_left : V i ⊓ V j ≤ V i) (a i j)) :=
    IsUnit.of_mul_eq_one _ ((hc i j i).symm.trans (by rw [h₁, map_one]))
  have hg (i j) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i ⊓ V j) (hu i j).unit.val = gs (𝟙 Y) y (V i) (a i j) := gs_res _ y _ hy _
  have hc' (i j k) (y : Y) (hy : y ∈ V i ⊓ V j) :
      gs (𝟙 Y) y (V i) (a i k) = gs (𝟙 Y) y (V i) (a i j) * gs (𝟙 Y) y (V j) (a j k) := by
    have e := congrArg (gs (𝟙 Y) y _) (hc i j k)
    rwa [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy] at e
  refine ⟨⟨K, V, fun i j => (hu i j).unit⟩, fun k => ⟨fun i => a i k, fun i j => hc i j k⟩,
    ⟨hV, fun i => Units.ext (fn_ext fun y hy => ?_), fun i j k => Units.ext (fn_ext fun y hy => ?_)⟩, fun j => ?_⟩
  · exact (gs_res (𝟙 Y) y (le_inf le_rfl le_rfl) hy _).trans ((hg i i y ⟨hy, hy⟩).trans (by rw [h₁]; rfl))
  · refine (gs_mul (𝟙 Y) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) ((gs_res (𝟙 Y) y inf_le_left hy _).trans (hg i j y hy.1))
      ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hy _).trans
        (hg j k y ⟨hy.1.2, hy.2⟩))).trans ((hc' i j k y hy.1).symm.trans ?_)
    exact ((gs_res (𝟙 Y) y (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hy _).trans
      (hg i k y ⟨hy.1.1, hy.2⟩)).symm
  · refine le_antisymm (iSup_le fun i => hle i j) (le_trans ?_ (basicOpen_le_nonzeroLocus _ j))
    exact (Y.basicOpen_of_isUnit (f := a j j) (h₁ j ▸ isUnit_one)).ge

variable {G : Type} [Group G] {X Y : Scheme.{0}} {ρ : G →* Aut X} {π : X ⟶ Y}

theorem eq_of_gs (h : IsAffineQuotient ρ π) {W : Y.Opens} {a b : Γ(Y, W)}
    (e : ∀ x, π x ∈ W → gs π x W a = gs π x W b) : a = b :=
  h.app_injective W (fn_ext fun x hx => (gs_pull (𝟙 X) π x W hx a).trans
    (((Category.id_comp π).symm ▸ e x hx :).trans (gs_pull (𝟙 X) π x W hx b).symm))

theorem exists_norm [Fintype G] (h : IsAffineQuotient ρ π) {W : Y.Opens} {D : X.Opens}
    (hD : ∀ g, π ⁻¹ᵁ W ≤ (ρ g).asIso.hom ⁻¹ᵁ D) (r : Γ(X, D)) :
    ∃ a : Γ(Y, W), ∀ x, π x ∈ W → gs π x W a = ∏ g, gs (ρ g).asIso.hom x D r := by
  obtain ⟨a, ha⟩ := h.mem_range_app W (∏ g, (ρ g).asIso.hom.appLE D _ (hD g) r) fun k => ⟨h.preimage_le W k, by
    rw [map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight k) _ _ fun g => ?_
    have : (ρ (g * k)).asIso.hom = (ρ k).asIso.hom ≫ (ρ g).asIso.hom := by rw [map_mul]; rfl
    simp only [Equiv.coe_mulRight, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, this]⟩
  refine ⟨a, fun x hx => ?_⟩
  have e := gs_pull (𝟙 X) π x W hx a
  rw [Category.id_comp] at e
  rw [← e, show (π.app W).hom a = _ from ha, gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx, map_prod, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  exact (gs_eq (𝟙 X) x (π ⁻¹ᵁ W) hx _).symm.trans ((gs_appLE _ D _ (hD g) (𝟙 X) x hx r).trans (by rw [Category.id_comp]))

theorem exists_affine_cover_of_quotient :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → X.IsSeparated → ∀ (L : LB X) (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB → (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) → (∀ x : X, ∃ i, ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i)) → (∃ (L : LB X') (n : ℕ) (σ : Fin n → LB.Sec L), L.IsLB ∧ (∀ i, IsAffineOpen (Out.nonzeroLocus (σ i))) ∧ ⨆ i, Out.nonzeroLocus (σ i) = ⊤) := by
  rintro G _ _ X Y ρ π H _ L n σ - haff hcov
  classical
  have := Fintype.ofFinite G
  obtain ⟨-, hsurj, -, -, hst⟩ := quotient_isIntegral_surjective_orbits G X Y ρ π H
  have h : IsAffineQuotient ρ π :=
    ⟨H.2.1, H.1, fun W => (H.2.2 W).1, fun W s hs => (H.2.2 W).2 s fun g _ => (hs g).2⟩
  let W : Fin n → X.Opens := fun i => ⨅ g, (ρ g).asIso.hom ⁻¹ᵁ Out.nonzeroLocus (σ i)
  have hW (i x) : x ∈ W i ↔ ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
    change x ∈ ((W i : X.Opens) : Set X) ↔ _
    simp only [W, Opens.coe_iInf, Set.mem_iInter]
    rfl
  choose V hV using fun i => hst (W i) fun k => by
    ext x
    change (ρ k).asIso.hom x ∈ W i ↔ x ∈ W i
    simp only [hW, ← aut_map_mul_apply]
    exact ⟨fun e g => by simpa using e (g * k⁻¹), fun e g => e _⟩
  have hm (i x) : π x ∈ V i ↔ ∀ g, (ρ g).asIso.hom x ∈ Out.nonzeroLocus (σ i) := by
    rw [← hW, ← hV]; rfl
  choose r hr using fun i j => AmpleSpan.exists_isRatio (σ j) (σ i)
  choose a ha using fun i j => exists_norm h (W := V i) (D := Out.nonzeroLocus (σ i)) (fun g x hx => (hm i x).1 hx g) (r i j)
  have top : ⨆ i, V i = ⊤ := top_le_iff.1 fun y _ => by
    obtain ⟨x, rfl⟩ := π.surjective y
    obtain ⟨i, hi⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨i, (hm i x).2 hi⟩
  have hc (i j k) (f : X ⟶ X) (x : X) (hi : f x ∈ Out.nonzeroLocus (σ i)) (hj : f x ∈ Out.nonzeroLocus (σ j)) :
      gs f x _ (r i k) = gs f x _ (r i j) * gs f x _ (r j k) := by
    obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
    refine ((mem_nonzeroLocus_iff_pull _ f x hl).1 hi).mul_right_cancel ?_
    rw [← (hr i k).gs f x hi hl, (hr j k).gs f x hj hl, (hr i j).gs f x hi hl]
    ring
  obtain ⟨L', σ', hL', hσ'⟩ := exists_lb_of_cocycle V top a
    (fun i => eq_of_gs h fun x hx => by
      rw [ha i i x hx, AmpleSpan.gs_one' _ _ _ hx]
      refine Finset.prod_eq_one fun g _ => ?_
      have hi := (hm i x).1 hx g
      obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hi
      refine ((mem_nonzeroLocus_iff_pull _ _ x hl).1 hi).mul_right_cancel ?_
      rw [← (hr i i).gs _ x hi hl, _root_.one_mul])
    (fun i j y hy => by
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : π x ∈ V i := Y.basicOpen_le _ hy
      have u := (LBGerm.isUnit_gs_iff π x _ hx _).2 hy
      rw [ha i j x hx, IsUnit.prod_univ_iff] at u
      refine (hm j x).2 fun g => ?_
      have := (LBGerm.isUnit_gs_iff _ x _ ((hm i x).1 hx g) _).1 (u g)
      rw [(hr i j).basicOpen] at this
      exact this.2)
    (fun i j k => eq_of_gs h fun x hx => by
      rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, ha i k x hx.1, ha i j x hx.1,
        ha j k x hx.2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun g _ => hc i j k _ x ((hm i x).1 hx.1 g) ((hm j x).1 hx.2 g))
  refine ⟨L', n, σ', hL', fun i => ?_, by simp only [hσ', top]⟩
  rw [hσ']
  refine h.isAffineOpen_of_preimage ?_
  rw [hV]
  exact IsAffineOpen.iInf fun g => (haff i).preimage (ρ g).asIso.hom

end GlobalTheory.QuotientNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_local_on_base_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → (∀ i, Out.Sym (G i) (M i)) → Out.Sym A L := by
  first | exact @GlobalTheory.CoverGlue.sym_of_cover | exact GlobalTheory.CoverGlue.sym_of_cover | (intros; apply GlobalTheory.CoverGlue.sym_of_cover <;> assumption)
end

