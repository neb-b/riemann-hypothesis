module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorsDescent

theorem descend_point {K : Type} [Field K] [CharZero K] (X : Scheme.{0}) [IsAffine X]
    (f : Sp (AlgebraicClosure K) ⟶ X)
    (hf : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, spMap σ.toAlgHom.toRingHom ≫ f = f) :
    ∃ g : Sp K ⟶ X, spMap (algebraMap K (AlgebraicClosure K)) ≫ g = f := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (f ≫ X.isoSpec.hom)
  have hfix : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) a, σ (φ a) = φ a := by
    intro σ a
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom σ.toAlgHom.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, ← Category.assoc]
      exact congrArg (· ≫ X.isoSpec.hom) (hf σ)
    exact congrArg (fun g => g.hom a) (Spec.map_injective h1)
  have hmem : ∀ a, φ a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    intro a
    have hb := InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))
    have h2 : φ a ∈ IntermediateField.fixedField (⊥ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ _ => hfix σ a
    rw [hb] at h2
    exact IntermediateField.mem_bot.1 h2
  let jb := algebraMap K (AlgebraicClosure K)
  let e := RingEquiv.ofBijective jb.rangeRestrict
    ⟨fun a b h => jb.injective (congrArg Subtype.val h), jb.rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* K := e.symm.toRingHom.comp (φ.hom.codRestrict jb.range hmem)
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom jb = φ := by
    ext r
    exact congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict jb.range hmem r))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_⟩
  rw [← Category.assoc, spMap, ← Spec.map_comp, hψ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem torsRat_of_retract_galoisFixed : ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G' ≅ A.A) (inc : G ⟶ G') (pr : G' ⟶ G) (n : ℕ), IsMonHom gen.hom → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → 1 ≤ n → (∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (x : Over.mk (spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ jK R) ⟶ G), x ^ n = 1 → spMap σ.toAlgHom.toRingHom ≫ x.left = x.left) → TorsRat G n := by
  have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
      {X : Scheme} (y y' : Sp K ⟶ X)
      (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
    obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
    have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
        spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
          (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
      intro q ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
    rw [e, e] at h
    have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h2
    obtain ⟨rfl, h3⟩ := h2
    have h4 : φ = φ' := by
      have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
      ext x
      apply gam.injective
      have := congrArg (fun f => f.hom x) h5
      simpa using this
    rw [h4]
  intro R _ _ _ G _ _ G' _ _ A gen inc pr n hgen hinc hpr hret hn hfix
  haveI := hgen
  haveI := hinc
  haveI := hpr
  intro Ω _ _ κ x hx
  letI : Algebra (FractionRing R) Ω := κ.toAlgebra
  let jb := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))
  let i₁ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hκ : κ = i₁.toRingHom.comp jb := by
    ext a
    exact (i₁.commutes a).symm
  have hκs : spMap κ = spMap i₁.toRingHom ≫ spMap jb := by
    rw [hκ, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hip : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hret, Over.id_left]

  have hpb := isGrpPullback_pullback G' (jK R)
  let T : Over (Sp (FractionRing R)) := Over.mk (spMap κ)
  let x1 : Over.mk (T.hom ≫ jK R) ⟶ G' := x ≫ inc
  have hx1 : x1 ^ n = 1 := by
    show (x ≫ inc) ^ n = 1
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2 : x2 ^ n = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G'.hom (jK R) = x.left ≫ inc.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ n = 1 := by rw [← MonObj.pow_comp, hx2, MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A n = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t : T ⟶ torsion A.A n := pullback.lift x3 (toUnit _) hmul
  have ht : t ≫ torsion.ι A.A n = x3 := pullback.lift_fst _ _ _

  have hfin := (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb n hn).1
  obtain ⟨K', _, _, _, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A n) hfin
  let i' : K' →ₐ[FractionRing R] AlgebraicClosure (FractionRing R) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra K' (AlgebraicClosure (FractionRing R)) := i'.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (AlgebraicClosure (FractionRing R)) :=
    IsScalarTower.of_algebraMap_eq fun a => (i'.commutes a).symm
  obtain ⟨w, hw⟩ := H (AlgebraicClosure (FractionRing R)) Ω i₁.toRingHom t.left (by
    rw [Over.w t]
    show spMap κ = _
    rw [hκ])
  have hw2 : w ≫ (torsion A.A n).hom = spMap jb := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hw, Over.w t]
    exact hκs
  let Tb : Over (Sp (FractionRing R)) := Over.mk (spMap jb)
  let t₀ : Tb ⟶ torsion A.A n := Over.homMk w hw2
  let g₀ : Tb ⟶ (Over.pullback (jK R)).obj G' := t₀ ≫ torsion.ι A.A n ≫ gen.inv
  let y₁ := ObjPull.pushEquiv hpb Tb g₀
  have hy₁l : y₁.left = w ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R) := by
    rw [ObjPull.pushEquiv_left]
    simp only [g₀, t₀, Over.comp_left, Over.homMk_left, Category.assoc]
  have hkey : spMap i₁.toRingHom ≫ y₁.left = x.left ≫ inc.left := by
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    rw [hy₁l, ← Category.assoc, hw, ← hx2l, ← Category.assoc, ← Over.comp_left, ht]
    show (x2.left ≫ gen.hom.left) ≫ gen.inv.left ≫ _ = _
    rw [Category.assoc, ← Category.assoc gen.hom.left, hgh, Category.id_comp]

  let y₀ : Over.mk (Tb.hom ≫ jK R) ⟶ G := y₁ ≫ pr
  have hy₀ : y₀ ^ n = 1 := by
    have h0 : (t₀ ≫ torsion.ι A.A n) ≫ mulN A.A n = toUnit _ ≫ η := by
      have hc : torsion.ι A.A n ≫ mulN A.A n = pullback.snd (mulN A.A n) η[A.A] ≫ η := pullback.condition
      rw [Category.assoc, hc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id] at h0
    have h1 : g₀ ^ n = 1 := by
      show (t₀ ≫ torsion.ι A.A n ≫ gen.inv) ^ n = 1
      rw [← Category.assoc, ← MonObj.pow_comp, h0, ← Hom.one_def, MonObj.one_comp]
    show (y₁ ≫ pr) ^ n = 1
    rw [← MonObj.pow_comp, ← map_pow, h1, map_one, MonObj.one_comp]
  have hy₁inc : y₁.left ≫ pr.left ≫ inc.left = y₁.left := by
    refine spec_map_field_cancel i₁.toRingHom _ _ ?_
    rw [← Category.assoc, hkey, Category.assoc, reassoc_of% hip]
  have hy₁fix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ y₁.left = y₁.left := by
    intro σ
    calc spMap σ.toAlgHom.toRingHom ≫ y₁.left = spMap σ.toAlgHom.toRingHom ≫ (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [Category.assoc, hy₁inc]
      _ = (y₁.left ≫ pr.left) ≫ inc.left := by
          rw [← Category.assoc]
          exact congrArg (· ≫ inc.left) (hfix σ y₀ hy₀)
      _ = y₁.left := by rw [Category.assoc, hy₁inc]
  haveI : Mono (torsion.ι A.A n) := inferInstanceAs (Mono (pullback.fst _ _))
  have hwfix : ∀ σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R),
      spMap σ.toAlgHom.toRingHom ≫ w = w := by
    intro σ
    have hσ : spMap σ.toAlgHom.toRingHom ≫ Tb.hom = Tb.hom := by
      show spMap _ ≫ spMap jb = spMap jb
      rw [spMap, spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact σ.commutes a
    let eσ : Tb ⟶ Tb := Over.homMk (spMap σ.toAlgHom.toRingHom) hσ
    have h1 : eσ ≫ g₀ = g₀ := by
      apply (ObjPull.pushEquiv hpb Tb).injective
      apply Over.OverMorphism.ext
      rw [ObjPull.pushEquiv_left, ObjPull.pushEquiv_left, Over.comp_left, Category.assoc]
      exact hy₁fix σ
    have h2 : eσ ≫ t₀ = t₀ := by
      rw [← cancel_mono (torsion.ι A.A n ≫ gen.inv)]
      simpa only [Category.assoc] using h1
    exact congrArg (fun f => f.left) h2

  haveI := hfin
  haveI : IsAffine (torsion A.A n).left := isAffine_of_isAffineHom (torsion A.A n).hom
  obtain ⟨w₁, hw₁⟩ := descend_point (torsion A.A n).left w hwfix
  have hw₁s : w₁ ≫ (torsion A.A n).hom = 𝟙 _ := by
    refine spec_map_field_cancel jb _ _ ?_
    rw [← Category.assoc, hw₁, hw2, Category.comp_id]
  let z : Sp (FractionRing R) ⟶ G'.left :=
    w₁ ≫ (torsion.ι A.A n).left ≫ gen.inv.left ≫ pullback.fst G'.hom (jK R)
  have hz : z ≫ G'.hom = jK R := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G'.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A n).left,
      Over.w (torsion.ι A.A n), ← Category.assoc w₁, hw₁s, Category.id_comp]
  refine ⟨Over.homMk z hz ≫ pr, ?_⟩
  have hz' : spMap κ ≫ z = x.left ≫ inc.left := by
    have e1 : spMap κ ≫ z = spMap i₁.toRingHom ≫ y₁.left := by
      show spMap κ ≫ (w₁ ≫ _ ≫ _ ≫ _) = _
      rw [hκs, Category.assoc, ← Category.assoc (spMap jb), hw₁, hy₁l]
    rw [e1, hkey]
  show x.left = spMap κ ≫ z ≫ pr.left
  rw [← Category.assoc, hz', Category.assoc, hip, Category.comp_id]

end GlobalTheory.TorsDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two


open CoordCompare TorusCoord in
theorem exists_level_ratio {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegPre R} {e : ℕ}
    {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
    (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂) (a : thickObj R I e G₁ ⟶ thickObj R I e G₂) [IsMonHom a]
    (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X → D₁.X)
    (t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X)
    (ht : TorusHomOf h t) (hi : g₁.i ≫ a = t ≫ g₂.i) (hq : a ≫ g₂.q = g₁.q ≫ (Over.pullback (thick R I e)).map b)
    (χ : D₂.X) :
    ∃ u : LB.Gen (LB.LinComb (JN D₁ D₂) (Y := (thickObj R I e D₁.P.A).left)
      (fun k => pullback.fst D₁.P.A.hom (thick R I e) ≫
        Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
      (Sum.elim Oε Oinvε)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
        val (g₂.t χ) (x ≫ a.left) z (rr J) = val (g₁.t (h χ)) x z (rl J) * val u (x ≫ g₁.q.left) z J := by
  have := g₁.q_flat
  have := g₁.q_surj
  have := g₁.q_affine
  have p₁ := isPart_inl D₁.P.L D₂.P.L
  have p₂ := isPart_inr D₁.P.L D₂.P.L
  have hp : (Over.map (thick R I e)).map a ≫ g₂.pG = g₁.pG ≫ b := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g₂.q.left = g₁.q.left ≫ ((Over.pullback (thick R I e)).map b).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst D₂.P.A.hom (thick R I e) =
        pullback.fst D₁.P.A.hom (thick R I e) ≫ b.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D₂.Oφ g₂.pG χ k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₂.Oφ b χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g₂.pG χ k).trans
      ((congrArg (D₂.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g₁.pG b χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D₁.Oφ g₁.pG (h χ) k =
      g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫ D₁.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D₁.Oφ · (h χ) k) (Category.comp_id g₁.pG).symm).trans
      ((WeightPf.Oφ_comp g₁.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen (jn_isLB D₁ D₂)
    (φ' := fun k => g₁.q.left ≫ pullback.fst D₁.P.A.hom (thick R I e) ≫
      Sum.elim (fun k => D₁.Oφ (𝟙 _) (h χ) k ≫ coprod.inl) (fun k => D₂.Oφ b χ k ≫ coprod.inr) k)
    (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · refine congrArg₂ (· ^ ·) (congrArg f ?_) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
        exact (congrArg (· ≫ coprod.inl) (e₂ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))
      · refine congrArg (fun ψ => f ψ ^ Oinvε k) ?_
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ coprod.inr) (e₁ k)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _)))))
    (LB.mulGen (JN D₁ D₂) _ _ _ _ (LB.invGen (JN D₁ D₂) _ _ (p₁.gen (g₁.t (h χ))))
      (LB.pullGen (JN D₁ D₂) _ _ (p₂.gen (g₂.t χ)) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (p₁.gen_isGen (g₁.t_gen _)))
      (pullGen_isGen _ _ _ _ (p₂.gen_isGen (g₂.t_gen χ)) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁ D₂) z J →
      val u r z J = (val (g₁.t (h χ)) r z (rl J))⁻¹ * val (g₂.t χ) (r ≫ a.left) z (rr J) := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((Geo.Tor.val_inv _ _).trans (congrArg (·⁻¹) (p₁.val_gen _ _ z hJ)))
        ((Geo.Tor.val_pull hJ _ _ _).trans (p₂.val_gen _ _ z hJ))))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq (jn_isLB D₁ D₂) _ _ g₁.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁).hom := by
      rw [← Over.w g₁.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G₁).hom)
    let c : Z' ⟶ thickObj R I e G₁ := Over.homMk r hw
    let c' : Z' ⟶ thickObj R I e G₁ := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g₁ c c' (Over.OverMorphism.ext hr)
    have hτa : c ≫ a = ((τ ≫ t) ≫ g₂.i) * (c' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g₁ (h χ) (Z := Z') (p₁.good hJ) τ c'
    have v₂ := val_torus g₂ χ (Z := Z') (p₂.good hJ) (τ ≫ t) (c' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D₂.X χ) = gm τ.left z ⊤ (charUnit _ D₁.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

theorem prod_unit_hom {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {B : Over (Sp R)} [GrpObj B] (p : B ⟶ D.P.A)
    [IsMonHom p] (χ : D.X) {U : Type} [CommGroup U] (h : (Spec (CommRingCat.of R) ⟶ D.P.A.left) → U) :
    ∏ k, h (eSec B ≫ D.Oφ p χ k) ^ Oinvε k = 1 := by
  have e0 : ∀ k, eSec B ≫ D.Oφ p χ k = eSec D.P.A ≫ D.Oφ (𝟙 _) χ k := fun k =>
    (WeightPf.Oφ_comp η[B] p χ k).trans ((congrArg (D.Oφ · χ k)
      ((IsMonHom.one_hom p).trans (Category.comp_id _).symm)).trans (WeightPf.Oφ_comp η[D.P.A] (𝟙 _) χ k).symm)
  simp only [e0]
  exact (EndData.prod_unit D (𝟙 _) χ h).2


open EndData in
theorem coord_of_lin : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h ⟨ha, hb, hq, hh⟩ χ
  have hC := hR.2.2.2
  have hB := jn_isLB D₁.toPre D₂.toPre
  have p₁ := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have p₂ := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  choose t ht hi using hh
  choose v hv vv using fun e => exists_level_ratio (U₁.gt e) (U₂.gt e) ((Over.pullback (thick R I e)).map a) b h (t e)
    (ht e) (hi e) (hq e) χ
  have down₁ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good D₁.toPre.P.L z J →
      val ((U₁.gt (e + 1)).t χ) (r ≫ thickMap R I e G₁) z J = val ((U₁.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₁.gt_t e χ) r)
  have down₂ : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (J), Good D₂.toPre.P.L z J →
      val ((U₂.gt (e + 1)).t χ) (r ≫ thickMap R I e G₂) z J = val ((U₂.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U₂.gt_t e χ) r)
  obtain ⟨u, hu, uv⟩ := _root_.GlobalTheory.Unif.exists_gen_of_thick R I hC D₁.toPre.P.A D₁.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D₁.toPre.P (IsPullback.id_horiz _)) _ (JN D₁.toPre D₂.toPre) _ _ _ _ hB
    (fun _ _ => rfl) v hv (fun e z J hJ => by
      have := (U₁.gt e).q_flat
      have := (U₁.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U₁.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv (e + 1) _ (𝟙 _ ≫ thickMap R I e G₁) x J hJ
        have k₀ := vv e _ (𝟙 _) x J hJ
        rw [down₁ _ _ _ _ _ _ (p₁.good hJ), Category.assoc, trans_map, ← Category.assoc,
          down₂ _ _ _ _ _ _ (p₂.good hJ), k₀, Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨u, ⟨hu, fun Z r z J hJ => ?_⟩, fun e Z x z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (t' := LB.oneGen _)
      (corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm) r).trans (val_one _))
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ hu _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·)
        (Eq.trans ?_ (prod_unit D₁.toPre (𝟙 _) (h χ) (fun ψ => k (ψ ≫ coprod.inl))).1)
        (Eq.trans ?_ (prod_unit_hom D₂.toPre b χ (fun ψ => k (ψ ≫ coprod.inr))))).trans
        ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oε j) (Category.assoc _ _ _).symm
      · exact Finset.prod_congr rfl fun j _ => congrArg (fun ψ => k ψ ^ Oinvε j) (Category.assoc _ _ _).symm
    · have := (U₁.gt e).q_hom
      have k := vv e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G₁).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ (p₂.good hJ),
        TorusCoord.val_unit _ _ (p₁.good hJ), _root_.one_mul, ← uv e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D₁.toPre.P.A) =
        η[thickObj R I e D₁.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val u p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D₁.toPre.P.A).symm).trans k.symm)
  · refine (vv e Z x z J hJ).trans (congrArg (_ * ·) ((uv e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.Mum.Two
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.TorusCoordPull in
theorem isPullPt_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  intro R R' _ _ _ _ ρ D I E hE A' G' _ _ U Y e φ h Z g
  obtain ⟨ξ', hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt e)
    (T := Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)) g rfl
  have hp := Y.rep.1 (Over.mk ((g ≫ φ) ≫ Y.H.hom)) Y.H (Over.homMk (g ≫ φ) rfl) (𝟙 Y.H)
  rw [Category.comp_id] at hp
  set Yξ := Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl) with hYξ
  have hb : ξ'.b.left ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) = 𝟙 Z ≫ Yξ.b.left := by
    rw [hξ.1, Category.assoc, h.1, hp.1, Category.id_comp]
    rfl
  refine ⟨ξ', hξ, hb, fun χ => ?_⟩
  have hψ : ∀ κ : Fin 4, DegPre.gtφT E.toPre _ ξ'.b χ κ ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) =
      𝟙 Z ≫ DegPre.gtφT D _ Yξ.b (hE.xe χ) κ := fun κ => by
    rw [GlobalTheory.TorusCoord.gtφT_eq, GlobalTheory.TorusCoord.gtφT_eq]
    exact Oφ_pull hE Yξ.b ξ'.b (𝟙 Z) hb χ κ
  refine ⟨hψ, maps_of_good ((isGen_iff hE.w).1 hE.w_gen) D.P.isLB E.toPre.P.isLB (ξ'.s χ) (ξ'.isGen χ) _
    (Yξ.isGen _) hψ fun z J J' hJ hJ' => ?_⟩
  have o := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (U.gt e).pG (𝟙 Z) g (by rw [Category.id_comp]; exact hξ.1)).1 χ
  have r1 : val (Yξ.s (hE.xe χ)) (𝟙 Z) z J = val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) (g ≫ φ) z J :=
    (val_corr hJ (hp.2 _) (𝟙 _)).trans ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) r z J) (Category.id_comp _)))
  have r3 : val (ξ'.s χ) (𝟙 Z) z J' = val ((U.gt e).t χ) g z J' :=
    (val_corr hJ' (hξ.2 χ) (𝟙 _)).trans ((val_pull hJ' _ _ _).trans
      (congrArg (fun r => val ((U.gt e).t χ) r z J') (Category.id_comp _)))
  refine r1.trans ((h.2 χ Z g z J J' hJ hJ').trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) r3.symm))
  have ok := o k
  rw [Category.id_comp] at ok
  rw [← ok]
  rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsosCommuteOfCommutatorPairingOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

theorem snd_transl (x : 𝟙_ (Over S) ⟶ G) :
    (snd (𝟙_ (Over S)) G ≫ transl x).left = (Out.translPt G x).left := by
  congr 1
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (snd (𝟙_ (Over S)) G ≫ toUnit G)
    (fst (𝟙_ (Over S)) G), mul_comm]
  rfl

theorem exists_theta (hL : L.IsLB) (x : 𝟙_ (Over S) ⟶ G)
    (φ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (transl x).left] ![1, -1])) (hφ : φ.IsGen) :
    ∃ θ : Out.ThetaGrp G L 1 (𝟙_ (Over S)), θ.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ 𝟙_ (Over S)) (a : Z ⟶ G)
      (z : Z.left) (J), Good L z J → CommutatorPairing.thetaVal θ t a z J = val φ a.left z J := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(snd (𝟙_ (Over S)) G).left, (Out.translPt G x).left]) (ε' := ![1, -1]) (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id]
      rw [← Over.comp_left, snd_transl])
    (LB.pullGen L _ _ φ (snd (𝟙_ (Over S)) G).left) (DVR.pullGen_isGen _ _ _ _ hφ _)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)
  rw [← Over.comp_left, lift_snd]

theorem gen_commute_of_weilIs : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G →
    ∀ (L : LB G.left), L.IsLB → ∀ (x y : 𝟙_ (Over S) ⟶ G)
    (φx : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl x).left] ![1, -1]))
    (φy : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GlobalTheory.UPel.HT.Hecke.transl y).left] ![1, -1])),
    φx.IsGen → φy.IsGen → Out.WeilIs G L 1 x y 1 →
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ φx (LB.pullGen L _ _ φy (GlobalTheory.UPel.HT.Hecke.transl x).left))
      (LB.mulGen L _ _ _ _ φy (LB.pullGen L _ _ φx (GlobalTheory.UPel.HT.Hecke.transl y).left)) := by
  intro S G _ _ hA L hL x y φx φy hx hy hW
  obtain ⟨θx, hθx, ex⟩ := exists_theta hL x φx hx
  obtain ⟨θy, hθy, ey⟩ := exists_theta hL y φy hy
  rw [← hθx, ← hθy] at hW
  have hC := (GlobalTheory.CommutatorPairing.commIsOf_iff hL θx θy 1).1
    ((GlobalTheory.GlobalLift.weilIs_iff_commIsOf GlobalTheory.globalFns_holds hA hL θx θy 1).1 hW)
  refine corr_of_val hL fun g J hJ => ?_
  have h := hC G (toUnit G) (𝟙 G) g J hJ
  rw [map_one, CommutatorPairing.commVal, mul_inv_eq_one, ex _ _ _ _ _ hJ, ex _ _ _ _ _ hJ, ey _ _ _ _ _ hJ,
    ey _ _ _ _ _ hJ] at h
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
  rw [hθx, hθy, show toUnit G ≫ x * 𝟙 G = transl x from mul_comm _ _,
    show toUnit G ≫ y * 𝟙 G = transl y from mul_comm _ _] at h
  exact h

end GlobalTheory.UPel.HT.Hecke
end
end

