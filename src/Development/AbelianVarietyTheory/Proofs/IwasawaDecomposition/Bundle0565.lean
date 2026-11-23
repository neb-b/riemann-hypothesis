module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationCharMapEqOnEvenCharacters
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.SqCompare


open GlobalTheory.CoordCompare GlobalTheory.PrimNorm GlobalTheory.MulPull in
theorem sq_law {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {M : LB A.left} (hM : M.IsLB)
    (hT : ∃ t : LB.Gen (Theta A M), t.IsGen) {Y : Over S} (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A)
    (v : LB.Gen (LB.LinComb M (diffφ y a b) ![2, -2, 2, -2])) (hv : v.IsGen) :
    ∃ v' : LB.Gen (LB.LinComb M (diffφ y (a * a) (b * b)) ![1, -1, 1, -1]), v'.IsGen := by
  have hc := fun p q s : Y ⟶ A => diff₃_ptCls (T := Y) hM hT p q s
  have h := (hasGen_iff hM _ _).1 ⟨v, hv⟩
  rw [Fin.prod_univ_four] at h
  refine (hasGen_iff hM _ _).2 ?_
  rw [Fin.prod_univ_four]
  set m := ptCls M Y with hm
  set α := toUnit Y ≫ a
  set β := toUnit Y ≫ b
  have cα : toUnit Y ≫ (a * a) = α * α := MonObj.comp_mul _ _ _
  have cβ : toUnit Y ≫ (b * b) = β * β := MonObj.comp_mul _ _ _
  change m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ) = 1 at h
  change m (y * (toUnit Y ≫ (b * b))) ^ (1 : ℤ) * m (y * (toUnit Y ≫ (a * a))) ^ (-1 : ℤ) *
    m (toUnit Y ≫ (a * a)) ^ (1 : ℤ) * m (toUnit Y ≫ (b * b)) ^ (-1 : ℤ) = 1
  rw [cα, cβ]
  have kα := diff₂_mul_right hc y α α
  have kβ := diff₂_mul_right hc y β β
  calc _ = (diff₂ m y (β * β) * (diff₂ m y β * diff₂ m y β)⁻¹) *
        (diff₂ m y (α * α) * (diff₂ m y α * diff₂ m y α)⁻¹)⁻¹ *
        (m (y * β) ^ (2 : ℤ) * m (y * α) ^ (-2 : ℤ) * m α ^ (2 : ℤ) * m β ^ (-2 : ℤ)) := by
        apply Additive.ofMul.injective
        simp only [diff₂, ofMul_mul, ofMul_inv, ofMul_zpow]
        abel
    _ = 1 := by rw [← kα, ← kβ, h, mul_inv_cancel, mul_inv_cancel, inv_one, _root_.mul_one, _root_.mul_one]


open GlobalTheory.CoordCompare TorusCoord in
theorem sq_desc {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D' e G)
    (Φ : D'.P.A ⟶ D.P.A) [IsMonHom Φ] [Mono Φ.left] (hp : g'.pG ≫ Φ = g.pG)
    (w : LB.Iso (LB.LinComb D'.P.L (K := Fin 1) (fun _ => 𝟙 D'.P.A.left) (fun _ => 2))
      ((LB.LinComb D.P.L (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => 2)).pull Φ.left)) (hw : w.IsGen)
    (χ : D.X) (χ' : D'.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ)) ![2, -2, 2, -2]), v.IsGen := by
  obtain ⟨t, ht, W, hW⟩ := GlobalTheory.T.exists_square_generator_through_squareIso D.P.isLB D'.P.isLB w hw (D'.Oφ g'.pG χ') Oinvε (g'.t χ') (g'.t_gen χ')
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) (ε' := ![2, -2, 2, -2])
    (fun U _ h => by
      have e2 := prod_diff (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) ((Over.map (thick R I e)).map g.q) h
      have e3 : ∏ k, h (g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^ (![2, -2, 2, -2] : Fin 4 → ℤ) k =
          (∏ k, h (((Over.map (thick R I e)).map g.q).left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) ^
            (![1, -1, 1, -1] : Fin 4 → ℤ) k) ^ (2 : ℤ) := by
        simp only [Fin.prod_univ_four, mul_zpow, ← zpow_mul]
        rfl
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (e3.trans (congrArg (· ^ (2 : ℤ)) e2)).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, Oφ_comp_hom, hp, Fintype.prod_sum_type]
      simp only [Fin.prod_univ_four]
      let T := (Over.map (thick R I e)).obj (thickObj R I e G)
      show h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left ^ (2 * (-1 : ℤ)) * h (toUnit T ≫ D'.c χ' ≫ Φ).left ^ (2 * (1 : ℤ)) *
          h g.pG.left ^ (2 * (1 : ℤ)) * h (1 : T ⟶ D.P.A).left ^ (2 * (-1 : ℤ)) *
        ((h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ)) *
         (h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ))) =
        (h (g.pG * (toUnit T ≫ D.c χ)).left * (h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left)⁻¹ *
          h (toUnit T ≫ D'.c χ' ≫ Φ).left * (h (toUnit T ≫ D.c χ).left)⁻¹) ^ (2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t χ)) (LB.invGen D.P.L _ _ (g.t χ))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))
      (DVR.invGen_isGen _ _ _ _ (g.t_gen χ))))
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
    obtain ⟨h₁, h₂⟩ := ratio_invariant g g' Φ hp χ χ' hker r r' z J J' hJ hJ' h
    have hWeq : (fun k => r ≫ D'.Oφ g'.pG χ' k) = (fun k => r' ≫ D'.Oφ g'.pG χ' k) :=
      funext (Oφ_congr χ' g'.pG r r' h₁)
    rw [hu' Z r z J hJ, hu' Z r' z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv,
      hW Z r z J J' hJ hJ', hW Z r' z J J' hJ hJ', hWeq]
    calc _ = W Z z (fun k => r' ≫ D'.Oφ g'.pG χ' k) J J' *
          (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) ^ 2 := by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel
      _ = _ := by
          rw [h₂]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_pow]
          abel)
  exact ⟨v, hv⟩

end GlobalTheory.SqCompare


open GlobalTheory.CoordCompare in
theorem GlobalTheory.SqCompare.c_two_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' hL Φ w hw hΦ hpG xe hval x
  obtain ⟨hN, -, hC, -⟩ := hR
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hpG e)
  have hmono : Mono Φ.hom.left := inferInstance
  set a := D'.toPre.c x ≫ Φ.hom
  set b := D.toPre.c (xe x)
  have desc : ∀ n, ∃ v : LB.Gen (LB.LinComb D.toPre.P.L
      (diffφ (D.toPre.prBe (maximalIdeal R) n) (a * a) (b * b)) ![1, -1, 1, -1]), v.IsGen := fun n => by
    obtain ⟨v, hv⟩ := GlobalTheory.SqCompare.sq_desc (U.gt n) (U'.gt n) Φ.hom (hp' n) w hw (xe x) x
      (fun Z r z J J' hJ hJ' h h' => hval n Z r z J J' hJ hJ' h h' x)
    exact GlobalTheory.SqCompare.sq_law D.toPre.P.isLB ⟨D.toPre.cub.t, D.toPre.cub.isGen⟩ _ _ _ v hv
  have hab : a * a = b * b := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
      D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ (a * a)) (toUnit _ ≫ (b * b)) fun n => by
        obtain ⟨v, hv⟩ := desc n
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
            pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.toPre.P.A] ≫ ·) h
  have e1 : D'.toPre.c (2 • x) ≫ Φ.hom = a * a := by
    rw [two_nsmul, D'.toPre.c_add, padd, ← Hom.mul_def, MonObj.mul_comp]
  have e2 : D.toPre.c (xe (2 • x)) = b * b := by
    rw [map_nsmul, two_nsmul, D.toPre.c_add, padd, ← Hom.mul_def]
  rw [e1, e2, hab]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DividesOfNormBoundedPoints
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Dvd

attribute [local instance] Over.cartesianMonoidalCategory

section Algebra

variable {R : Type} [CommRing R]

theorem mk_le_of_finiteType {D : Type} [CommRing D] (σ : D →+* R) (hσ : σ.FiniteType)
    (h : Cardinal.mk D ≤ Cardinal.continuum) : Cardinal.mk R ≤ Cardinal.continuum := by
  letI := σ.toAlgebra
  have : Algebra.FiniteType D R := hσ
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 this
  refine (Cardinal.mk_le_of_surjective hf).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le h ((Cardinal.lt_aleph0_of_finite _).le.trans Cardinal.aleph0_le_continuum)) Cardinal.aleph0_le_continuum

end Algebra

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_opn (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {x : Z.X} (hx : ∀ x' : Z.X, x' ⤳ x → x' = x) :
    x ∈ Z.opn := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.toPre.s
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have ho := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hc
  have hg := hc.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hc)
  have e := hx _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  obtain ⟨y, hy, hyo⟩ := Z.dense.inter_open_nonempty _ ho ⟨_, mem_irreducibleComponent⟩
  have hopen : IsOpen Z.opn := Z.cover ▸ isOpen_iUnion fun a => (Z.U a).1.isOpen
  exact (hg.specializes hy).mem_open hopen hyo

theorem exists_base (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : Z.i.c.V W →+* Γ(Z.X, U), σ.Flat ∧ σ.FiniteType := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.toPre.s := by
    unfold Pre.s
    infer_instance
  have := Z.flat
  let σ : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.toPre.s)).hom
  have e : spMap σ = hU.fromSpec ≫ Z.toPre.s := Spec.map_preimage _
  have h1 : Flat (spMap σ) := by rw [e]; infer_instance
  have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
  exact ⟨σ, (HasRingHomProperty.Spec_iff (P := @Flat)).1 h1, (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2⟩


end Model

end GlobalTheory.HTLine.Dvd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricOnSet
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.EigMet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem gram_eq_of_isMap {σ : c.F →+* ℂ} (G : EigMet Z σ) {y : CxPts (genStr Z) σ} {R : Type} [CommRing R]
    {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {F : EigFrame Z φ x} {ψ : R →+* ℂ} {f f' : EigFrame Z σ (y.1 ≫ genι Z)}
    (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) ψ f) (hf' : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) ψ f') (τ : E →+* ℂ) : G.gram y f' τ = G.gram y f τ := by
  have hc : f.co f' τ = 1 := by
    rw [← f.co_self τ]
    exact EigFrame.co_eq fun i => by rw [hf' τ i, ← hf τ i]; exact f.co_spec f τ i
  rw [G.change y f f' τ, hc, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem eq_comp_evHom {σ : c.F →+* ℂ} {V : (gen Z).affineOpens} {φ : c.F →+* Γ(gen Z, V.1)}
    (hV : LogKS.chart V ≫ genStr Z = spMap φ) {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1) :
    σ = (evHom h).comp φ := by
  have e : spMap σ = spMap ((evHom h).comp φ) := by
    rw [← y.2, ← spMap_evHom h, Category.assoc, hV, ← Spec.map_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem smoothOn_of_locally {σ : c.F →+* ℂ} (G : EigMet Z σ) (S : Set (CxPts (genStr Z) σ))
    (hloc : ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
      (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ y₀ ∈ S,
      y₀ ∈ ptsIn (genStr Z) σ V.1 → ∃ (T : Set (CxPts (genStr Z) σ)) (g : CxPts (genStr Z) σ → ℂ),
        IsOpen T ∧ y₀ ∈ T ∧ (manifold Z σ).SmoothOn T (fun y => (g y).re) ∧
        (manifold Z σ).SmoothOn T (fun y => (g y).im) ∧
        ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
          (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v F embτ basisIdx) (evHom hy) f → G.gram y f τ a b = g y) :
    G.SmoothOn (manifold Z σ) S := by
  classical
  intro V φ F τ a b hV
  have hx : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      y.1 ≫ genι Z = spMap (evHom h) ≫ LogKS.chart V ≫ genι Z := fun h => by
    rw [← Category.assoc, spMap_evHom h]
  have hex : ∀ {y : CxPts (genStr Z) σ} (h : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), (_root_.GlobalTheory.ShFam.EigFrame.IsMap F) (evHom h) f := fun h =>
    F.exists_isMap (evHom h) (eq_comp_evHom hV h) (hx h)
  let g : CxPts (genStr Z) σ → ℂ := fun y =>
    if h : y ∈ ptsIn (genStr Z) σ V.1 then G.gram y (hex h).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
      (_root_.GlobalTheory.ShFam.EigFrame.IsMap F) (evHom hy) f → G.gram y f τ a b = g y := fun y hy f hf => by
    simp only [g, dif_pos hy]
    rw [gram_eq_of_isMap G (hex hy).choose_spec hf τ]
  let ι := {y₀ // y₀ ∈ S ∧ y₀ ∈ ptsIn (genStr Z) σ V.1}
  choose T gl hT hmem hre him hagree using fun j : ι => hloc V φ F τ a b hV j.1 j.2.1 j.2.2
  have hc : ∀ y ∈ S ∩ ptsIn (genStr Z) σ V.1, ∃ j, y ∈ T j := fun y hy => ⟨⟨y, hy⟩, hmem _⟩
  have heq : ∀ j, ∀ y ∈ (S ∩ ptsIn (genStr Z) σ V.1) ∩ T j, g y = gl j y := fun j y hy =>
    (hg y hy.1.2 _ (hex hy.1.2).choose_spec).symm.trans (hagree j y hy.2 hy.1.2 _ (hex hy.1.2).choose_spec)
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun j => ((hre j).mono Set.inter_subset_right).congr fun y hy => ?_,
    AnRead.smoothOn_of_cover hT hc fun j => ((him j).mono Set.inter_subset_right).congr fun y hy => ?_,
    fun y _ hy f hf => hg y hy f hf⟩
  · exact congrArg Complex.re (heq j y hy)
  · exact congrArg Complex.im (heq j y hy)

end GlobalTheory.ShFam.EigMet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.HodgeOnDomain

attribute [local instance] Over.cartesianMonoidalCategory

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem eigGram_transport {σ : c.F →+* ℂ} (M : EigMet Z σ) {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    M.gram p F τ = Tᴴ * M.gram q G τ * T := by
  subst e
  rw [M.change p G F τ, EigFrame.co_eq h]

theorem eigGram_of_comb {σ : c.F →+* ℂ} (M : EigMet Z σ) (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x)
    (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    M.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * M.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine eigGram_transport M (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

theorem eq_of_conj_eq_one {n : Type} [Fintype n] [DecidableEq n] {W P : Matrix n n ℂ} (hW : IsUnit W.det)
    (h : Wᴴ * P * W = 1) : P = (W⁻¹)ᴴ * W⁻¹ := by
  have hW' : IsUnit Wᴴ.det := by rw [det_conjTranspose]; exact hW.star
  calc P = (Wᴴ)⁻¹ * (Wᴴ * P * W) * W⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hW',
          Matrix.one_mul]
    _ = (W⁻¹)ᴴ * W⁻¹ := by rw [h, Matrix.mul_one, conjTranspose_nonsing_inv]

theorem smul_submatrix_sq {m n : Type} (a : ℂ) (M : Matrix n n ℂ) (e : m → n) :
    (a • M).submatrix e e = a • M.submatrix e e := rfl

end GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeOnDomain

end GlobalTheory.HodgeOnDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionCompIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Member

theorem isEtaleCompletion_comp_bijective' {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion φ) : IsEtaleCompletion (φ.comp e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨RingHom.Flat.comp (RingHom.Flat.of_bijective he) h1, ?_, ?_⟩
  · rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
    exact h2
  · rw [← RingHom.comp_assoc]
    exact RingHom.Finite.comp h3 (RingHom.Finite.of_surjective e he.2)

theorem isEtaleCompletion_stalkClosedPointTo_comp_iso : ∀ {R : Type} [CommRing R] [IsLocalRing R] {X Y : Scheme.{0}} (ξ : Spec (CommRingCat.of R) ⟶ X) (g : X ⟶ Y) [IsIso g], IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → IsEtaleCompletion (Scheme.stalkClosedPointTo (ξ ≫ g)).hom := by
  intro R _ _ X Y ξ g _ h
  have hb : Function.Bijective (g.stalkMap (ξ (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp]
  exact isEtaleCompletion_comp_bijective' _ hb _ h

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 1 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

end GlobalTheory.CdvrExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqTransport


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  intro R _ _ _ hCN G _ _ _ D D' A A' U U' wL hwL σ
  have hR := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  haveI : IsNoetherianRing R := hR.1
  have hL := linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  let σ' : H0 U'.LG.L 2 := secOfIso σ hwL hL' hL
  obtain ⟨s, hs⟩ := exists_sec U'.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ' (pullback.fst G.hom (jK R)))
  obtain ⟨E, hsE, -⟩ := (U'.expand 2 (by norm_num)).1 s
  obtain ⟨f', hf', -⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D' A' G U'.toUnifPre 2 σ' s
    (SectionScalarValuation.secScal_of_sval U'.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  refine ⟨σ', f', hf', fun Z r z J J' hJ hJ' => ?_⟩
  have hm : r z ∈ (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J' r) ⊓
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J r) :=
    ⟨Set.mem_iInter.2 fun _ => hJ' r, Set.mem_iInter.2 fun _ => hJ r⟩
  have e := gs_secOfIso_eq wL σ hwL hL' hL (fun _ => J' r) (fun _ => J r) r z hm
  rw [sval_of σ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id]),
    sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
  show _ = (gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r)))).val * _
  have e' : gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J' r) (σ'.f fun _ => J' r) =
      ((gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r))))⁻¹).val *
        gs r z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J r) (σ.f fun _ => J r) := e
  rw [e', ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end GlobalTheory.SqTransport
end
end

