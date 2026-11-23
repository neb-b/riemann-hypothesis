module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem traitExtSt_of (h₁ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
      GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
        ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
          (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
          ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
            IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
            ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
              IsSemiAbelian G ∧ IsMonHom gen.hom)
    (h₂ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
      [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
      ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
      IsSemiAbelian G → IsMonHom gen.hom →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
          (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
          ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
            (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
            (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
            IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
            LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂'))
    (h₃ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
      ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
        IsMonomial D.toPre ![ϖ] ![β]) : TraitExtSt := by
  intro g n o _ ζ F V _ _ _ hB hD y
  obtain ⟨V₁, _, _, _, f, fK, hC₁, hinj₁, hloc₁, hfin₁, hK₁, A, α, α₂, hcart, hsq, hlb, G, _, _, gen, hsemi, hmon⟩ :=
    h₁ g n o ζ F V hB hD y
  obtain ⟨W, _, _, _, f', fK', hCW, hinj₂, hloc₂, hfin₂, hK₂, G', _, _, D, A', U, α', α₂', hsemi', hcart', hsq', hlb'⟩ :=
    h₂ g n o ζ F V₁ hC₁ (spMap fK ≫ y) A α α₂ hcart hsq hlb G gen hsemi hmon
  obtain ⟨hdvr, hcpl, hchar⟩ := hCW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨β, hβs, hβm⟩ := h₃ W ⟨hdvr, hcpl, hchar⟩ ϖ hϖ D
  have hsp : spMap (fK'.comp fK) = spMap fK' ≫ spMap fK := by
    unfold spMap
    simp
  refine ⟨
    { V := W
      complete := hcpl
      ϖ := ϖ
      irr := hϖ
      y := spMap (fK'.comp fK) ≫ y
      G := G'
      semi := hsemi'
      D := D
      A := A'
      U := U
      α := α'
      α₂ := α₂'
      cart := ?_
      sq := hsq'
      lb := hlb'
      β := β
      symm := hβs
      mono := hβm },
    f'.comp f, fK'.comp fK, hinj₂.comp hinj₁, ?_, hfin₂.comp hfin₁, ?_, rfl⟩
  · rw [hsp, Category.assoc]
    exact hcart'
  · exact RingHom.isLocalHom_comp f' f
  · intro a
    simp [hK₁, hK₂]

theorem traitExtSt : TraitExtSt :=
  traitExtSt_of _root_.GlobalTheory.CExtGen.exists_polAV_semiAbelian _root_.GlobalTheory.PoincUnif.exists_unif_finExt _root_.GlobalTheory.MonPeriods.exists_isMonomial_symm

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem traitInv_eqv_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hem
  obtain ⟨f, hfi, hf1, hf2⟩ := GlobalTheory.T.exists_fibre_iso_genericFibre_cover R hR D C W T F hem
  obtain ⟨lab', hq, hm⟩ := GlobalTheory.T.exists_torsionLabels_genericFibre_trait R hR D C j W T F em hem f hfi hf1 hf2
  have hW := T.cdvr
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have : CharZero R := hR.2
  have hcW : CharZero W := charZero_of_injective_ringHom T.inj
  have hsemi : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨w₀, hw₀⟩ := T.U.ext
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hx⟩ := GlobalTheory.T.exists_equivariant_inverse_thetaExpansion W (maximalIdeal W) hW' hcW T.D' T.A T.G T.U hsemi F (C.n ^ j) hodd w₀ hw₀ lab' hq
  obtain ⟨lab, E, Φ, hlab, hE, hΦ, hrel⟩ := GlobalTheory.T.trait_equivariant_bijection_transport_cover R hR D C j wA hwA W T F em hem f hfi hf1 hf2 w₀ hw₀ lab' hm E' hE'
  refine ⟨lab, E, hlab, hE, ?_⟩
  intro F₀ s σ hs hσ Z p p' hβ hG z J J' hJ hJ'
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt T.U.LG.isLB z
  obtain ⟨Jt, hJt⟩ := GlobalTheory.UU.exists_good_pt T.A.isLB z
  have hq1 : (p' ≫ inv f) ≫ f = p' := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hG' : p ≫ T.G.hom = (p' ≫ inv f) ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [hG, ← hf1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hβ' : p ≫ T.β = (p' ≫ inv f) ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    rw [hβ, ← hf2, Category.assoc, IsIso.inv_hom_id_assoc]
  exact (GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion R hR D C j W T F w₀ hw₀ E' hx F₀ (Φ s) σ (hΦ s F₀ hs) hσ Z p (p' ≫ inv f) hβ' hG' z J JG Jt hJ hJG hJt).trans
    (hrel s Z p p' (p' ≫ inv f) hq1 hβ hG' z J J' JG Jt hJ hJ' hJG hJt).symm

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMember
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMoveSnd

variable {D : D7}

theorem heisO_smul' {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    (a : ℂ) {g₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c g₀ Tm) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (a • g₀) (a • Tm) :=
  { trans := fun Φ hΦ x hx => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul']
    modul := fun Φ hΦ y hy => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul']
    vac := by rw [LinearMap.smul_apply, hT.vac] }

theorem isThetaAt_rescale {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c κ : ℂ}
    {f₀ Φ f : WO S T → ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (κ • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  refine ⟨⟨κ⁻¹ • Tm, ?_⟩, fun Tm' hT' => ?_⟩
  · have := isPlaceModel_smul κ⁻¹ hT
    rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  · rw [hall _ (isPlaceModel_smul κ hT'), LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem isHalf_iff_smul {m n : ℕ} (c : AE D) (u : Mx D m n) : IsHalf c u ↔ c • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem isHalf_actO' {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf c x) :
    IsHalf c (actO S T g h x) := by
  rw [isHalf_iff_smul] at hx ⊢
  rw [GlobalTheory.VacMove.actO_eq]
  conv_rhs => rw [← hx]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_actO_inv_iff {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf c (actO S T g⁻¹ h⁻¹ x) ↔ IsHalf c x := by
  refine ⟨fun hx => ?_, isHalf_actO' c _ _⟩
  have := isHalf_actO' c g h hx
  have e := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) g⁻¹ h⁻¹ x
  simp only [inv_inv] at e
  rwa [e] at this

theorem frame_move_alg {R : Type} [CommRing R] {s t : ℕ} (a βS : GL (Fin s) R) (b βT : GL (Fin t) R)
    (K : Matrix (Fin s) (Fin t) R) :
    ((a * βS)⁻¹ : GL (Fin s) R).1 * K * (b * βT).1 =
      (βS⁻¹).1 * (a⁻¹).1 * βS.1 * ((βS⁻¹).1 * K * βT.1) * ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R).1 := by
  have e1 : (βS.1 : Matrix (Fin s) (Fin s) R) * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : (βT.1 : Matrix (Fin t) (Fin t) R) * (βT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e3 : ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R) = βT⁻¹ * b * βT := by group
  rw [e3, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1 (βS⁻¹).1, e1, Matrix.one_mul, ← Matrix.mul_assoc βT.1 (βT⁻¹).1, e2, Matrix.one_mul]

theorem frMapAdj_move (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D S)
    (h : GA D T) (x : WO S T) :
    frMapAdj S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapAdj S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have split : actO S T g⁻¹ h⁻¹ x = actO S T g⁻¹ 1 (actO S T 1 h⁻¹ x) := by
    simp only [GlobalTheory.VacMove.actO_eq, inv_one, GlobalTheory.VacMove.mt_one₀, Matrix.one_mul, Matrix.mul_one]
  rw [split, GlobalTheory.FreeBlockTwist.frMapAdj_actO_one, GlobalTheory.AdjAct.frMapAdj_actO, ← GlobalTheory.AdjAct.finE_inv_val, ← map_inv]
  unfold frMapAdj
  rw [map_inv (Lev.finE S), map_inv (Lev.finE T), ← Matrix.mul_assoc]
  exact frame_move_alg (R := EAf D) (Lev.finE S g) βS (Lev.finE T h) βT _

theorem stdSnd_move (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    stdSnd ν e I a S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = stdSnd ν e I a S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  unfold stdSnd dualCoord
  rw [frMapAdj_move]
  rw [propext (isHalf_actO_inv_iff (cA D e) g h x)]

theorem snd_moved : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv' t
  have hWe : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := (GlobalTheory.Grid.isWeil_false ψ A' WW _ _ _).1 (hY.weil' t)
  have hee : cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self (hY.idem t)]
  have hinf : infPart D (cA D (Y.e t)) = 0 :=
    GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum (hY.idem t))
  have hm := GlobalTheory.VacMove.isThetaAt_moveLat D ψ A' WW (α t) (α t / β t) (Y.ω' t) hWe Y.rA'.Λ ΛA' Y.rW.Λ ΛW hY.rigA'.1 hA'
    hY.rigW.1 hW g' hg' h hh mA' mW (cA D (Y.e t)) _ Y.vac' (Y.f' t) hee hinf hY.isVac'.2.theta
    (GlobalTheory.ConstRatio.theta_f hY t).2 (hY.snd t)
  rw [hv' t] at hm
  have hm2 := isThetaAt_rescale (hr t).2 hm
  have hΦ : (fun x => stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β (actO A' WW g'⁻¹ h⁻¹ x)) =
      stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW (Lev.finE A' g' * Y.rA'.β) (Lev.finE WW h * Y.rW.β) :=
    funext fun x => (stdSnd_move _ _ _ _ _ _ _ _ _ _ x).symm
  rw [hΦ] at hm2
  exact hm2

end GlobalTheory.BotMoveSnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombination
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.QuadSum

variable {K : Type} [Field K]

theorem hom_finset_sum {B A : AbVar K} {J : Type} (s : Finset J) (g : J → (B ⟶ A)) :
    Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i ∈ s, g i) = ∏ i ∈ s, (g i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, add_hom, ih]

theorem lam_symm {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  unfold AbVar.lam
  rw [mul_comm x y]
  abel

theorem lam_prod_right {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x : Y ⟶ A.X) {J : Type}
    (s : Finset J) (y : J → (Y ⟶ A.X)) :
    AbVar.lam c x (∏ j ∈ s, y j) = ∑ j ∈ s, AbVar.lam c x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x 1 1 0).2.2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x (y a) _ 0).1, ih]

theorem lam_prod_left {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} {J : Type}
    (s : Finset J) (x : J → (Y ⟶ A.X)) (y : Y ⟶ A.X) :
    AbVar.lam c (∏ i ∈ s, x i) y = ∑ i ∈ s, AbVar.lam c (x i) y := by
  rw [lam_symm, lam_prod_right]
  exact Finset.sum_congr rfl (fun i _ => lam_symm c y (x i))

theorem lam_zpow_zpow {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) (m n : ℤ) :
    AbVar.lam c (x ^ m) (y ^ n) = (m * n) • AbVar.lam c x y := by
  rw [(GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y (x ^ m) y y n).2.2.2.2, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x y y m).2.2.2.1, smul_smul,
    mul_comm n m]

end GlobalTheory.AV.QuadSum

theorem GlobalTheory.AV.QuadSum.pull_sum_smul : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  intro K _ B A c hc n f m
  rw [← (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K B A c hc (∑ i, m i • f i) 1).1, QuadSum.hom_finset_sum, QuadSum.lam_prod_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [QuadSum.lam_prod_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zsmul_hom, zsmul_hom, QuadSum.lam_zpow_zpow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullComplete

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  intro Z G₀ _ _ hG₀ L R _ _ _ hR ξ _ D A U hL hψ V _ _ _ hV ψ hloc hgen
  have hG : IsSemiAbelian ((Over.pullback ξ).obj G₀) := IsSemiAbelian.pullback ξ G₀ hG₀
  have hpb := isGrpPullback_pullback G₀ ξ
  have hab : ξ ⁻¹' abLocus G₀ = abLocus ((Over.pullback ξ).obj G₀) :=
    Set.ext fun x => abLocus_pullback abLocusOne hG₀ hpb.1 x
  let W : (Sp R).Opens := ⟨ξ ⁻¹' abLocus G₀, by rw [hab]; exact GlobalTheory.AbLocusOpen.isOpen_abLocus_local _ hG⟩
  have hz : (jK V).base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hW : spMap ψ (genericPoint (Sp V)) ∈ W := by
    show ξ (spMap ψ (genericPoint (Sp V))) ∈ abLocus G₀
    rw [← hz]
    have := hgen (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    exact this
  let G := (Over.pullback ξ).obj G₀
  let G' := (Over.pullback (specOf ψ)).obj G
  have hbc : IsMonHom (Iso.refl G').hom := by show IsMonHom (𝟙 G'); infer_instance
  obtain ⟨D', A', hD, U', hP⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U V hV.1 ψ hloc W hψ hW
    G' (Iso.refl G') hbc
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback (specOf ψ) G hG
  let β : G'.left ⟶ G.left := (Iso.refl G').hom.left ≫ pullback.fst G.hom (specOf ψ)
  obtain ⟨hLB, hC, hE⟩ := GlobalTheory.Poinc.Eq8.PullUnif.main R hR G hG D A U V hV G' hG' D' A' U' ψ β hloc (Iso.refl G')
    hbc rfl hD hP
  let gm : G'.left ⟶ G₀.left := β ≫ pullback.fst G₀.hom ξ
  have hβ : IsGrpPullback G' G (specOf ψ) β :=
    ((isGrpPullback_of_iso (Iso.refl G')).comp (isGrpPullback_pullback G (specOf ψ))).congr (Category.id_comp _) rfl
  refine ⟨G', inferInstance, inferInstance, D', A', U', gm, hD.xe.symm, hG', hβ.comp hpb, ?_, hC, ?_⟩
  · exact GlobalTheory.LBIsoEnd.lbIso_trans_end _ _ _ _ U'.LG.isLB (pull_isLB U.LG.isLB β) hLB
      (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL β rfl))
  · intro f hf
    haveI := hf
    have e1 : ((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β =
        β ≫ ((Over.pullback ξ).map f).left := by
      show _ ≫ 𝟙 _ ≫ _ = (𝟙 _ ≫ _) ≫ _
      exact pullback.lift_fst _ _ _
    have e2 : ((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ = pullback.fst G₀.hom ξ ≫ f.left :=
      pullback.lift_fst _ _ _
    refine ⟨(Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f), inferInstance, ?_, ?_⟩
    · show _ ≫ β ≫ _ = (β ≫ _) ≫ _
      calc _ = (((Over.pullback (specOf ψ)).map ((Over.pullback ξ).map f)).left ≫ β) ≫ pullback.fst G₀.hom ξ :=
            (Category.assoc _ _ _).symm
        _ = (β ≫ ((Over.pullback ξ).map f).left) ≫ pullback.fst G₀.hom ξ := by rw [e1]
        _ = β ≫ (((Over.pullback ξ).map f).left ≫ pullback.fst G₀.hom ξ) := Category.assoc _ _ _
        _ = β ≫ (pullback.fst G₀.hom ξ ≫ f.left) := by rw [e2]
        _ = _ := (Category.assoc _ _ _).symm
    · intro m m' hm hm' y
      exact hE _ _ inferInstance inferInstance e1 m m' hm hm' y

end GlobalTheory.Poinc.Eq8.PullComplete
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.TorusExt GlobalTheory.Balanced

attribute [local instance] gtGroup


set_option maxHeartbeats 2000000 in
theorem pull_unif_tors : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  intro R _ _ _ J hR D₀ A₀ G₀ _ _ U₀ hG V _ _ _ _ hV f hf hJ
  have hL := GlobalTheory.firstFiveLaws
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨D, hD, A, U, hG', hU, hpt, -⟩ := _root_.GlobalTheory.UT.EndBaseChange.main hL R J hR D₀ A₀ G₀ hG U₀ V f hV hf hJ
  refine ⟨D, hD, A, U, hG', hU, ?_⟩
  intro F₀ _ _ _ F _ _ _ j hj k hk p₀ x₀ hx₀
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  let σ : F₀ →ₐ[FractionRing R] F := { j with commutes' := fun _ => rfl }
  have hB := D₀.tau_bimult
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (f r)) := hj
  obtain ⟨p₁, hp₁⟩ := qkExtExists R D₀.toPre F₀ F σ.toRingHom (fun r => σ.commutes r) k p₀
  let x₁ : TFK (R := R) F ⟶ A₀.A := extPt σ x₀
  have hx₁ : QkToAkU U₀.toUnifPre F k p₁ x₁ := (GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R J hR D₀ A₀ G₀ hG U₀ F₀ F σ k hk p₀ p₁ x₀ x₁
    hp₁ rfl).1 hx₀
  obtain ⟨ex, -, io, ns⟩ := hpt F hF
  obtain ⟨g, hg, -⟩ := ex p₁.g
  let p : QkPt D.toPre F k := ⟨hD.xe.symm p₁.y, g, by
    obtain ⟨s, h1, h2⟩ := p₁.eq
    obtain ⟨s', hs', -⟩ := ex s
    exact ⟨s', (ns k _ _ _ _ hg hs').1 h1, (io _ _ _ hs').1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x, hx⟩ := exists_toG_pull f U₀.toUnifPre U.toUnifPre hF x₁
  refine ⟨p, x, by simpa [p, hp₁.1], ⟨p₁.g, hp₁.2, hg⟩, ?_, ?_⟩
  · exact hL.2.2.2.2.qkBaseChange R V J _ hR hR' f D₀ A₀ G₀ U₀ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A D
      hD U hU F hF k hk p₁ x₁ p x rfl hg
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx) hx₁
  · simpa only [toG, Category.assoc, x₁, extPt, Over.homMk_left] using hx

end GlobalTheory.TInj
end
end

