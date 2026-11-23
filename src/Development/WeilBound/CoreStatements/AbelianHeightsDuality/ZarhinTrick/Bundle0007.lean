module

public import Mathlib
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0006
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FourfoldProductExt

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamC
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)


omit [GrpObj B] in
theorem lam_cL_pt {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (p q : T ⟶ (Over.pullback s).obj A) :
    lam (cls L hL) p q = evc hP (toBase A s p) (toBase A s q ≫ l) := by
  have hLam := GlobalTheory.FullSiegel.isLB_lam (G := (Over.pullback s).obj A) hL
  have hE : (ev P (fst A A) (snd A A ≫ l)).IsLB := LB.isLB_pull hP _
  have hM := LB.isLB_pull hE (sqToBase A s)
  have hc : cls (abelian₂ ((Over.pullback s).obj A) L) hLam = cls _ hM := (cls_eq_iff hLam hM).mpr (LBIso.symm e)
  rw [← GlobalTheory.FullSiegel.cls_lam_pull hL p q, cls_pull hLam, hc, cls_pull hE, cls_ev hP]
  have hw : sqToBase A s = Over.Hom.left (lift (toBase A s (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)))
      (toBase A s (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)))) := rfl
  rw [hw, pull_evc, lift_fst, lift_snd_assoc]
  have e1 := toBase_comp s A (lift p q) (fst _ _)
  have e2 := toBase_comp s A (lift p q) (snd _ _)
  rw [lift_fst] at e1
  rw [lift_snd] at e2
  rw [e1, e2, Category.assoc (Over.homMk _ _) _ l, ← pull_evc]
  rfl

theorem pull_phiP {P : LB (A ⊗ B).left} (hP : P.IsLB) {T : Over (Sp Ω)}
    (v : T ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) (ij : Fin 4 × Fin 4) :
    pull v.left (pull (phiP s ij) (cls P hP)) =
      evc hP (toBase _ s v ≫ prj _ ij.1 ≫ fst A B) (toBase _ s v ≫ prj _ ij.2 ≫ snd A B) := by
  have e1 := toBase_comp s (G4 (A ⊗ B)) v (𝟙 _)
  rw [Category.comp_id] at e1
  rw [evc, e1, ← comp_lift, Category.assoc, Over.comp_left, pull_comp]
  rfl

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FinSurjOfQuasiInverse
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem isFinite_mu_fibre (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (g : ℕ)
    (hgA : SmoothOfRelativeDimension g A.hom) (hgB : SmoothOfRelativeDimension g B.hom) (l : A ⟶ B) [IsMonHom l]
    (mu : B ⟶ A) [IsMonHom mu] (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) : IsFinite ((Over.pullback s).map mu).left :=
  Z2.isFinite_mu_fibre hA hB g hgA hgB l mu m hm h₁ h₂ s L hL ha

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMapG4map
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def fourfoldProductMap {G H : Over S} (h : G ⟶ H) : G4 G ⟶ G4 H := h ⊗ₘ (h ⊗ₘ (h ⊗ₘ h))

theorem isFinite_map_g4map {T : Scheme.{0}} (s : T ⟶ S) {G H : Over S} (h : G ⟶ H)
    (hh : IsFinite ((Over.pullback s).map h).left) : IsFinite ((Over.pullback s).map (fourfoldProductMap h)).left :=
  isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh hh))

variable {Ω : Type} [Field Ω]

theorem isIso_inv_left {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := by
  have e : ((𝟙 G)⁻¹ : G ⟶ G) ≫ (𝟙 G)⁻¹ = 𝟙 G := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G) := ⟨⟨(𝟙 G)⁻¹, e, e⟩⟩
  exact (Over.forget (Sp Ω)).map_isIso ((𝟙 G)⁻¹ : G ⟶ G)

theorem relAmple_sym {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (ha : Out.RelAmple G L) :
    Out.RelAmple G (LB.LinComb L (K := Fin 2) ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]) := by
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := isIso_inv_left
  haveI : IsAffineHom ((𝟙 G)⁻¹ : G ⟶ G).left := inferInstance
  have hLi : Out.RelAmple G (L.pull ((𝟙 G)⁻¹ : G ⟶ G).left) :=
    GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom _ hL ha
  have hN := LB.isLB_linComb (K := Fin 2) hL ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]
  refine GlobalTheory.relAmple_of_isAmpleLB G hN (fun U hU => ?_)
  have hP := LB.isLB_pull hL ((𝟙 G)⁻¹ : G ⟶ G).left
  have h1 := GlobalTheory.isAmpleLB_of_relAmple G hL ha U hU
  have h2 := GlobalTheory.isAmpleLB_of_relAmple G hP hLi U hU
  have a1 := LB.isLB_pull hN (G.hom ⁻¹ᵁ U).ι
  have a2 := LB.isLB_pull hL (G.hom ⁻¹ᵁ U).ι
  have a3 := LB.isLB_pull hP (G.hom ⁻¹ᵁ U).ι
  have a4 := LB.isLB_div a1 a2
  have a5 := LB.isLB_div a4 a3
  refine GlobalTheory.IsAmpleLB.tensor h1 h2 a1 ?_
  rw [← cls_eq_zero_iff a5, cls_div a4 a3 a5, cls_div a1 a2 a4, cls_pull hN _ a1, cls_pull hL _ a2,
    cls_pull hP _ a3, cls_pull hL _ hP, cls_linComb hL _ _ hN]
  simp [Fin.sum_univ_two, pull_id]

end PositivityTheory.PrwZar.XB
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfTwoSmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_two_smul {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M N : LB G.left}
    (hM : M.IsLB) (hN : N.IsLB) (d : ℕ) (hd : 1 ≤ d) (e : d • cls M hM = d • cls N hN) (h : Out.RelAmple G N) :
    Out.RelAmple G M :=
  Z2.relAmple_of_two_smul hG hM hN d hd e h

end PositivityTheory.PrwZar
end
end

