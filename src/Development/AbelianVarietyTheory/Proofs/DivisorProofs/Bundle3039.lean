module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

open GlobalTheory.CechPic

theorem principal_zP : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → Out.RelAmple (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) ∧ ∀ (T : Over S) (x : T ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → x = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hunit hK
  refine ⟨?_, fun T x hx => ?_⟩
  · have hAb : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
      (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
    have := hAb.proper
    have hA : Out.RelAmple c.A c.diag := hK.1
    have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ Out.powObj c.A 8,
        ∀ u, x ≫ Out.powPr c.A u = y u := fun T y =>
      ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
        fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
    have h8 := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef GlobalTheory.SemiRigid.globalFns h M 8 _ _ S t c
      (Out.powObj c.A 8) (Out.powPr c.A) (zW d) (fun u => inferInstance) huniv hA (GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef d hd)
    have := GlobalTheory.T.isAffineHom_zarhinProduct_to_eighthPower h M d S t c B Q la mu hZ hd hunit
    have hF : (LB.LinComb c.P (K := Fin 8 × Fin 8)
        (fun uv => (lift (Out.powPr c.A uv.1) (Out.powPr c.A uv.2)).left) (fun uv => zW d uv.1 uv.2)).IsLB :=
      LB.isLB_linComb c.isLB _ _
    have hp := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom (zphi c.A B mu) hF h8
    have hzP := zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
    refine GlobalTheory.PosDefAmple.relAmple_of_nsmul (pull_isLB hzP _) (pull_isLB hF _) (N := d) hd ?_ hp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cls_pull hzP, cls_zP, cls_pull hF, cls_linComb c.isLB, GlobalTheory.T.nsmul_zarhinDiagonalClass_eq_form h M d S t c B Q la mu hZ hd, map_sum]
    refine Finset.sum_congr rfl fun kl _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, zphi_powPr, zphi_powPr]
  · have hla := hZ.2.2.2.1
    have hmu := hZ.2.2.2.2.1
    let f : (T ⟶ c.A) →* (T ⟶ B) := MonoidHom.mk' (fun a => a ≫ la) (fun a b => MonObj.mul_comp a b la)
    let g : (T ⟶ B) →* (T ⟶ c.A) := MonoidHom.mk' (fun a => a ≫ mu) (fun a b => MonObj.mul_comp a b mu)
    have hfg : ∀ a, g (f a) = a ^ d := fun a => by
      change (a ≫ la) ≫ mu = a ^ d
      rw [Category.assoc, hZ.2.2.2.2.2.1, MonObj.comp_pow, Category.comp_id]
    obtain ⟨hu, hv⟩ := GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial d (T ⟶ c.A) (T ⟶ B) f g hd hfg (fun i => x ≫ pa c.A B i) (fun j => x ≫ pb c.A B j)
      (fun i => by simpa [f, Category.assoc] using GlobalTheory.T.zarhinBundle_kernel_firstCoord_equations h M d S t c B Q la mu hZ T x hx i)
      (fun j => GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations h M d S t c B Q la mu hZ T x hx j)
      (GlobalTheory.T.zarhinBundle_kernel_of_secondCoord_trivial h M d S t c B Q la mu hZ T x hx)
    have e1 : x ≫ fst _ _ = 1 := (Out.powIsLimit c.A 4).hom_ext fun ⟨i⟩ => by
      change (x ≫ fst _ _) ≫ Out.powPr c.A i = 1 ≫ Out.powPr c.A i
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hu i)
    have e2 : x ≫ snd _ _ = 1 := (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by
      change (x ≫ snd _ _) ≫ Out.powPr B j = 1 ≫ Out.powPr B j
      rw [MonObj.one_comp]
      exact (Category.assoc _ _ _).trans (hv j)
    ext1
    · rw [e1, MonObj.one_comp]
    · rw [e2, MonObj.one_comp]

end GlobalTheory.ZarhinFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinModelGenericFibreIsPullbackThetaSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

noncomputable section
namespace GlobalTheory.ZH.GenFib

theorem genFib_pullback : ∀ (X₁ : GlobalTheory.GSep.GSet) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (O : ZHOut X₁.ρ Y U₀ EE), X₁.S.Over₀ Y U₀ → ∃ ψ : ((Over.pullback Y.pt).obj O.G).left ⟶ X₁.ρ.P.A.left, IsGrpPullback ((Over.pullback Y.pt).obj O.G) X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) ψ ∧ LBIso (O.L.L.pull (pullback.fst O.G.hom Y.pt)) (X₁.ρ.P.L.pull ψ) ∧ ∀ f : X₁.ρ.P.A ⟶ X₁.ρ.P.A, IsMonHom f → ∃ F : O.G ⟶ O.G, IsMonHom F ∧ ((Over.pullback Y.pt).map F).left ≫ ψ = ψ ≫ f.left := by
  intro X₁ Y U₀ EE O hO
  have hcov := (top_le_preimage_iff _ _).1 (Y.top_le_preimage_pt hO.ne)
  let x : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt (by rw [Scheme.Opens.range_ι]; exact hcov)
  have hx : x ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x ≫ O.u₀ = spMap X₁.S.R.val.toRingHom := O.u₀_gen x hx
  have hc : pullback.fst O.G.hom Y.pt ≫ O.G.hom = (pullback.snd O.G.hom Y.pt ≫ x) ≫ U₀.ι := by
    rw [pullback.condition, Category.assoc, hx]
  let κ : pullback O.G.hom Y.pt ⟶ pullback X₁.ρ.P.A.hom O.u₀ := O.cart.1.lift _ _ hc
  have hκ₁ : κ ≫ O.φ = pullback.fst O.G.hom Y.pt := O.cart.1.lift_fst _ _ hc
  have hκ₂ : κ ≫ ((Over.pullback O.u₀).obj X₁.ρ.P.A).hom = ((Over.pullback Y.pt).obj O.G).hom ≫ x :=
    O.cart.1.lift_snd _ _ hc
  have n : IsGrpPullback ((Over.pullback Y.pt).obj O.G) O.G (x ≫ U₀.ι) (κ ≫ O.φ) :=
    (isGrpPullback_pullback O.G Y.pt).congr hx.symm hκ₁.symm
  have h₁ : IsGrpPullback ((Over.pullback Y.pt).obj O.G) ((Over.pullback O.u₀).obj X₁.ρ.P.A) x κ :=
    O.cart.cancel n hκ₂
  have hP : IsGrpPullback ((Over.pullback Y.pt).obj O.G) X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom)
      (κ ≫ pullback.fst X₁.ρ.P.A.hom O.u₀) :=
    (h₁.comp (isGrpPullback_pullback X₁.ρ.P.A O.u₀)).congr hxu rfl
  refine ⟨κ ≫ pullback.fst X₁.ρ.P.A.hom O.u₀, hP, ?_, ?_⟩
  · exact GlobalTheory.GenSpread.lbIso_pull_comp κ hκ₁.symm rfl ⟨O.w, O.w_gen⟩
  · intro f hf
    obtain ⟨e, he, he'⟩ := grpPullback_iso hP (isGrpPullback_pullback X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom))
    let f' := e.hom ≫ (Over.pullback (spMap X₁.S.R.val.toRingHom)).map f ≫ e.inv
    have hf' : IsMonHom f' := by infer_instance
    obtain ⟨F, ⟨hF, hFf⟩, -⟩ := O.endo f' hf'
    refine ⟨F, hF, ?_⟩
    rw [hFf]
    show (e.hom ≫ (Over.pullback (spMap X₁.S.R.val.toRingHom)).map f ≫ e.inv).left ≫ (κ ≫ pullback.fst X₁.ρ.P.A.hom O.u₀) = _
    have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
    rw [← he']
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie]
    congr 1
    exact pullback.lift_fst _ _ _

end GlobalTheory.ZH.GenFib
end
end

