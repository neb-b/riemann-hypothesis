module

public import Formalism.AdmissibleDesigns.Bundle0011
public import Formalism.AdmissibleDesigns.Bundle0003
public import Formalism.AdmissibleDesigns.DesignNormalizedOfAdmitted
public import Formalism.AdmissibleDesigns.URecApply

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.SelmerInequalityOpen
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.St

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Places

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem col_not_row (l : Col i dc) : colIdx i dc l ∉ rowsN i dc := by
  intro h
  simp only [rowsN, colIdx, Finset.mem_image] at h
  obtain ⟨v, hv, hvi⟩ := h
  have hl : (l : HeightOneSpectrum (𝓞 D.host.E)) ∈ dc.col := l.2
  have hvl : v = l := idx_inj i dc (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
    (Finset.mem_union_left _ (Finset.mem_union_right _ hl)) hvi
  subst hvl
  exact Finset.disjoint_left.1 dc.disj hv hl

theorem row_not_q (w : ℕ) (hw : w ∈ rowsN i dc) : w ∉ qsN i dc := by
  intro hq
  simp only [rowsN, qsN, Finset.mem_image] at hw hq
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨u, hu, huv⟩ := hq
  have huv' : u = v := idx_inj i dc (Finset.mem_union_right _ hu)
    (Finset.mem_union_left _ (Finset.mem_union_left _ hv)) huv
  subst huv'
  exact D.nd.SQ_l i u (Or.inr hu) ((dc.cover u).1 (Or.inl hv))

end Places

section Open

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)


end Open

section Final

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)

end Final

end Formalism.MainNotions.N.K.St

end
end

-- bundled from Formalism.AdmissibleDesigns.URepApply
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem uRec_smul {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (a : D.nd.O i) (m : Mc i Dd c) :
    uRec i Dd hw c φ (a • m) = (D.nbr i w hw).eO a • uRec i Dd hw c φ m := by
  rw [uRec_apply, uRec_apply]
  exact (congrArg (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw))
    (fun x => Br.toLLK_alg (D.nbr i w hw) x)) (φ.map_smul a m)).trans (koEquiv_smul _ _ _ _ _)

theorem uRep_apply' (c : Fin (D.R.t + 1)) (g : GE D.nd) (m : Mc i Dd c) :
    uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m = uElt Dd.r Dd.χ g • m := rfl

omit [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem koE_apply' (e : ℕ) (g : GE D.nd) (x : KO (D.nd.O i)) : koE i e g x = sE i e g • x := rfl

theorem eO_sE (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (e : ℕ) (g : Dw i dc (idx i dc w)) :
    (D.nbr i w hw).eO (sE i e (g : GE D.nd)) = (epsL i dc hw (eW i dc hw g)) ^ e := by
  have hz : (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = ((cycE i (g : GE D.nd))⁻¹) ^ e := by
    rw [show (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = (cycE i (g : GE D.nd)) ^ (-(e : ℤ)) from rfl,
      zpow_neg, zpow_natCast, inv_pow]
  have key : sE i e (g : GE D.nd) = (algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (((cycE i (g : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) ^ e := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hz]
    rfl
  rw [key, map_pow]
  simp [epsL]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem uRec_act (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (g : Dw i dc (idx i dc w)) (m : Mc i Dd c) :
    uRec i Dd hw c φ (uElt Dd.r Dd.χ (g : GE D.nd) • m) =
      (epsL i dc hw (eW i dc hw g)) ^ ((c : ℕ) - 1) • uRec i Dd hw c φ m := by
  have h1 : uElt Dd.r Dd.χ (g : GE D.nd) • m = sE i ((c : ℕ) - 1) (g : GE D.nd) • m := by
    apply φ.injective
    rw [← uRep_apply' i Dd c, hφ, koE_apply', φ.map_smul]
  rw [h1, uRec_smul, eO_sE i dc hcyc hw]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def coefDictOf (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (hcont : Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^ ((c : ℕ) - 1)) :
    CoefDict (Br.PD D.loc D.nbr i w hw) (Br.LLw (D.nbr i w hw)) (Br.Ow (D.nbr i w hw)) (D.nbr i w hw).eO
      (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1) where
  Ce := twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont
  u := uRec i Dd hw c φ
  u_smul a m := uRec_smul i Dd hw c φ a m
  u_act g m := (uRec_act i dc Dd hcyc hw c φ hφ g m).trans
    (actD_twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont (eW i dc hw g)
      (uRec i Dd hw c φ m)).symm

end Dict

end Formalism.MainNotions.N.K.TBb

end
end

