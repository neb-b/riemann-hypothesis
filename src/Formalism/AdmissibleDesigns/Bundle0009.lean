module

public import Formalism.AdmissibleDesigns.LiftMapEquivariant
public import Formalism.AdmissibleDesigns.LengthSemilinear
public import Formalism.AdmissibleDesigns.Bundle0008
public import Formalism.AdmissibleDesigns.MemIntegralSpanIffImage

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.FiniteClassesRowEqGeneric
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.BasicNotions.Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem len_congr {O H : Type} [CommRing O] [AddCommGroup H] [Module O H] {A A' B B' : Submodule O H}
    (hA : A = A') (hB : B = B') :
    Module.length O (↥A ⧸ B.comap A.subtype) = Module.length O (↥A' ⧸ B'.comap A'.subtype) := by
  subst hA hB
  rfl

theorem fs_eq {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Fs i dc VT VT' Dat n = FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) (Dat n) := by
  have key : fZ i dc n (Dat n).ρT' = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Dat n).ρT' (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Fs FsG Hf₂ finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]

theorem finite_classes_row_eq_generic {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Hf₁ i dc ρ₁ n = finiteClassesContinuousLattice (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn)
      (resRep ρ₁ (Γn i dc n)) := by
  have key : fZ i dc n (locRep (resRep ρ₁ (Γn i dc n))) = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Hf₁ finiteClassesContinuousLocal finiteClassesContinuousLattice finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i)


set_option maxHeartbeats 1000000 in
theorem rowLenD_eq_gen {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      Module.length (D.nd.O i)
        (↥(FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)) ⧸
          (imG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)
            (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n)).comap
            (FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw)
              (Dat n)).subtype) := by
  unfold rowLenD
  exact len_congr (fs_eq i dc VT VT' Dat hw) (by unfold imRow; rw [finite_classes_row_eq_generic i dc ρ₁ hw]; rfl)


set_option maxHeartbeats 1000000 in
theorem rowLenD_eq {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    [Module.Finite (D.nd.O i) T₁] [Module.Free (D.nd.O i) T₁]
    [Module.Finite (D.nd.O i) (Dat n).T'] [Module.Free (D.nd.O i) (Dat n).T']
    (hsp : ∀ x : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m : (Dat n).T', (Dat n).T'.subtype m = c • x)
    (hcob : OrbC i dc (n := n) (Dat n).ρT')
    (htopV : ∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (c (Br.iota D.nbr i _ hw g))) → Continuous c)
    (htop1 : ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) →
        Continuous c) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
        (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp).col (Br.PD D.loc D.nbr i _ hw) := by
  have hbij : Function.Bijective (Br.iota D.nbr i _ hw) := (D.nbr i _ hw).e.symm.bijective
  have hcobn : ∀ x : VT' n, (fun γ => (Dat n).ρT' γ x - x) ∈
      finZ (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Dat n).ρT' (Br.iota D.nbr i _ hw) := by
    intro x
    have h := cob_mem_fZ i dc (Dat n).ρT' hcob x
    rwa [fZ_pos i dc _ hw] at h
  exact (rowLenD_eq_gen i dc VT VT' Dat ρ₁ π vD hpD heD hw).trans
    (len_eq_col (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw)
      (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n) hsp
      hbij hcobn htopV htop1)


set_option maxHeartbeats 1000000 in
theorem rowTie_disp (hπ : Function.Surjective π)
    (hSub : RowSub (ρ₁ := ρ₁) i dc r) (hOrb : RowOrb (ρ₁ := ρ₁) i dc)
    (hMat : RowMat i dc VT VT' Dat ρ πx) (hTop : RowTop i dc VT' (T₁ := T₁))
    (hFin : RowFin i dc VT VT' Dat (T₁ := T₁))
    (hcob : ∀ n ∈ K.rowsN i dc, OrbC i dc (n := n) (Dat n).ρT') :
    K.Sel.RowTie i dc r ρ πx (rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD) := by
  intro n hn hw b hR
  obtain ⟨hF1, hF2, hFn⟩ := hFin
  obtain ⟨hF3, hF4, hsp⟩ := hFn n hn
  haveI := hF1
  haveI := hF2
  haveI := hF3
  haveI := hF4
  have hev : Function.Surjective ((vD n).toLinearMap ∘ₗ π) := (vD n).surjective.comp hπ
  have hrow := rowLenD_eq i dc VT VT' Dat ρ₁ π vD hpD heD hw hsp (hcob n hn) (hTop n hn hw).1 (hTop n hn hw).2
  have hR' : RowAt (Br.PD D.loc D.nbr i _ hw) (LL := Br.LLw (D.nbr i _ hw)) (O := Br.Ow (D.nbr i _ hw))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (rDuO D.nd i r x)))
      ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (T2O D.nd i ρ πx)) b := hR
  have hL1 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
  have hL2 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
  have hons : Function.Surjective (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))) :=
    trL_onto (hspQ := hsp) (hcomm := fun m => lift_map_mk (Dat n) π (vD n) m) hev
  have hc1 := hOrb n hn hw
  have hc2 : ∀ y, Continuous fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g y := by
    intro y
    obtain ⟨x, rfl⟩ := hons y
    have h : (fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g
        (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n)) x)) =
        fun g => trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))
          (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw) g x) :=
      funext fun g => (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) (Br.iota D.nbr i _ hw g) x).symm
    rw [h]
    exact (trL_cont (eK (D.nbr i _ hw)) _).comp (hc1 x)
  have hOnto := latHom_onto (ρP := resRep ρ₁ (Γn i dc n)) (ρQ := (Dat n).ρTl') (Br.iota D.nbr i _ hw) (heO_br i dc hw) mkK_inj Subtype.val_injective
    (fun γ m => (locRep_mkK (resRep ρ₁ (Γn i dc n)) γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n)) (fun m => lift_map_mk (Dat n) π (vD n) m) hev
  obtain ⟨m, k, hm, hk, hmk⟩ := hR' (TrV (eK (D.nbr i _ hw)) (VT' n))
    (repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw))
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
    hc2 (hMat n hn hw) (TrV (eK (D.nbr i _ hw)) (MK (O := D.nd.O i) T₁))
    (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw))
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
    hc1 (hSub n hn hw)
    (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
      (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp) hOnto
  have hm' : rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n = m := hrow.trans hm
  have hk' : lenOl (Br.PD D.loc D.nbr i (K.plOf i dc n) hw)
      (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (K.plOf i dc n) hw).LL)) = k := hk
  refine ⟨by rw [hm']; exact ENat.coe_ne_top m, ?_⟩
  rw [hm', hk']
  simp only [ENat.toNat_coe]
  exact hmk


end Rec

end Formalism.MainNotions.N.KRow

end
end

-- bundled from Formalism.AdmissibleDesigns.InvariantsMapEquivariant
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.NG Formalism.BasicNotions
  Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

section Phi

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem toKOG_surjective : Function.Surjective (H0.toKOG (D := D) i Dd) := by
  intro y
  refine ⟨fun b => (H0.kogEq _ y) (H0.e0.symm b), ?_⟩
  show (H0.kogEq _).symm (fun a => (H0.kogEq _ y) (H0.e0.symm (H0.e0 a))) = y
  simp only [Equiv.symm_apply_apply]
  exact (H0.kogEq _).symm_apply_apply y

def phi0 : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r :=
  LinearEquiv.ofBijective (H0.toKOG i Dd) ⟨H0.toKOG_injective i Dd, toKOG_surjective i Dd⟩


variable {i r ρ π g0 eB e₁ s Dd} in
theorem invariants_map_equivariant
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    phi0 i Dd (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ g m) = Br.WKO i ρ π g (phi0 i Dd m) := by
  exact H0.toKOG_equiv hD hN g m


variable {i r ρ π g0 eB e₁ s Dd} in
theorem tieSel1_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ)
      (decs D.host.E (Aw i dc) w))))
    (hBk : BkAt i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) F) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F
      (K.QS.Io i) := by
  exact tieSel1_of (hBk := hBk)


variable {i r ρ π g0 eB e₁ s Dd} in
theorem tieSel1_rec_loc
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ)
      (decs D.host.E (Aw i dc) w))))
    (hBk : BkLoc i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) F) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F
      (K.QS.Io i) := by
  exact tieSel1_rec (hD := hD) (hN := hN) (F := F) (hBk := bkAt_of_loc (h := hBk))

end Phi

end Formalism.MainNotions.N.K.Sel

end
end

-- bundled from Formalism.AdmissibleDesigns.KoEquivSmul
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section Eps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

def epsHom (e : ℕ) : G →* Matrix (Fin 1) (Fin 1) LL where
  toFun := Formalism.MainNotions.N.epsTw PD (LL := LL) e
  map_one' := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw]
  map_mul' g h := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw, Matrix.mul_apply, mul_pow]
    ring

theorem matRep_eps (e : ℕ) (g : G) (v : Fin 1 → LL) :
    Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g v =
      fun _ => (algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) ^ e * v 0 := by
  funext j
  change Matrix.mulVec (Formalism.MainNotions.N.epsTw PD (LL := LL) e g) v j = _
  simp [Matrix.mulVec, dotProduct, Formalism.MainNotions.N.epsTw]

variable {PD}

@[reducible] def twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) : TwLat PD LL O e where
  V := Fin 1 → LL
  ρ := Formalism.MainNotions.N.matRep (epsHom PD e)
  L :=
    { T := Formalism.MainNotions.N.stdG O LL 1
      stable := by
        intro g x hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨fun _ => (ε' g) ^ e * u 0, ?_⟩
        rw [matRep_eps]
        funext j
        simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, map_mul, map_pow, hε]
      fg := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).fg
      free := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).free
      span := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).span }
  cont := by
    intro x
    have h : (fun g => Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g x) =
        fun g => fun _ : Fin 1 => (algebraMap O LL (ε' g)) ^ e * x 0 := by
      funext g
      rw [matRep_eps, hε]
    rw [h]
    exact continuous_pi fun _ => hcont.mul continuous_const
  mat := by
    refine ⟨LinearEquiv.refl LL _, fun g v => rfl, fun v => ⟨?_, ?_⟩⟩
    · rintro ⟨u, rfl⟩ j
      exact ⟨u j, rfl⟩
    · intro hv
      choose u hu using hv
      exact ⟨u, funext fun j => hu j⟩

theorem actD_twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) (h : G)
    (x : (twLat hinj ε' hε e hcont).V ⧸ (twLat hinj ε' hε e hcont).L.T) :
    actD (twLat hinj ε' hε e hcont).L h x = (ε' h ^ e) • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    unfold actD
    refine (congrArg Submodule.Quotient.mk
      (?_ : (twLat hinj ε' hε e hcont).ρ h v = (ε' h ^ e) • v)).trans
      (Submodule.Quotient.mk_smul _ _ _)
    funext j
    show Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) h v j = (ε' h ^ e) • v j
    rw [matRep_eps, Algebra.smul_def, map_pow, hε, Subsingleton.elim j 0]

end Eps

section KO

variable {O' : Type} [CommRing O'] [IsDomain O'] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  (σ : O' ≃+* O) (eK : FractionRing O' ≃+* LL)
  (heK : ∀ c : O', eK (algebraMap O' (FractionRing O') c) = algebraMap O LL (σ c))

def kVec : FractionRing O' →ₛₗ[σ.toRingHom] (Fin 1 → LL) where
  toFun x := fun _ => eK x
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp only [Algebra.smul_def, map_mul, heK, Pi.smul_apply]
    rfl

def vecK : (Fin 1 → LL) →ₛₗ[σ.symm.toRingHom] FractionRing O' where
  toFun v := eK.symm (v 0)
  map_add' u v := by simp
  map_smul' c v := by
    apply eK.injective
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply, heK]
    exact congrArg (fun y => algebraMap O LL y * v 0) (σ.apply_symm_apply c).symm

theorem kVec_le : (1 : Submodule O' (FractionRing O')) ≤ (Formalism.MainNotions.N.stdG O LL 1).comap (kVec σ eK heK) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
  rw [Submodule.mem_comap]
  refine ⟨fun _ => σ c, ?_⟩
  funext j
  show algebraMap O LL (σ c) = eK (algebraMap O' (FractionRing O') c)
  exact (heK c).symm

def koTo : KO O' →ₛₗ[σ.toRingHom] ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) :=
  Submodule.mapQ _ _ (kVec σ eK heK) (kVec_le σ eK heK)

def koEquiv : KO O' ≃+ ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) where
  toFun := koTo σ eK heK
  invFun := Submodule.mapQ _ _ (vecK σ eK heK) (by
    rintro _ ⟨u, rfl⟩
    refine Submodule.mem_one.2 ⟨σ.symm (u 0), ?_⟩
    apply eK.injective
    show eK (algebraMap O' (FractionRing O') (σ.symm (u 0))) = eK (eK.symm (algebraMap O LL (u 0)))
    rw [heK, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show Submodule.Quotient.mk (eK.symm (eK x)) = _
      rw [RingEquiv.symm_apply_apply]
  right_inv v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      show Submodule.Quotient.mk (fun _ => eK (eK.symm (v 0))) = _
      congr 1
      funext j
      rw [RingEquiv.apply_symm_apply, Subsingleton.elim j 0]
  map_add' x y := map_add _ x y

theorem koEquiv_smul (a : O') (x : KO O') : koEquiv σ eK heK (a • x) = σ a • koEquiv σ eK heK x := by
  show koTo σ eK heK (a • x) = σ a • koTo σ eK heK x
  exact (koTo σ eK heK).map_smulₛₗ a x

end KO

end Formalism.MainNotions.N.K.TBb

end
end

-- bundled from Formalism.AdmissibleDesigns.RankFfNormAt
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.NG

namespace Formalism.MainNotions.N.KTate

open Formalism.MainNotions.N.KHf

section RecIso2

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)


set_option maxHeartbeats 1000000 in
theorem isoV_of (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (l : K.Col i dc) : IsoV i dc Dd ρ π l := by
  have hn := KDim.col_over i dc l
  let F : TrV (eK (D.nbr i _ hn)) (KFin.Vr i Dd) ≃ₗ[Br.LL D.nbr i _ hn] (Fin D.R.r → Br.LL D.nbr i _ hn) :=
    { toFun := fun v a => eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
      invFun := fun w => (show KFin.Vr i Dd from fun j => (eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm j)))
      map_add' := fun u v => funext fun a => map_add (eK (D.nbr i _ hn)) _ _
      map_smul' := fun c v => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a)) =
          c * eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
        rw [map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun v => funext fun j => by
        show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn)
          ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) ((K.H0.e0 (D := D)).symm j)))) = (show KFin.Vr i Dd from v) j
        rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
      right_inv := fun w => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm (K.H0.e0 (D := D) a)))) = w a
        rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply] }
  refine ⟨F, fun g v => funext fun a => ?_⟩
  have h1 : F (repL (eK (D.nbr i _ hn)) (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) g v) a =
      eK (D.nbr i _ hn) (∑ j, Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd))
        (K.H0.e0 (D := D) a) j • (show KFin.Vr i Dd from v) j) := rfl
  have h2 : KDim.repW i dc ρ π (K.colIdx i dc l) hn g (F v) a =
      ∑ b, algebraMap (Br.OLL D.nbr i _ hn) (Br.LL D.nbr i _ hn) ((D.nbr i _ hn).eO
        (WpO D.nd i ρ π ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd) a b)) * F v b := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, ← Equiv.sum_comp (K.H0.e0 (D := D))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, map_mul, KHf.eK_apply, Br.toLLK_alg, K.H0.unipotent_block_zero_entry hD hN _ a b]
  rfl

theorem rankFf_normAt (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KFin.RankFf i dc Dd ρ π l := by
  apply rankFf_iso (hD := hD) (hc := hc)
  exact isoV_of i dc Dd ρ π r g0 eB e₁ s hD hN l

end RecIso2

end Formalism.MainNotions.N.KTate
end
end

