module

public import Formalism.AdmissibleDesigns.Bundle0003
public import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound
public import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.BlockTwistedCyclotomic
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]

def selRep2 (ρ : Representation R G M) {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (F : ∀ w, Submodule R (H1z (resRep ρ (D w)))) (P : Finset ℕ) : Submodule R (H1z ρ) :=
  (lcH1 ρ ⊓ (⨅ v, unrH1 ρ (J v)) ⊓ ⨅ v, unrH1 ρ (JS v)) ⊓ ⨅ w ∈ P, (F w).comap (resH1 ρ (D w))

def Fsha (ρ : Representation R G M) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) :
    Submodule R (H1z (resRep ρ (D w))) :=
  if w ∈ qs then unrH1 (resRep ρ (D w)) (Iq w) else ⊥

def RepIso {M' : Type} [AddCommGroup M'] [Module R M'] (ρ : Representation R G M) (ρ' : Representation R G M') :
    Prop :=
  ∃ φ : M ≃ₗ[R] M', ∀ g m, φ (ρ g m) = ρ' g (φ m)

end Gen

def CoefChange (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (ψ : G →* ℤ_[l]ˣ) {V VS : Type} (J : V → Subgroup G)
    (JS : VS → Subgroup G) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ),
    let ψO : G →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ψ
    let ρO := Formalism.GaloisCohomology.scalRep (KO O) ψO
    let ρZ := Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ l) ψ
    Module.length O ↥(selRep2 ρO J JS D (Fsha ρO D Iq qs) P) ≤
      Module.length O (O ⧸ Ideal.span {((l : ℕ) : O)}) * Module.length ℤ_[l] ↥(selRep2 ρZ J JS D (Fsha ρZ D Iq qs) P)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def Pall : Finset ℕ := rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc)

def cycE : GE D.nd →* ℤ_[D.nd.l i]ˣ := cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i)

def qzE (e : ℕ) : Representation ℤ_[D.nd.l i] (GE D.nd) (Formalism.GaloisCohomology.QZ (D.nd.l i)) :=
  Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ (D.nd.l i)) (cycE i ^ (-(e : ℤ)))

def koE (e : ℕ) : Representation (D.nd.O i) (GE D.nd) (KO (D.nd.O i)) :=
  Formalism.GaloisCohomology.scalRep (KO (D.nd.O i)) ((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
    (cycE i ^ (-(e : ℤ))))

def selZ (e : ℕ) : Submodule ℤ_[D.nd.l i] (H1z (qzE i e)) :=
  selRep2 (qzE i e) (Io i) (IS i) (decs D.host.E (Aw i dc)) (Fsha (qzE i e) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc))
    (Pall i dc)

def BlockTwistedCyclotomic (c : Fin (D.R.t + 1)) : Prop :=
  RepIso (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (koE i ((c : ℕ) - 1))

def ZlSha (e : ℕ) : Prop :=
  Module.length ℤ_[D.nd.l i] ↥(selZ i dc e) ≤ Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

end Rec

end Formalism.MainNotions.N.K.ShaT

end
end

-- bundled from Formalism.AdmissibleDesigns.DisplayForms
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.N.K.Topo

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem topoHyps
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (u : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) ∧ PadicCoeff (D.nd.l i) (D.nd.O i) ∧
      FracTop (D.nd.O i) ∧ IsFGTop (D.nd.O i) Dd.R' ∧ IsCycG (D.nd.l i) (epsU D.nd i) ∧
      (Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g) ∧
      (∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v) ∧
      (D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0) ∧
      1 ≤ D.nd.s0 i ∧ (D.nd.l i = 2 → 2 ≤ D.nd.s0 i) ∧
      ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) - 1 =
        ((D.nd.l i : ℕ) : D.nd.O i) ^ D.nd.s0 i * ((yU i u : (D.nd.O i)ˣ) : D.nd.O i) ∧
      (∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc, (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
        IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w)) := by
  refine ⟨?_, padicCoeff_O i, fracTop_O i, fgTop_RD i r π g0 eB e₁ s Dd hD, ?_, uElt_cont i r π g0 eB e₁ s Dd hD hc,
    av_over, ?_, one_le_localLevel i, restNLevelExponent_of_two i, ?_, rows_over i dc⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((PadicInt.unitCoeff h0 : ℤ_[D.nd.l i]) * (D.nd.l i : ℤ_[D.nd.l i]) ^ x.valuation) = 0 := by
      rw [← PadicInt.unitCoeff_spec h0]
      exact hx
    rw [map_mul, map_pow, map_natCast] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).ne_zero h
    · exact (padicCoeff_O i).p_ne (pow_eq_zero_iff'.mp h).1
  · apply isCyc_eps <;> assumption
  · apply l_or_noReal <;> assumption
  · have h2 : ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) := rfl
    rw [h2, hcyc]
    simp [yU]

end Formalism.MainNotions.N.K.Topo

end
end

-- bundled from Formalism.AdmissibleDesigns.ExistsLx
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KHf

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem exists_Lx {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    (hPe : ∀ (c : D.nd.O i) (m : Pe), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (hPE : ∀ (c : D.nd.O i) (m : PE), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (j : ℕ → ℕ) (x' : X') (l : K.Col i dc)
    (hO : letI := evalModO i (R' := R') x'
      haveI := evalTower i (R' := R') x'
      OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)))
    (hdim : DimLx i dc r χ j x' l) :
    ∃ Lx : Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x'),
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx ∧
      (∀ (f : Pe →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := Pe) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → Pe) g)) ∈ Lx) ∧
      (∀ (f : PE →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := PE) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := PE) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → PE) g)) ∈ Lx) ∧
      Module.rank (FractionRing (D.nd.O i))
          (Lx ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))).comap Lx.subtype) ≤
        (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
          (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))) : ℕ) := by
  refine ⟨Lx i dc r χ x' l, ?_, ?_, ?_, hdim⟩
  · apply colD_le_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption

end Formalism.MainNotions.N.KHf

end
end

-- bundled from Formalism.AdmissibleDesigns.RealDisplayAllKOf
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain
open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
  (InChi InRowRho inputs_from_selmer_inj theorem_n_five_delta_clause)
open Formalism.RepresentationBoundsCohomology.FIN
  (InRhoFixReal blk_ko colPsi_lc decs inRowReal_of kRowRange pi_ko_torsion resLC rowRhoReal)
open Formalism.RepresentationBoundsCohomology.JL (colFun colK colk)
open Formalism.RepresentationBoundsCohomology.JT (BKIn InRowRhoNoBK rowBK)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (clsRow kRow kRowInj lcH1 qK)
open Formalism.RepresentationBoundsCohomology.SplitClassesAll (InRhoFix)
open Formalism.RepresentationBoundsCohomology.T2 (vhEInChi)
open ReciprocityTheory.ChartRestriction.T2 (IsCycOn)
open ReciprocityTheory.Gal (H1)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem realDisplayAllK_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAllK ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard1, -, -, -, -, -, -, hOne0⟩ := hR
  obtain ⟨p1, -, -, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha cB cT cols eO vδ N h0 c1
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ ince eve heve PE _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne

  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix2 : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hpD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hk : ∀ w, Function.Injective (kRow (Dat w) _ (uD w) (huD w)) :=
    fun w => kRowInj O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w)
  have hcycw : ∀ w, IsCycOn ℓ (decs Ek Aw w) (ε.comp (decs Ek Aw w).subtype) :=
    fun w g n ζ h => hcyc g.1 n ζ h
  have hnu : ¬ IsUnit (ℓ : O) := fun h => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hO.p_mem)) h
  have hKO : ∀ c : Fin (t + 1), c ≠ 0 → Nonempty (blockRestrictedRepresentationType bl ρk c ≃ₗ[O] KO O) :=
    fun c hc => blk_ko bl ρk c (hcard1 c hc)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hFix2
  have key : ∀ w, w ∈ what₂ →
      ∃ (pr : LinearMap.range (kRow (Dat w) _ (uD w) (huD w)) →ₗ[O] H1 (Dat w).ρTl' →ₗ[O] KO O)
      (pair : H1 (Dat w).ρT →ₗ[FractionRing O] H1 (Dat w).ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (qK (Dat w) _ (hk w)) (Dat w).j' pr pair (HfW w) (Hf₂ w)
        ((((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w))) (Fs w) ∧
      InRowRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ
        (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (clsRow (Dat w) (vD w)) pr (Fs w) (Im w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact rowRhoReal ℓ O (VT w) (VT' w) Ek Ω (Aw w) a1 R' Tc (blockRestrictedRepresentationType bl ρk 0) r χ E ε T₁ T₂ ρ₁ ρ₂ inc π γ
      (Dat w) (uD w) (huD w) (vD w) (HfW w) (Hf₂ w) (Fs w) (Im w) hO hFr hA (hcycw w) a3 a4 e8 a5 a6 a7 a9
      (e10 w hw) (hk w)
  choose! pr pair hpp using key
  let HcG : ∀ c : Fin (t + 1), Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) :=
    fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)
  let HcR : ∀ (c : Fin (t + 1)) (w : ℕ),
      Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))) := fun c =>
    Fin.cases (motive := fun c => ∀ w : ℕ,
        Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))))
      (fun w => LinearMap.range (kRow (Dat w) _ (uD w) (huD w)))
      (fun c' w => lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c'.succ) r χ) (decs Ek Aw w))) c
  have hBK' : ∀ w ∈ what₂, BKIn (HcR 0 w) (qK (Dat w) _ (hk w)) (Dat w).j' (pr w) (pair w) (HfW w) (Hf₂ w)
      (F 0 w) (Fs w) := by
    intro w hw
    rw [(hRows w hw).2.2.2.2.2.2.2.1]
    exact (hpp w hw).1
  have hFix' : InRhoFix (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (HcG 0)
      (HcR 0) (F 0) Io ε ρ₁ ρ₂ inc π γ lam (fun w => clsRow (Dat w) (vD w)) pr Fs Im :=
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, fun w hw => (hpp w hw).2, e11⟩
  obtain ⟨a1, a2, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, a7, a8, a9, a10, a11, a12, a13⟩ := hFix'

  choose Kc Kz hKc1 hKc2 hKc3 using fun l => colK O R' Tc (Ω ≃ₐ[Ek] Ω) Pe L r χ (decs Ek Aw (colIdx l)) ince v₁ eve heve hse
    (Hfe₁ l) (Ff l) ℓ (e' (colIdx l)) (j (colIdx l)) (κ l) (κz l) (c8 l).1 (c8 l).2.2.1 (hLe l)
  choose k0 kz hk01 hk02 hk03 hk04 using fun l => colk O R' Tc (Ω ≃ₐ[Ek] Ω) PE (blockRestrictedRepresentationType bl ρk c1) r χ E δO (decs Ek Aw (colIdx l)) incE
    evE hincE hact hevE hsE (HfE₁ l) (HfE₂ l) ℓ (e' (colIdx l)) (u l) (uz l) (huz l) (hu l) (hLE l)
  have hcont : ∀ (c : Fin (t + 1)) φ, Submodule.mkQ _ (colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ
      (fun l => decs Ek Aw (colIdx l)) (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG c :=
    fun c φ => colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ
  have hRowsA : ∀ w ∈ what₂, InRowRho (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ (HcR 0 w) (F 0 w)
      (clsRow (Dat w) (vD w)) (pr w) (Fs w) (Im w) := by
    intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7⟩ := a12 w hw
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hBK' w hw
    exact ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7,
      rowBK O _ (HcR 0 w) (H1 (Dat w).ρT) (H1 (Dat w).ρTl') (H1 (Dat w).ρT') (qK (Dat w) _ (hk w)) (Dat w).j'
        (pr w) (pair w) (HfW w) (Hf₂ w) (F 0 w) (Fs w) f2 f3 f4 f5 f6 f7⟩

  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w))
        (cT c) (Sha ((c : ℕ) - 1)) (HcG c) (HcR c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc2
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    obtain ⟨c', rfl⟩ : ∃ c', c = Fin.succ c' := ⟨c.pred hc0, (Fin.succ_pred _ _).symm⟩
    obtain ⟨-, hrw, ⟨i1, i3, i4⟩, i5⟩ := hC _ hc2
    refine ⟨fun w hw => ⟨?_, (hrw w hw).2.1, (hrw w hw).2.2.1, (hrw w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, i5⟩
    rw [(hrw w hw).1]
    exact bot_le
  obtain ⟨o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
  have hc1 : c1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [c1] at this
  have hOneA : InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs
      (fun w => ReciprocityTheory.Gal.locDeg (pl w)) (cT c1) (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞))
      (HcG c1) (HcR c1) (F c1) Io IS I γQ ζ ζO nQ := by
    refine ⟨fun w hw => ⟨?_, (o7 w hw).2.1, (o7 w hw).2.2.1, (o7 w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, ?_⟩
    · rw [(o7 w hw).1]
      exact inf_le_left
    · refine vhEInChi Ek Ω Av hAv ℓ O hreal R' Tc (blockRestrictedRepresentationType bl ρk c1) (hKO _ hc1) r χ p1
        (decs Ek Aw) (what₂ ∪ qs ∪ univ.image colIdx) (HcG c1) (F c1) Vo VS Io IS ?_ o10
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, rfl, hc⟩
  obtain ⟨hv1, hv2⟩ := theorem_n_five_delta_clause O ℓ Fact.out hnu s₀ hs1 hs2 (ε gI) y u₁ hε t
  refine ⟨?_, ?_, ?_⟩
  · exact hF ι colIdx hinj (decs Ek Aw) j e' Kc k0
      (fun x' hx' => by
        obtain ⟨q5, q6⟩ := hrat0 x' hx'
        refine ⟨q5, fun l => ?_⟩
        obtain ⟨Lx, w1, w2, w3, w4⟩ := q6 l
        exact ⟨Lx, w1, fun a s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) Pe (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) ince
            (Hfe₁ l) (Lx : Set _) w2 (Kc l a) (Kz l a) (hKc1 l a) (hKc2 l a) s,
          fun s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) PE (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) incE (HfE₁ l)
            (Lx : Set _) w3 (k0 l) (kz l) (hk01 l) (hk02 l) s, w4⟩)
      ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w)) s (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞)) H0 Sha
      (fun l g => hk03 l g) L tens v₁ κ HcG HcR F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂
      inc π γ lam (fun w => H1 (Dat w).ρTl') (fun w => clsRow (Dat w) (vD w)) pr Fs Im cT I γQ ζ ζO nQ u
      (inputs_from_selmer_inj O R' Tc (Ω ≃ₐ[Ek] Ω) (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ ι colIdx (decs Ek Aw) j e' Kc k0 ℓ what₂ s L tens v₁ κ V
        iL qV Ff κz (HcG 0) (HcR 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam (fun w => H1 (Dat w).ρTl')
        (fun w => clsRow (Dat w) (vD w)) pr Fs Im
        ⟨a1, a2, fun l a g hg => hKc3 l a g hg, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, hcont 0, a7, a8,
          a9, a10, a11, hRowsA, a13⟩)
      (fun c hc2 => ⟨(hC c hc2).1, hC' c hc2⟩)
      ⟨fun l g hg m => hk04 l g hg m, o4, o5, o6, hOneA⟩
  · show IsDiscreteValuationRing.addVal O δO = _
    rw [hδO]
    exact hv1
  · show IsDiscreteValuationRing.addVal O δO ≤ _
    rw [hδO]
    exact hv2

end Formalism.MainNotions.N.K
end
end

