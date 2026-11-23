module

public import Formalism.AdmissibleDesigns.Bundle0002
public import Formalism.AdmissibleDesigns.GlobalIndexTheoremPlacesOfRNAdm

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.InertiaActsTrivially
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.QS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Places
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def Vo : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.E) // v ∉ placesOver D.host.E (D.nd.l i) ∧ v ∉ D.nd.S i ∧ v ∉ D.nd.Q i}

def VS : Type := {v : HeightOneSpectrum (𝓞 D.host.E) // v ∈ D.nd.S i}

def Io (v : Vo i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def IS (v : VS i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def I (w : ℕ) : Subgroup (decs D.host.E (Aw i dc) w) :=
  (Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w)

def γQ (w : ℕ) : decs D.host.E (Aw i dc) w :=
  ⟨D.nd.gam0 i (plOf i dc w), Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i (plOf i dc w))⟩

def ζO (w : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc w)

def nQ (w : ℕ) (g : decs D.host.E (Aw i dc) w) : ℕ :=
  if h : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n then Nat.find h else 0

def QPow : Prop :=
  ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n

end Places

section Ring
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def ζ (w : ℕ) : Dd.T' := ((Dd.χ (γQ i dc w : GE D.nd) : Dd.T'ˣ) : Dd.T')

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev resU (c : Fin (D.R.t + 1)) (w : ℕ) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc) w)

def Fpos (c : Fin (D.R.t + 1)) (w : ℕ) : Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  if w ∈ qsN i dc then unrH1 (resU i dc Dd c w) (I i dc w)
  else if w ∈ rowsN i dc then
    (if (c : ℕ) = 1 then lcH1 (resU i dc Dd c w) ⊓
        unrH1 (resU i dc Dd c w) ((Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w))
      else ⊥)
  else if (c : ℕ) = 1 then unrH1 (resU i dc Dd c w) (I i dc w) else ⊥

def Fall (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (w : ℕ) :
    Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  Fin.cases (motive := fun c => Submodule (D.nd.O i) (H1z (resU i dc Dd c w))) (F0 w)
    (fun c' => Fpos i dc Dd c'.succ w) c

def c1 : Fin (D.R.t + 1) := ⟨1, by have := RepresentationBoundsCohomology.one_le_letterBlockLength D.R; omega⟩

def InertiaActsTrivially : Prop := ∀ v, ∀ g ∈ Io i v, Dd.r g = 1 ∧ Dd.χ g = 1

def LocClause (c : Fin (D.R.t + 1)) : Prop :=
  InChiLoc (Mc i Dd c) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc) (Fpos i dc Dd c) (Io i) (IS i)
    (I i dc) (γQ i dc) (ζ i dc Dd) (ζO i dc) (nQ i dc)

def CoverClause : Prop :=
  ∀ v, (∃ a, Ine (F := D.host.E) (Av v) ≤ Io i a) ∨ (∃ a, Ine (F := D.host.E) (Av v) ≤ IS i a) ∨
    ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup (decs D.host.E (Aw i dc) w),
      Fpos i dc Dd (c1 (D := D)) w ≤ unrH1 (resU i dc Dd (c1 (D := D)) w) J ∧
      Ine (F := D.host.E) (Av v) ≤ J.map (decs D.host.E (Aw i dc) w).subtype

def NoFixedVectorOffZ : Prop :=
  ∀ x', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) →
    ∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing (D.nd.O i))
        (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.E), η ≠ 0 →
      ∃ g : GE D.nd, ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η ≠ η

end Ring

end Formalism.MainNotions.N.K.QS

end
end

-- bundled from Formalism.AdmissibleDesigns.RealDisplayAllK
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR (divBy unrH1 yY)
open Formalism.RepresentationBoundsCohomology.JL (LiftO ev_equiv ev_equiv_triv mapH1)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (kRow lcH1)
open Formalism.RepresentationBoundsCohomology.FIN
  (InChiFixReal InChiLoc InRhoFixReal2 IsCycG RealLat decs gRow)
open Formalism.RepresentationBoundsCohomology.LOC (LatData pairKO)
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual (IsPlaceOver)
open ReciprocityTheory.Gal (H1 Ine)
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def RealDisplayAllK (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R')
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (Aw : ℕ → ValuationSubring Ω) (pl : ℕ → HeightOneSpectrum (𝓞 Ek))
      (Av : HeightOneSpectrum (𝓞 Ek) → ValuationSubring Ω) (j e' : ℕ → ℕ)
      (what₂ qs : Finset ℕ) (s H0 : ℕ∞) (Sha : ℕ → ℕ∞)
      (cB : ℕ) (cT : Fin (t + 1) → ℕ → ℕ),
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ ((decs Ek Aw) w)))
    let c1 : Fin (t + 1) := ⟨1, by omega⟩

    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L] [SMulCommClass R' O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → (Ω ≃ₐ[Ek] Ω) → L)
      (V : Type) [AddCommGroup V] [Module R' V] [Module O V] [Module (FractionRing O) V]
      [IsScalarTower O (FractionRing O) V] [SMulCommClass R' (FractionRing O) V]
      (iL : L →ₗ[O] V) (qV : V →ₗ[O] blockRestrictedRepresentationType bl ρk 0)
      (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l)))))
      (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l))))
      (F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))))
      (Vo VS : Type) (Io : Vo → Subgroup (Ω ≃ₐ[Ek] Ω)) (IS : VS → Subgroup (Ω ≃ₐ[Ek] Ω))
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
      (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁) (ρ₂ : Representation O (Ω ≃ₐ[Ek] Ω) T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)

      (VT VT' : ℕ → Type)
      [∀ w, AddCommGroup (VT w)] [∀ w, Module O (VT w)] [∀ w, TopologicalSpace (VT w)]
      [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul O (VT w)]
      [∀ w, Module (FractionRing O) (VT w)] [∀ w, IsScalarTower O (FractionRing O) (VT w)]
      [∀ w, AddCommGroup (VT' w)] [∀ w, Module O (VT' w)] [∀ w, TopologicalSpace (VT' w)]
      [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul O (VT' w)]
      [∀ w, Module (FractionRing O) (VT' w)] [∀ w, IsScalarTower O (FractionRing O) (VT' w)]
      (Dat : ∀ w, LatData O ((decs Ek Aw) w) (VT w) (VT' w))
      (uD : ∀ w, blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] (VT w ⧸ (Dat w).T))
      (huD : ∀ w g m, uD w (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) ((decs Ek Aw) w) g m) = (Dat w).ρA g (uD w m))
      (vD : ∀ w, T₂ ≃ₗ[O] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
      (heD : ∀ w g t, vD w (π (resRep ρ₁ ((decs Ek Aw) w) g t)) = (Dat w).ρTl' g (vD w (π t)))

      (Fs : ∀ w, Submodule O (H1 (Dat w).ρTl')) (Hf₁ : ∀ w, Submodule O (H1 (resRep ρ₁ ((decs Ek Aw) w))))
      (I : ∀ w, Subgroup ((decs Ek Aw) w)) (γQ : ∀ w, (decs Ek Aw) w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, (decs Ek Aw) w → ℕ) (u : ι → (Ω ≃ₐ[Ek] Ω) → O)
      (s₀ : ℕ) (y : Oˣ)

      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT)] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT)]
      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT')] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT')]
      (HfW : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT))
      (Hf₂ : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT')),

    let gR : ∀ w, H1 (resRep ρ₁ ((decs Ek Aw) w)) →ₗ[O] H1 (Dat w).ρTl' :=
      fun w => gRow (Dat w) (resRep ρ₁ ((decs Ek Aw) w)) π (vD w) (hpD w) (heD w)
    let Im : ∀ w, Submodule O (H1 (Dat w).ρTl') := fun w => (Hf₁ w).map (gR w)

    ∀ (Pe : Type) [AddCommGroup Pe] [Module R' Pe] [Module O Pe] [SMulCommClass R' O Pe]
      (ince : Pe →ₗ[R'] R') (eve : Pe →ₗ[O] L) (heve : ∀ a, eve a = ince a • v₁)
      (PE : Type) [AddCommGroup PE] [Module R' PE] [Module O PE] [SMulCommClass R' O PE]
      (incE : PE →ₗ[R'] R') (evE : PE →ₗ[O] ↥(Ideal.span {δO}))
      (hevE : ∀ g a, evE (uElt r χ g • a) = evE a)
      (Hfe₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₂ : ∀ l : ι,
        Submodule O (H1z (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))))
      (uz : ∀ l : ι, coZ1s (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))),

    Function.Injective (algebraMap ℤ_[ℓ] O) → PadicCoeff ℓ O → FracTop O → IsFGTop O R' → IsCycG ℓ ε →
    Continuous inc → (Continuous fun g : (Ω ≃ₐ[Ek] Ω) => uElt r χ g) →
    (∀ v, IsPlaceOver (Av v) v) → (ℓ ≠ 2 ∨ InfinitePlace.nrRealPlaces Ek = 0) →
    1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ((ε gI : Oˣ) : O) - 1 = (ℓ : O) ^ s₀ * (y : O) →

    Function.Surjective eve → Function.Surjective evE → (∀ a, ∃ c : R', incE a = c * E) →
    (∀ a (m : blockRestrictedRepresentationType bl ρk c1), incE a • m = ((evE a : ↥(Ideal.span {δO})) : O) • m) →

    (∀ l (g : (decs Ek Aw) (colIdx l)),
      (((uz l : (decs Ek Aw) (colIdx l) → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u l g) →
    (∀ l, Submodule.mkQ _ (uz l) ∈ HfE₂ l) →

    (∀ l, LiftO ℓ (Hfe₁ l) (Ff l)
      (mapH1 _ _ eve (ev_equiv r χ ((decs Ek Aw) (colIdx l)) ince v₁ eve heve)) (e' (colIdx l))) →
    (∀ l, LiftO ℓ (HfE₁ l) (HfE₂ l)
      (mapH1 _ _ evE (ev_equiv_triv r χ ((decs Ek Aw) (colIdx l)) evE hevE)) (e' (colIdx l))) →

    (∀ x', p x' ∉ Z →
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : (Ω ≃ₐ[Ek] Ω), ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ Lx : Submodule (FractionRing O) ((decs Ek Aw) (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l))) ≤ Lx ∧
        (∀ (f : Pe →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ Hfe₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → Pe) g)) ∈ Lx) ∧
        (∀ (f : PE →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ HfE₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → PE) g)) ∈ Lx) ∧
        Module.rank (FractionRing O)
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))).comap
              Lx.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))) : ℕ))) →

    InRhoFixReal2 (blockRestrictedRepresentationType bl ρk 0) r χ e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam →

    (∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : (decs Ek Aw) w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : (decs Ek Aw) w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' ∧ Im w ≤ Fs w) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ ((decs Ek Aw) w))) ≤ H0) ∧
      (∀ w ∈ what₂, F c w = ⊥ ∧
        cT c w ≤ cB ∧
        (∀ ψ : Ymod r χ E →ₗ[O] blockRestrictedRepresentationType bl ρk c, (∀ g ∈ (decs Ek Aw) w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
          ∀ z : coZ1s (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)),
            (∀ g : (decs Ek Aw) w, (z : (decs Ek Aw) w → blockRestrictedRepresentationType bl ρk c) g = ψ (yY r χ E (g : (Ω ≃ₐ[Ek] Ω)))) →
            ((ℓ : O) ^ cT c w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))) ∈ F c w) ∧
        Module.length O (↥(lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c w) ((ℓ : O) ^ cT c w)) ⧸ (F c w).comap (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c w) ((ℓ : O) ^ cT c w)).subtype) ≤
          eO * (cT c w : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 1)) ∧
      InChiFixReal (blockRestrictedRepresentationType bl ρk c) r χ E colIdx (decs Ek Aw) what₂ qs
        (Sha ((c : ℕ) - 1)) (F c) Io IS I γQ ζ ζO nQ) →

    ((∀ l, ∀ g ∈ I (colIdx l), u l (g : (Ω ≃ₐ[Ek] Ω)) = 0) ∧ (∀ l, ∃ g ∈ (decs Ek Aw) (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, F c1 w = lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓
         unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ((Ine (F := Ek) (Aw w)).subgroupOf ((decs Ek Aw) w)) ∧
       cT c1 w ≤ cB ∧
       (∀ ψ : Ymod r χ E →ₗ[O] blockRestrictedRepresentationType bl ρk c1, (∀ g ∈ (decs Ek Aw) w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
         ∀ z : coZ1s (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)),
           (∀ g : (decs Ek Aw) w, (z : (decs Ek Aw) w → blockRestrictedRepresentationType bl ρk c1) g = ψ (yY r χ E (g : (Ω ≃ₐ[Ek] Ω)))) →
           ((ℓ : O) ^ cT c1 w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w))) ∈ F c1 w) ∧
       Module.length O (↥(lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c1 w) ((ℓ : O) ^ cT c1 w)) ⧸ (F c1 w).comap (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c1 w) ((ℓ : O) ^ cT c1 w)).subtype) ≤
         eO * (cT c1 w : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 1)) ∧
     InChiLoc (blockRestrictedRepresentationType bl ρk c1) r χ E (decs Ek Aw) qs (F c1) Io IS I γQ ζ ζO nQ ∧

     (∀ v, (∃ a, Ine (F := Ek) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := Ek) (Av v) ≤ IS a) ∨
        ∃ w ∈ what₂ ∪ qs ∪ univ.image colIdx, ∃ J : Subgroup ((decs Ek Aw) w),
          F c1 w ≤ unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) J ∧
          Ine (F := Ek) (Av v) ≤ J.map ((decs Ek Aw) w).subtype)) →
    (lhs ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + eO * (padicValNat ℓ (classNumber Ek) : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)) ∧
    vδ = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    vδ ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

end Formalism.MainNotions.N.K
end
end

-- bundled from Formalism.AdmissibleDesigns.SelfGood
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.N

def SelfGood {D : D7} (i : D.nd.Loc) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).IsGood

end Formalism.MainNotions.N.K

end
end

-- bundled from Formalism.AdmissibleDesigns.TheoremN5OfNormalizedItems
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions.N Topology

namespace Formalism.MainNotions.N.K.Norm

section Adic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O]

theorem mem_pow_of_mul {c : O} (hc : c ≠ 0) : ∃ k : ℕ, ∀ (n : ℕ) (y : O),
    c * y ∈ (IsLocalRing.maximalIdeal O) ^ (n + k) → y ∈ (IsLocalRing.maximalIdeal O) ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨k, fun n y hy => ?_⟩
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.span_singleton_pow] at hy ⊢
  rw [mul_assoc, Ideal.unit_mul_mem_iff_mem _ u.isUnit, Ideal.mem_span_singleton, pow_add, mul_comm (ϖ ^ n)] at hy
  rw [Ideal.mem_span_singleton]
  exact (mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).1 hy

theorem continuous_of_mul {X : Type} [TopologicalSpace X] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {c : O} (hc : c ≠ 0) {f : X → O} (hf : Continuous fun x => c * f x) : Continuous f := by
  obtain ⟨k, hk⟩ := mem_pow_of_mul hc
  obtain ⟨hopen, hbasis⟩ := isAdic_iff.1 hadic
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, Filter.tendsto_def]
  intro s hs
  have hs0 : (fun y => f x0 + y) ⁻¹' s ∈ 𝓝 (0 : O) := by
    have hcont : Continuous fun y : O => f x0 + y := continuous_const.add continuous_id
    have := hcont.continuousAt (x := 0)
    rw [ContinuousAt, add_zero] at this
    exact this hs
  obtain ⟨n, hn⟩ := hbasis _ hs0
  let V : Set X := (fun x => c * f x - c * f x0) ⁻¹' (((IsLocalRing.maximalIdeal O) ^ (n + k) : Ideal O) : Set O)
  have hV : V ∈ 𝓝 x0 := by
    refine (hopen (n + k)).preimage (hf.sub continuous_const) |>.mem_nhds ?_
    show c * f x0 - c * f x0 ∈ (IsLocalRing.maximalIdeal O) ^ (n + k)
    rw [sub_self]
    exact Ideal.zero_mem _
  refine Filter.mem_of_superset hV (fun x hx => ?_)
  have h1 : c * (f x - f x0) ∈ (IsLocalRing.maximalIdeal O) ^ (n + k) := by
    rw [mul_sub]
    exact hx
  have h2 := hn (hk n _ h1)
  simpa using h2

end Adic

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem map_smul_toK' (c : D.nd.O i) (A : MatN D.nd i) :
    (c • A).map (toK D.nd i) = toK D.nd i c • A.map (toK D.nd i) := by
  ext a b
  simp [Matrix.smul_apply]

theorem exists_integral_mul (M : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) :
    ∃ (b : D.nd.O i) (M0 : MatN D.nd i), b ≠ 0 ∧ M0.map (toK D.nd i) = b • M := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ
    (fun ab : Fin D.R.nV × Fin D.R.nV => M ab.1 ab.2)
  choose M0 hM0 using fun ab : Fin D.R.nV × Fin D.R.nV => hb ab (Finset.mem_univ _)
  refine ⟨b, fun a c => M0 (a, c), nonZeroDivisors.coe_ne_zero b, ?_⟩
  ext a c
  simp only [Matrix.smul_apply]
  exact hM0 (a, c)

theorem rhoCont_of (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) : RhoCont i ρ π := by
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := conjK_self i r ρ π hd
  have hA : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q := by
    intro g
    have h := hconj g
    beta_reduce at h
    rw [h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  obtain ⟨b1, P0, hb1, hP0⟩ := exists_integral_mul i P
  obtain ⟨b2, Q0, hb2, hQ0⟩ := exists_integral_mul i Q
  have hid : ∀ g, (b1 * b2) • rO D.nd i (rN i r ρ π) π g = P0 * rO D.nd i r π g * Q0 := by
    intro g
    apply Matrix.map_injective (toK_inj i)
    show ((b1 * b2) • rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = (P0 * rO D.nd i r π g * Q0).map (toK D.nd i)
    rw [Matrix.map_mul, Matrix.map_mul, hP0, hQ0, map_smul_toK', hA, map_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_comm (toK D.nd i b1), ← map_mul]
    exact algebraMap_smul (KK D.nd i) (b2 * b1) _
  have hcont : Continuous fun g => (b1 * b2) • rO D.nd i (rN i r ρ π) π g := by
    simp only [hid]
    exact (continuous_const.matrix_mul (hc π)).matrix_mul continuous_const
  have hne : b1 * b2 ≠ 0 := mul_ne_zero hb1 hb2
  unfold RhoCont
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine continuous_of_mul (D.nd.O_adic i) hne ?_
  have h2 : Continuous fun g => ((b1 * b2) • rO D.nd i (rN i r ρ π) π g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :=
    (continuous_apply_apply _ _).comp hcont
  refine h2.congr (fun g => ?_)
  change (b1 * b2) * rO D.nd i (rN i r ρ π) π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _
  rw [(normAt_rN i r ρ π).2.2 g a b]

end Rec

end Formalism.MainNotions.N.K.Norm
end
end

