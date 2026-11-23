module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.MainNotions.NAdm (TWSet AdmQ)
open GlobalTheory.UnivChar (IsUnivChar withUnivChar)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

namespace Setup

variable (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m) (b : Bool)

structure IsHeckeDatum (k : ℕ) (P : Pl D.host.E) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) : Prop where
  elt : Links.IsHeckeAt (Wc D j) P k α
  reps : Bridge.IsDC (ρ.levK i j b) α R
  det : IsDetAt (idemAt P) (Wc D j) α z

def hecke (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) :
    (GA D (Wc D j) → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
  ((((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹) •
    ∑ γ ∈ R, LinearMap.funLeft ℂ ℂ fun x => x * γ

theorem hecke_apply (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) (F : GA D (Wc D j) → ℂ)
    (x : GA D (Wc D j)) : ρ.hecke i j b k P R z F x = (((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ *
      (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹ * ∑ γ ∈ R, F (x * γ) := by
  simp only [hecke, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.funLeft_apply]

end Setup

section Hecke

variable {ρ : Setup X} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b)

def HeckeAt (k : ℕ) (P : Pl D.host.E) (f g : Y.Fm i ((j : ℕ) + 1) b) : Prop :=
  ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → rd g = ρ.hecke i j b k P R z (rd f)

def HeckeTie : Prop :=
  ∀ k P, HkIdx i k P → ∀ f, (∃ g, HeckeAt rd k P f g) → HeckeAt rd k P f (Y.hkF i _ b k P f)

def RatHecke : Prop := ∀ k P, HkIdx i k P → ∀ f, ∃ g, HeckeAt rd k P f g

variable {rd}

theorem heckeRead_iff : HeckeRead rd ↔ ∀ k P, HkIdx i k P → ∀ f, HeckeAt rd k P f (Y.hkF i _ b k P f) :=
  ⟨fun h k P hk f α R z d => funext fun x => (h k P hk α R z d.1 d.2 d.3 f x).trans (ρ.hecke_apply ..).symm,
    fun h k P hk α R z h1 h2 h3 f x => (congrFun (h k P hk f α R z ⟨h1, h2, h3⟩) x).trans (ρ.hecke_apply ..)⟩

theorem heckeRead_iff_tie : HeckeRead rd ↔ HeckeTie rd ∧ RatHecke rd := by
  rw [heckeRead_iff]
  exact ⟨fun h => ⟨fun k P hk f _ => h k P hk f, fun k P hk f => ⟨_, h k P hk f⟩⟩,
    fun h k P hk f => h.1 k P hk f (h.2 k P hk f)⟩

theorem HeckeTie.heckeRead (h : HeckeTie rd) (hR : RatHecke rd) : HeckeRead rd := heckeRead_iff_tie.2 ⟨h, hR⟩

theorem HeckeTie.eq (h : HeckeTie rd) (hinj : Function.Injective rd) {k P} (hk : HkIdx i k P) {α R z}
    (d : ρ.IsHeckeDatum i j b k P α R z) {f g : Y.Fm i ((j : ℕ) + 1) b} (hg : HeckeAt rd k P f g) : Y.hkF i _ b k P f = g :=
  hinj ((h k P hk f ⟨g, hg⟩ α R z d).trans (hg α R z d).symm)

theorem CellTie.injective_rdK {hρ : ρ.Good} (T : CellTie hρ Y rd) (k : ℕ) : Function.Injective (rdK rd hρ k) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨d⟩ := T.nonempty_dat
  have h := (T.thPsi_iff k ∅ 1 (twOK_one i k) d ((1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i _ b d + x)).2 (by
    rw [map_add (f := _), hx, add_zero, rdK_tmul, map_one, one_smul, T.th_eq, Setup.gens_one]
    rfl)
  rw [Y.thPsi_one] at h
  exact add_eq_left.1 h

end Hecke

section Univ

theorem twSet_of_twOK {i : X.Tw} {k : ℕ} {Q : Finset (Pl D.host.E)} {ψ} (h : TwOK (X := X) i k Q ψ) : TWSet X i Q :=
  fun v hv => ⟨h.1 v hv, fun hl => Finset.disjoint_left.1 h.2.1 hv (X.twistExcludedPlaces_contains_residueChar i hl)⟩

variable {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : IsUnivChar Y) {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ}
include hY

theorem delU_off (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∉ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = 0 := by
  classical
  rw [hY, GalChar.delU_apply, GalChar.delCoord]
  split_ifs with h
  · rw [GalChar.delOf, dif_neg]
    · rfl
    rintro ⟨d, h1, h2, h3, h4, h5⟩
    obtain ⟨P', hc⟩ := GlobalTheory.TwistDet.exists_isConjPl v.1
    have hP' : P' ∈ Q := h (Or.inr hc)
    have key : ∀ P, GalChar.pair D.host P = GalChar.pair D.host v.1 →
        ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)), IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
        (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
        (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
        ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
          Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P e =>
      ⟨d, h1, h2, h3, fun w a c => h4 w (e ▸ fun t => t.elim a c), fun A hA x => by
        obtain ⟨σ, hσ, hx⟩ := h5 P (e ▸ Or.inl rfl) A hA (Multiplicative.ofAdd x)
        exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩⟩
    refine hv (mem_admissibleConjugatePairPlaces_iff.2 ⟨v.2, P', hP', hc, fun w hw => ?_, fun w hw => ?_⟩)
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hQ _ v.2
      · exact Finset.mem_singleton.1 hw ▸ hQ _ hP'
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨⟨P', by simp, hc⟩, key _ rfl⟩
      · obtain rfl := Finset.mem_singleton.1 hw
        exact ⟨⟨v.1, by simp, GalChar.isConjPl_symm hc⟩, key _ (GalChar.pair_eq hc)⟩
  · rfl

theorem delU_on (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v =
      Multiplicative.toAdd (GalChar.delOf D.host X.cc (X.l i) M (GalChar.pair D.host v.1) σ) := by
  rw [hY, GalChar.delU_apply, GalChar.delCoord, if_pos]
  rintro w (rfl | hw)
  · exact v.2
  · exact admissibleConjugatePairPlaces_subset i Q M (conj_mem_admissibleConjugatePairPlaces hv hw)

theorem delU_eq_coord (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M v.1 σ) := by
  by_cases hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M
  · rw [delU_on hY σ v hv, coord_apply _ _ _ _ hv, hY, GalChar.delU_apply,
      GalChar.delCoord_of_closed _ _ _ (fun _ h _ hc => conj_mem_admissibleConjugatePairPlaces h hc) M hv]
  · rw [delU_off hY hQ σ v hv, coord, dif_neg hv]
    rfl

theorem delU_eq_spread (hQ : TWSet X i Q) {ch : Set (Pl D.host.E)} (hch : IsChoice ch) (σ : G D.host.E N.Om) :
    Multiplicative.toAdd (Y.delU i Q M σ) =
      spread Y i Q M ch fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) :=
  funext fun v => (delU_eq_coord hY hQ σ v).trans (spread_coord Y i Q M hch σ v).symm

end Univ

section Full

variable {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ)

structure FullTie : Type where

  tie : Comparison₂ hρ rd

  hecke : ∀ i j b, HeckeTie (rd i j b)

  univ : IsUnivChar Y

variable (hF : ∀ i j b, Faithful (rd i j b))


variable (hL : ρ.LatFG)

end Full

end GlobalTheory.SeriesTie

end
