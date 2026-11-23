module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

structure SFam (h k : ℕ) {o : Type} [CommRing o] (ζ : o) where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h k ζ s

  princ : univ.Principal

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre h k ζ s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} →
    c.Principal → ∃ f : S ⟶ X, f ≫ s = s' ∧ SiegPB c univ f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ X) (s' : Sp R ⟶ Sp o) (c : SiegPre h k ζ s'),
    x ≫ s = y ≫ s → SiegPB c univ x → SiegPB c univ y → x = y

def SRep {h p M : ℕ} (Ag : SiegelFamily h p M) : Prop :=
  IsSeparated Ag.s ∧ ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (ZP p M)) (c : SiegPre h M (zetaZP p M) s'), IsReduced S →
    Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Ag.X, f ≫ Ag.s = s' ∧ SiegPB c Ag.univ f

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isSeparated_of_isQProjOver {X : Scheme.{0}} {f : X ⟶ Sp o} (h : IsQProjOver f) : IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have : IsImmersion i := hi
  unfold PSpace.str
  infer_instance

theorem SFam.isSeparated {h : ℕ} {ζ : o} (F : SFam h k ζ) : IsSeparated F.s := isSeparated_of_isQProjOver F.qproj

theorem SFam.eq_constPt {h : ℕ} {ζ : o} (F : SFam h k ζ) (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ F.X)
    (c : SiegPre h k ζ (x ≫ F.s)) (hs : x ≫ F.s = constPt x ≫ F.s) (h₁ : SiegPB c F.univ x)
    (h₂ : SiegPB c F.univ (constPt x)) : x = constPt x := F.inj (DualNumber K) x (constPt x) (x ≫ F.s) c hs h₁ h₂

theorem SFam.sRep {h p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    SRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := ⟨F.isSeparated, fun S s' c hS hd hc => F.rep S s' c hS hd hc⟩

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZM.DwModel

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

private lemma spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, spMap f = y :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

private lemma spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have h' := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

theorem isGaloisCover_field (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisCover (L ≃ₐ[K] L) (fun σ => spMap (σ : L →+* L)) (spMap (algebraMap K L)) := by
  refine
    { finite := inferInstance
      one := ?_
      mul := ?_
      inv := ?_
      fin := ?_
      etale := ?_
      onto := ?_
      fibre := ?_ }
  · show Spec.map _ = _
    convert Spec.map_id (CommRingCat.of L)
    rfl
  · intro a c
    show spMap (((a * c : L ≃ₐ[K] L) : L →+* L)) = _
    rw [← spMap_comp_moduli_spaces]
    rfl
  · intro a
    rw [← spMap_comp_moduli_spaces]
    congr 1
    ext r
    exact a.commutes r
  · show IsFinite (Spec.map _)
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · show Etale (Spec.map _)
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    show (algebraMap K L).Etale
    rw [RingHom.etale_algebraMap]
    exact ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  · exact ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  · intro K' _ _ y y' h
    obtain ⟨f, rfl⟩ := spMap_surjective' y
    obtain ⟨f', rfl⟩ := spMap_surjective' y'
    rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
    have hfa := spMap_inj_lemma_3 h
    let _ : Algebra K K' := (f.comp (algebraMap K L)).toAlgebra
    let φ : L →ₐ[K] K' := { f with commutes' := fun _ => rfl }
    let φ' : L →ₐ[K] K' :=
      { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
    let Φ : (L ≃ₐ[K] L) → (L →ₐ[K] K') := fun a => φ.comp a.toAlgHom
    have hinj : Function.Injective Φ := by
      intro a b hab
      ext x
      exact f.injective (AlgHom.congr_fun hab x)
    have hcard : Nat.card (L →ₐ[K] K') ≤ Nat.card (L ≃ₐ[K] L) := by
      rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
    obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
    refine ⟨a, ?_, fun b hb => ?_⟩
    · show spMap f ≫ spMap (a : L →+* L) = spMap f'
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext x
      exact AlgHom.congr_fun ha x
    · have hb' : f.comp (b : L →+* L) = f' := by
        have hb0 : spMap f ≫ spMap (b : L →+* L) = spMap f' := hb
        rw [← spMap_comp_moduli_spaces] at hb0
        exact spMap_inj_lemma_3 hb0
      apply hinj
      ext x
      exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm

end GlobalTheory.ZM.DwModel
end
end

