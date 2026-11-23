module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaC
public import Formalism.LocalToGlobal.NumberFieldFamilies.Bundle0002
public import Formalism.LocalToGlobal.JointCharacters.SameChr

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Host Formalism.L2.JoinChr Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

variable {D : D7}

def plE (τ : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (tauE D τ)


open Classical in
def embAt (τ : D.what₂.Tau) : (plE τ).Completion →+* ℂ :=
  if (plE τ).embedding = tauE D τ then InfinitePlace.Completion.extensionEmbedding (plE τ)
  else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (plE τ))

theorem conj_tauE_ne (τ τ' : D.what₂.Tau) : ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, tauE_sqrtMinusD, tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos D
  linarith

theorem plE_bij (D : D7) : Function.Bijective (plE (D := D)) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · exact tauE_inj e
    · exact absurd e (conj_tauE_ne τ τ')
  · intro w
    obtain ⟨τ, h | h⟩ := tauE_or w.embedding
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_embedding]⟩
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem plE_complex (τ : D.what₂.Tau) : (plE τ).IsComplex := by
  rw [plE, InfinitePlace.isComplex_mk_iff]
  exact fun h => conj_tauE_ne τ τ h

structure AdBC (D : D7) where
  Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E
  cont : Continuous Φ
  cont' : Continuous Φ.symm
  inc : ∀ k : D.host.E, Φ (incA D k) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) k

  fin : ∀ x, finPart D x = 1 ↔ (Φ x).2 = 1

  inf : ∀ τ x, embAt τ ((Φ x).1 (plE τ)) = cmpAt D τ x

  idem : ∀ P e, IsPlIdem D e P ↔ Φ e = pairA D.host.E 0 (singleV D.host.E P 1)

  int : ∀ x, finPart D x ∈ intAE D ↔ ∀ P, (Φ x).2 P ∈ P.adicCompletionIntegers D.host.E

  idemF : ∀ v, (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).1 = 0 ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), (P.under (𝓞 D.host.F) = v →
      (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 1) ∧
      (P.under (𝓞 D.host.F) ≠ v → (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 0)

namespace AdBC

variable (B : AdBC D)

def up : (AE D)ˣ →* Ideles D.host.E := Units.map B.Φ.toMonoidHom

def dn : Ideles D.host.E →* (AE D)ˣ := Units.map B.Φ.symm.toMonoidHom

theorem dn_up (x : (AE D)ˣ) : B.dn (B.up x) = x := Units.ext (by simp [up, dn])

theorem up_inc (k : D.host.Eˣ) : B.up (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (by simp [up, B.inc]; rfl)

theorem toUnits_cont : Continuous Circle.toUnits := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun z : Circle => z⁻¹)

def toH : chrA D →* HChar D.host.E where
  toFun χ := ⟨(Circle.toUnits.comp χ.1).comp B.dn,
    (toUnits_cont.comp χ.2.1.1).comp (Continuous.units_map _ B.cont'), fun k => by
      rw [← B.up_inc, MonoidHom.comp_apply, B.dn_up, MonoidHom.comp_apply, χ.2.1.2, map_one]⟩
  map_one' := Subtype.ext (MonoidHom.ext fun _ => map_one Circle.toUnits)
  map_mul' _ _ := Subtype.ext (MonoidHom.ext fun _ => map_mul Circle.toUnits _ _)

end AdBC

section Dens

variable {L : Type} [Field L] [NumberField L]

end Dens

namespace AdBC

variable (B : AdBC D)

def ResTriv : Prop := ∀ χ : HChar D.host.E, χ.TrivOn D.host.F → ∀ a, χ.1 (B.up (idF D a)) = 1

def EtaIs : Prop := ∀ χ : chrA D, (B.toH χ).ResEta D.host.F → IsEta D (χ.1.comp (idF D))

def UnrAll : Prop := ∀ χ : chrA D, (∀ v, (B.toH χ).UnrAt v) → UnramEverywhere D χ.1

end AdBC

def EtaU (D : D7) : Prop := ∀ η η', IsEta D η → IsEta D η' → η = η'

structure ChrGaps (B : AdBC D) : Prop where
  triv : B.ResTriv
  etaIs : B.EtaIs
  unr : B.UnrAll
  etaU : EtaU D

section Frame

variable {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

variable (B : AdBC D)

variable {ψ : AddChar (AF D.host.F) ℂ} (Gc : ChrGaps B) (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ)
  (f : Free Om)

end Frame

end Formalism.L2.Fam.ThC

end
