module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder

@[expose] public section

noncomputable section
section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

def eExp (D : D7) (j : Fin D.R.m) (g : D.R.Psi) : ℚ := (D.hc (D.eTau.symm g)).e j

structure CharFrame (D : D7) where

  P : PiBar D.host

  W : Omg D.host

  mu0 : Fin D.R.m → HChar D.host.E
  eta : HChar D.host.E
  chiPsi : HChar D.host.E
  del : HChar D.host.E
  del' : HChar D.host.E
  isMu0 : ∀ j, IsMu0 P W (eExp D j) j.1 (mu0 j)
  isEta : IsEtaT D.host eta
  isChi : IsChiPsi D.host chiPsi
  isDel : IsDelta D.host.pde del
  isDel' : IsDelta D.host.pde' del'

def CharFrame.delAt {D : D7} (C : CharFrame D) (l : ℕ) : HChar D.host.E := if l = D.host.pde then C.del' else C.del

structure TupTied (D : D7) (C : CharFrame D) (nch : NChoice D) where

  xi : D.what₂.Tup → HChar D.host.E
  xi_inj : Function.Injective xi
  xi_fin : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n
  xi_triv : ∀ μ, (xi μ).TrivOn D.host.F
  xi_tame : ∀ μ v, (xi μ).TameAt v

  psi : D.what₂.places.Pl → HChar D.host.E

  trueColumnChoices_heckeChar_reference_eq_one : xi D.what₂.mu0 = 1

  xi_star : xi D.what₂.muStar = C.del
  xi_star' : xi D.what₂.muStar' = C.del'

  xi_tw : ∀ w, xi (D.what₂.muTw w) = C.delAt (D.what₂.places.resChar w) * psi w

  psi_is : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → IsPsi (D.what₂.places.resChar w) (nch.Q w) (psi w)

  psi_un : ∀ w, D.what₂.muAt w = D.what₂.mu0 → psi w = 1

def IsFinIdele {L : Type} [Field L] [NumberField L] (a : Ideles L) : Prop :=
  ∀ w : InfinitePlace L, (a : AdeleRing (𝓞 L) L).1 w = 1

structure DtTied (D : D7) (C : CharFrame D) where
  eDt : Ideles D.host.E →* D.Dt
  surj : Function.Surjective eDt

  ker_open : IsOpen ((eDt.ker : Subgroup (Ideles D.host.E)) : Set (Ideles D.host.E))
  inf : ∀ w y, eDt (infIdele D.host.E w y) = 1

  onF : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : D.host.Fˣ),
    eDt (∏ Q ∈ aboveF (L := D.host.E) D.host.F v, localIdele D.host.E Q (atFin Q (upF D.host.F k))) = 1

  ker_le : ∀ a, eDt a = 1 → ∀ w w', IsConjPl D.host w w' →
    Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w) = Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w')

  rat : letI := D.host.cmStar; ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
    eDt (diagUnits D.host.E k) = D.e1Dt z

  UO_eq : ∀ x, x ∈ D.UO ↔ ∃ a : Ideles D.host.E,
    (∀ v, Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1) ∧ eDt a = x

  muTil_eq : ∀ (j : Fin D.R.m) (a : Ideles D.host.E), IsFinIdele a → D.muTil (j.1 + 1) (eDt a) = (C.mu0 j).1 a

  chiD_eq : ∀ a : Ideles D.host.E, IsFinIdele a → D.chiD (eDt a) = C.chiPsi.1 a

def IsCSD {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : Prop :=
  (∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹) ∧
    ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹

end GlobalTheory.Mem.Chr

end
