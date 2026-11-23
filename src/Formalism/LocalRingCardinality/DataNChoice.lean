module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct


set_option synthInstance.maxHeartbeats 400000 in
structure NChoice (D : D7) where

  twI : D.what₂.places.Pl → D.ntw.Tw
  twI_l : ∀ w, D.ntw.l (twI w) = D.what₂.places.resChar w
  sd : D.what₂.places.Pl → Bool

  Q : D.what₂.places.Pl → Finset (PlE D.host)
  k' : D.what₂.places.Pl → ℕ
  psi' : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k' w))ˣ

  Oe : D.what₂.places.Pl → Type
  [crOe : ∀ w, CommRing (Oe w)]
  [domOe : ∀ w, IsDomain (Oe w)]
  [dvrOe : ∀ w, IsDiscreteValuationRing (Oe w)]
  [algOe : ∀ w, Algebra (D.ntw.Ok (twI w) (k' w)) (Oe w)]
  [algOOe : ∀ w, Algebra (D.ntw.O (twI w)) (Oe w)]
  [towOe : ∀ w, IsScalarTower (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k' w)) (Oe w)]
  Oe_inj : ∀ w, Function.Injective (algebraMap (D.ntw.Ok (twI w) (k' w)) (Oe w))
  Oe_fin : ∀ w, Module.Finite (D.ntw.Ok (twI w) (k' w)) (Oe w)
  Oe_loc : ∀ w, IsLocalHom (algebraMap (D.ntw.Ok (twI w) (k' w)) (Oe w))

  embW : ∀ w, D.what₂.LL →+* FractionRing (Oe w)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (Oe w) (FractionRing (Oe w))).range

  eMt : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[embW w]
    FractionRing (Oe w) ⊗[D.ntw.Ok (twI w) (k' w)]
      D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))
  eMt_basis : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
    ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (Oe w)) (fun i => eMt w j (b i)) ∧
      Submodule.span (FractionRing (Oe w)) (Set.range fun i => eMt w j (b i)) = ⊤
  eMt_lat : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → Submodule.span (Oe w)
      (eMt w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
    Submodule.span (Oe w)
      ((TensorProduct.mk (D.ntw.Ok (twI w) (k' w)) (FractionRing (Oe w))
          (D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w)))) 1) ''
        (D.nexp.MtLat (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))) :
          Set (D.nexp.MtV (twI w) j (sd w) (k' w) (Q w) ((psi' w).comp (D.ntw.art (twI w) (Q w))))))

attribute [instance] NChoice.crOe NChoice.domOe NChoice.dvrOe NChoice.algOe NChoice.algOOe NChoice.towOe


set_option synthInstance.maxHeartbeats 400000 in
def NChoice.kMapE {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) :
    FractionRing (D.ntw.Ok (c.twI w) (c.k' w)) →+* FractionRing (c.Oe w) :=
  IsFractionRing.map (j := algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)) (c.Oe_inj w)

namespace NChoice

section OfOk

variable {K V : Type} [CommRing K] [IsDomain K] [AddCommGroup V] [Module (FractionRing K) V] [Module K V]
  [IsScalarTower K (FractionRing K) V]

def fracEquiv (K V : Type) [CommRing K] [IsDomain K] [AddCommGroup V] [Module (FractionRing K) V] [Module K V]
    [IsScalarTower K (FractionRing K) V] : FractionRing K ⊗[K] V ≃ₗ[FractionRing K] V :=
  haveI := isLocalizedModule_id (nonZeroDivisors K) V (FractionRing K)
  (IsLocalizedModule.isBaseChange (nonZeroDivisors K) (FractionRing K) (LinearMap.id : V →ₗ[K] V)).equiv

end OfOk


end NChoice

end Formalism.BasicNotions

end
