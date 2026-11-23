module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Phi

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))


set_option synthInstance.maxHeartbeats 400000 in
theorem phi_injective (k : ℕ) : Function.Injective (Br.phi (D.nbr i w hw) k) := by
  rw [← LinearMap.ker_eq_bot (τ₁₂ := (D.nbr i w hw).eO.toRingHom), eq_bot_iff]
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have h1 : Br.vecS (D.nbr i w hw) k u ∈ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hx
  obtain ⟨c, hc⟩ := h1
  refine ⟨fun j => (D.nbr i w hw).eO.symm (c j), ?_⟩
  funext j
  apply (Br.toLLK (D.nbr i w hw)).injective
  have := congrFun hc j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at this
  show Br.toLLK (D.nbr i w hw) (algebraMap _ _ ((D.nbr i w hw).eO.symm (c j))) = Br.toLLK (D.nbr i w hw) (u j)
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact this


set_option synthInstance.maxHeartbeats 400000 in
theorem phi_act {k : ℕ} (M : Gw D.nd w →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : ↥(GK (D.nbr i w hw).Kw))
    (x : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (actD (stdLatG (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g) x) = actD (Br.lat (D.nbr i w hw) M) g (Br.phi (D.nbr i w hw) k x) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  have key : Br.vecS (D.nbr i w hw) k ((matRep (mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g)) u) = (matRep (Br.locM (D.nbr i w hw) M) g) (Br.vecS (D.nbr i w hw) k u) := by
    funext p
    show Br.toLLK (D.nbr i w hw) (((mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M
        (Br.ι (D.nbr i w hw) g)).mulVec u) p) =
      ((Br.locM (D.nbr i w hw) M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (u j))) p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    show Br.toLLK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (M (Br.ι (D.nbr i w hw) g) p q)) = _
    rw [Br.toLLK_alg]
    rfl
  exact congrArg (fun z : Fin k → Br.LLw (D.nbr i w hw) =>
    (Submodule.Quotient.mk z : (Fin k → Br.LLw (D.nbr i w hw)) ⧸ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k)) key

end Phi

def wLat (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i))
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) :
    LocLat ↥(GK (D.nbr i u hu).Kw) ℚ_[D.nd.l i] (Br.LLw (D.nbr i u hu)) (Br.Ow (D.nbr i u hu)) :=
  { V := Fin D.R.r → Br.LLw (D.nbr i u hu)
    ρ := matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)))
    cont := hc
    L := Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) }

end Formalism.MainNotions.N
