module

public import Formalism.AdmissibleDesigns.Bundle0011
public import Formalism.AdmissibleDesigns.FiniteClassesLocalEq
public import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.TwistedTargetOfInputs

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.IdempotentPartFiniteAndFree
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section FinT

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

theorem rFree [Module.Finite O R'] : Module.Free O R' := by
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  exact Module.free_of_finite_type_torsion_free'

theorem idempotent_submodule_finite [Module.Finite O R'] (e₁ : R') : Module.Finite O (FirstSummandSubmodule O e₁) := by
  haveI : IsNoetherian O R' := isNoetherian_of_isNoetherianRing_of_finite O R'
  exact Module.Finite.of_injective (FirstSummandSubmodule O e₁).subtype Subtype.val_injective

theorem idempotent_submodule_free [Module.Finite O R'] (e₁ : R') : Module.Free O (FirstSummandSubmodule O e₁) := by
  haveI := idempotent_submodule_finite (R' := R') e₁
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  haveI : Module.IsTorsionFree O (FirstSummandSubmodule O e₁) := inferInstance
  exact Module.free_of_finite_type_torsion_free'

end FinT

section RecTop

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem idempotent_part_finite_and_free (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧ Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  haveI := Formalism.MainNotions.N.K.Topo.finite_R' hD
  exact ⟨idempotent_submodule_finite Dd.e₁, idempotent_submodule_free Dd.e₁⟩

def eL {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (FractionRing (D.nd.O i)) →ₗ[Br.LLw (D.nbr i _ hn)] Br.LLw (D.nbr i _ hn) where
  toFun k := eK (D.nbr i _ hn) k
  map_add' a b := map_add (eK (D.nbr i _ hn)) a b
  map_smul' c k := by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show FractionRing (D.nd.O i) from k)) =
      c * eK (D.nbr i _ hn) (show FractionRing (D.nd.O i) from k)
    rw [map_mul, RingEquiv.apply_symm_apply]

theorem rowTop1_S (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    KRow.RowTop1 i dc (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  set_option synthInstance.maxHeartbeats 200000 in
  haveI := K.Topo.finite_RD i r π g0 eB e₁ s Dd hD
  haveI : Module.Free (D.nd.O i) Dd.R' := rFree
  haveI := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  haveI := K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := K.Topo.rTop_smul (D.nd.O i) Dd.R'
  intro n _ hw c hc
  let b := Module.Free.chooseBasis (D.nd.O i) Dd.R'
  have hco : ∀ j, Continuous fun γ => b.equivFun ((c γ : Dd.R')) j := by
    intro j
    let f : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i] FractionRing (D.nd.O i) :=
      (Algebra.linearMap (D.nd.O i) (FractionRing (D.nd.O i))) ∘ₗ (b.coord j) ∘ₗ (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype
    let ℓ := (eL i dc hw).comp (trL (eK (D.nbr i _ hw)) (liftK f))
    have hℓ : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ
    have h1 : Continuous fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) := by
      have e1 : (fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))))) =
          fun g => ℓ (KRow.tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) := by
        funext g
        show _ = eK (D.nbr i _ hw) (liftK f (mkK (c (Br.iota D.nbr i _ hw g))))
        rw [liftK_mkK]
        rfl
      rw [e1]
      exact hℓ.comp hc
    have h2 : Continuous fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) := by
      refine continuous_induced_rng.2 ?_
      have e2 : ((↑) ∘ fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) =
          fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
            (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) :=
        funext fun g => (Br.toLLK_alg (D.nbr i _ hw) _).symm
      rw [e2]
      exact h1
    have h3 : Continuous fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')) := by
      have := (D.nbr i _ hw).eO_symm_cont.comp h2
      simpa [Function.comp_def] using this
    have heq : (fun γ => b.equivFun ((c γ : Dd.R')) j) =
        (fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) ∘ (Br.ιHomeo (D.nbr i _ hw)).symm := by
      funext γ
      simp only [Basis.equivFun_apply, Basis.coord_apply]
      exact congrArg (fun γ' => b.repr ((c γ' : Dd.R')) j) (((D.nbr i _ hw).e.symm_apply_apply γ).symm)
    rw [heq]
    exact h3.comp (Br.ιHomeo (D.nbr i _ hw)).symm.continuous
  have hv : Continuous fun γ => ((c γ : Dd.R')) := by
    have e3 : (fun γ => ((c γ : Dd.R'))) = fun γ => b.equivFun.symm (fun j => b.equivFun ((c γ : Dd.R')) j) :=
      funext fun γ => (b.equivFun.symm_apply_apply _).symm
    rw [e3]
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp (continuous_pi hco)
  exact continuous_induced_rng.2 hv

end RecTop

end Formalism.MainNotions.N.KRowA

end
end

-- bundled from Formalism.AdmissibleDesigns.IdempotentPartRepresentationAt
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

theorem sub_of_fam {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} {ιx : Type} {k : ℕ}
    {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} {I : Type} (xx : I → ιx)
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (ρ g v) = (Ms (xx a) g).mulVec (Ψ a v)) : IsSubOfSums ρ Ms := by
  obtain ⟨m, xs, hxs⟩ := KLift.fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

theorem orb_of_sub {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    (h : IsSubOfSums ρ Ms) (hMs : ∀ x, Continuous (Ms x)) (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := h
  exact KLift.cont_of_inj xs φ hφ heq hMs v

end Gen

section Fin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

end Fin

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kap1 : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i]
    (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := (((p : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lattice_inclusion_injective : Function.Injective (kap1 i Dd) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem idempotent_part_representation_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (p : FirstSummandSubmodule (D.nd.O i) Dd.e₁) (x' : Dd.X') :
    kap1 i Dd (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i) g p) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 g : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)) •
        (kap1 i Dd p x' * (rO D.nd i r (Dd.p x') g⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
  show (((((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) • (((Dd.χ g : (Dd.T')ˣ) : Dd.T') •
    ((p : Dd.R') * Dd.r g⁻¹)) : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [Subalgebra.coe_smul, Pi.smul_apply, hsm, hχ, Subalgebra.coe_mul, Pi.mul_apply, hr', map_mul, mul_smul,
    ← algebraMap_smul (FractionRing (D.nd.O i)) ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i), smul_comm]
  rfl

theorem locC_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i _ hn) (a b : Fin k) :
    TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) M g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (M ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← KLift.heO_br i dc hn]
  rfl


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rowSub_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    [Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)] [Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)]
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsSubOfSums (repL (eK (D.nbr i _ hn))
        (locRep (resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x))) := by
  set ρP := resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) (kap1 i Dd)
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = kap1 i Dd m := by
    intro m s
    rw [← map_smul, KLift.smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [lattice_inclusion_injective i Dd (h1.symm.trans (map_zero (kap1 i Dd)).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v x', Λ (locRep ρP γ v) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 (γ : GE D.nd) : D.nd.O i) * ((epsU D.nd i (γ : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (Λ v x' * (rO D.nd i r (Dd.p x') (γ : GE D.nd)⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    intro γ v x'
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply KLift.smul_cancel s
      have h1 := congrFun (hΛs (ρP γ m) s) x'
      have h2 := congrFun (hΛs m s) x'
      rw [Pi.smul_apply] at h1 h2
      rw [h1, smul_comm, ← Matrix.smul_mul, h2]
      exact idempotent_part_representation_at i r Dd hr' hsm hχ (γ : GE D.nd) m x'
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v j => e ((Λ (KLift.untr e v)) q.1 q.2 j)
      map_add' := fun v w => funext fun j => by
        show e ((Λ (KLift.untr e v + KLift.untr e w)) q.1 q.2 j) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun j => by
        show e ((Λ (e.symm c • KLift.untr e v)) q.1 q.2 j) = c * e ((Λ (KLift.untr e v)) q.1 q.2 j)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁))) :=
    KLift.finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (KLift.latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (KLift.heO_br i dc hn) (locRep ρP) ρP KLift.mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) KLift.mkK_span)
  refine sub_of_fam (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (KLift.untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', a)) b
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext j
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (KLift.untr e v))) q.1 q.2 j) =
          (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r (Dd.p q.1)) g).mulVec (Ψ q v) j := by
      intro γ hγ
      rw [hΛe, hγ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, locC_apply i dc hn, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
        Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rDuO, twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.transpose_apply, Ψ, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [show eK (D.nbr i _ hn) = e from rfl]
      have hc : ∀ x y z w : Br.LLw (D.nbr i _ hn), x * y * (z * w) = x * y * w * z := fun x y z w => by ring
      exact hc _ _ _ _
    exact key (Br.iota D.nbr i _ hn g) rfl

end Rec

end Formalism.MainNotions.N.KRowA

end
end

-- bundled from Formalism.AdmissibleDesigns.MsWApply
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.StC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf Formalism.MainNotions.N.K.TBa Formalism.MainNotions.N.KLift

section EmbRow

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem msW_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i w hw) (a b : Fin D.R.nV) :
    MsW i r hw x g a b = eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (rTwO D.nd i r x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b)) := by
  rw [msW_entry]
  first
  | rfl
  | simp [Matrix.map_apply]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem embRW_of {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (Formalism.MainNotions.N.RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    [Module.Finite (D.nd.O i) Dd.R']
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : EmbRW i dc r Dd hw := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  have := nzsd_R' i Dd
  have : Module.Free (D.nd.O i) Dd.R' := Module.free_of_finite_type_torsion_free'
  set ρP := resRep (lRep (D.nd.O i) Dd.r Dd.χ) (Dw i dc (idx i dc w)) with hρP
  set e := eS i hw
  let κ : Dd.R' →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) :=
    (Dd.R').val.toLinearMap
  have hκ : Function.Injective κ := Subtype.val_injective
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) κ
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = κ m := by
    intro m s
    rw [← map_smul, smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [hκ (h1.symm.trans (map_zero κ).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Dw i dc (idx i dc w))) v, Λ (locRep ρP γ v) =
      ((Formalism.NG.uElt Dd.r Dd.χ (γ : GE D.nd) : Dd.R') :
        Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * Λ v := by
    intro γ v
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply smul_cancel s
      rw [hΛs, ← mul_smul_comm, hΛs]
      rfl
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) Dd.R') →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) := fun q =>
    { toFun := fun v a => e ((Λ (untr e v)) q.1 a q.2)
      map_add' := fun v v₂ => funext fun a => by
        show e ((Λ (untr e v + untr e v₂)) q.1 a q.2) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun a => by
        show e ((Λ (e.symm c • untr e v)) q.1 a q.2) = c * e ((Λ (untr e v)) q.1 a q.2)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) (TrV e (MK (O := D.nd.O i) Dd.R')) :=
    finDim_of_lat (Ow := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Qp := ℚ_[D.nd.l i])
      (latOf e (selfO i hw) mkK (eW i dc hw).symm.toMonoidHom (heS i hw) (locRep ρP) ρP mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) mkK_span)
  have hinj : ∀ v, (∀ q, Ψ q v = 0) → v = 0 := by
    intro v hv
    have h0 : Λ (untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', b)) a
      simpa [Ψ] using this
    exact hΛi _ h0
  obtain ⟨m, xs, hxs⟩ := fin_sel Ψ hinj
  refine ⟨m, fun a => Dd.p (xs a).1, LinearMap.pi fun a => Ψ (xs a), fun v v' hvv => ?_, fun g v => funext fun a => ?_⟩
  · rw [← sub_eq_zero]
    refine hxs _ fun a => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun hvv a
  · have key : ∀ (q : Dd.X' × Fin D.R.nV) (γ : ↥(Dw i dc (idx i dc w))),
        (γ : GE D.nd) = ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) → ∀ b,
        e ((Λ (locRep ρP γ (untr e v))) q.1 b q.2) = (MsW i r hw (Dd.p q.1) g).mulVec (Ψ q v) b := by
      intro q γ hγ b
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΛe, Pi.mul_apply, hγ, uElt_at i r Dd hr' hsm hχ, Matrix.mul_apply, map_sum]
      simp only [Matrix.mulVec, dotProduct, msW_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [Ψ, Matrix.map_apply, map_mul]
      exact Or.inl rfl
    funext b
    exact key (xs a) ((eW i dc hw).symm g) rfl b

end EmbRow

end Formalism.MainNotions.N.K.StC

end
end

