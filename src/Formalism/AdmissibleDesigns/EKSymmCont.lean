module

public import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
public import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
public import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
public import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.Bundle0001

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Module Formalism.MainNotions.N.KHf Formalism.NG

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL)

abbrev modO (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module O (TrV e V) :=
  Module.compHom (TrV e V) (e.toRingHom.comp (algebraMap O (FractionRing O)))

theorem contSMulO (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c)) (V : Type)
    [AddCommGroup V] [Module (FractionRing O) V] :
    letI := modO e V
    ContinuousSMul O (TrV e V) := by
  letI := modO e V
  exact ⟨(ModuleTopology.continuousSMul LL (TrV e V)).continuous_smul.comp
    ((hO.comp continuous_fst).prodMk continuous_snd)⟩

variable {A : Type} [Ring A] [Algebra O A]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [Module A V]

def smulL (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    letI := modO e V
    A →ₗ[O] TrV e V :=
  letI := modO e V
  { toFun := fun a => (a • v : V)
    map_add' := fun a b => add_smul a b v
    map_smul' := fun c a => by
      show (c • a) • v = e.symm (e (algebraMap O (FractionRing O) c)) • (a • v : V)
      rw [RingEquiv.symm_apply_apply, algebraMap_smul, Algebra.smul_def, mul_smul, hP] }

theorem smul_cont [TopologicalSpace A] [IsModuleTopology O A]
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    Continuous fun a : A => (show TrV e V from (a • v : V)) := by
  letI := modO e V
  haveI := contSMulO e hO V
  haveI : ContinuousAdd (TrV e V) := ModuleTopology.continuousAdd LL (TrV e V)
  exact (IsModuleTopology.continuous_of_linearMap (R := O) (smulL e hP v) :)

theorem orbit_cont {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ]
    (ι : G →* Γ) (hι : Continuous ι) [TopologicalSpace A] [IsModuleTopology O A]
    (u : Γ → A) (hu : Continuous u) (ρ : Representation O Γ V) (hρ : ∀ g v, ρ g v = u g • v)
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : TrV e V) :
    Continuous fun g => repL e ρ ι g v := by
  refine ((smul_cont e hO hP v).comp (hu.comp hι)).congr fun g => ?_
  show u (ι g) • (show V from v) = ρ (ι g) v
  exact (hρ _ _).symm

end Gen

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem eK_alg_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) := by
  have h : (fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c)) =
      fun c => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO c) :=
    funext fun c => by rw [eK_apply, Br.toLLK_alg]
  rw [h]
  exact continuous_subtype_val.comp (D.nbr i w hw).eO_cont

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem uElt_cont_n
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (n : ℕ) :
    letI := K.Topo.rTopology (D.nd.O i) Dd.R'
    Continuous fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd) := by
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  exact (K.Topo.uElt_cont (hD := hD) (hc := hc)).comp continuous_subtype_val

theorem orbC_uRep
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {V : Type} [AddCommGroup V] [Module Dd.R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass Dd.R' (D.nd.O i) V]
    (hP : ∀ (c : D.nd.O i) (v : V), (algebraMap (D.nd.O i) Dd.R' c) • v = c • v) (n : ℕ) :
    OrbC i dc (resRep (uRep (D.nd.O i) (M := V) Dd.r Dd.χ) (Γn i dc n)) := by
  intro hn v
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  haveI : IsModuleTopology (D.nd.O i) Dd.R' := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  have hι : Continuous (Br.iota D.nbr i _ hn) := (D.nbr i _ hn).e_symm_cont.congr fun g => rfl
  exact orbit_cont (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) hι
    (fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd)) (uElt_cont_n i dc r π g0 eB e₁ s Dd hD hc n)
    _ (fun g v => rfl) (eK_alg_cont i _) hP v

theorem orbC_repE
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x' : Dd.X') (n : ℕ) :
    letI := evalModO i (R' := Dd.R') x'
    haveI := evalTower i (R' := Dd.R') x'
    OrbC i dc (repE i dc Dd.r Dd.χ x' n) := by
  letI := evalModO i (R' := Dd.R') x'
  haveI := evalTower i (R' := Dd.R') x'
  haveI := evalComm i (R' := Dd.R') x'
  haveI := smulComm_O i (A := Dd.R') (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
  exact orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (fun c v => evalScalar i x' c v) n

theorem latM_alg {n : Type} [Fintype n] [DecidableEq n] (ρ : Dd.R' →ₐ[D.nd.O i] Matrix n n (D.nd.O i))
    (c : D.nd.O i) (v : Formalism.RepresentationBoundsCohomology.SF.LatM (D.nd.O i) (FractionRing (D.nd.O i)) n ρ.toRingHom) :
    (algebraMap (D.nd.O i) Dd.R' c) • v = c • v := by
  funext j
  show ∑ k, (ρ (algebraMap (D.nd.O i) Dd.R' c)) j k • v k = c • v j
  rw [AlgHom.commutes]
  simp [Matrix.algebraMap_matrix_apply, Finset.sum_ite_eq, ite_smul]

end Rec

section Homeo

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem eK_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)) 0
  rw [← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), ← hemb.continuousAt_iff]
  exact (eK_alg_cont i hw).continuousAt

theorem eK_symm_val (z : Br.Ow (D.nbr i w hw)) :
    (eK (D.nbr i w hw)).symm (z : Br.LLw (D.nbr i w hw)) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) := by
  rw [RingEquiv.symm_apply_eq, eK_apply, Br.toLLK_alg, RingEquiv.apply_symm_apply]
  rfl

theorem eK_symm_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)).symm := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  have hOemb : Topology.IsOpenEmbedding
      (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) :=
    ⟨Topology.IsEmbedding.subtypeVal, ReciprocityTheory.ChartRestriction.T2.GlobAlg.isOpen_range_OL (D.nbr i w hw).LL⟩
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).symm.toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)).symm 0
  rw [← map_zero (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))), ← hOemb.continuousAt_iff]
  have hfun : ((eK (D.nbr i w hw)).symm ∘ algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) =
      fun z => algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) :=
    funext fun z => eK_symm_val i hw z
  rw [hfun]
  exact (hemb.continuous.comp (D.nbr i w hw).eO_symm_cont).continuousAt

theorem homeoK :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.HomeoK (eK (D.nbr i w hw)) := by
  exact ⟨eK_cont i hw, eK_symm_cont i hw⟩

theorem topMatch_pi (n : Type) [Finite n] :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.TopMatch (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  letI τ : TopologicalSpace (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    (Pi.topologicalSpace : TopologicalSpace (n → FractionRing (D.nd.O i)))
  let φ : (n → Br.LLw (D.nbr i w hw)) ≃L[Br.LLw (D.nbr i w hw)]
      TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) :=
    { toFun := fun v j => (eK (D.nbr i w hw)).symm (v j)
      invFun := fun x j => eK (D.nbr i w hw) (x j)
      left_inv := fun v => funext fun j => (eK (D.nbr i w hw)).apply_symm_apply (v j)
      right_inv := fun x => funext fun j => (eK (D.nbr i w hw)).symm_apply_apply (x j)
      map_add' := fun v v' => funext fun j => map_add (eK (D.nbr i w hw)).symm (v j) (v' j)
      map_smul' := fun c v => funext fun j => map_mul (eK (D.nbr i w hw)).symm c (v j)
      continuous_toFun := continuous_pi fun j => (eK_symm_cont i hw).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => (eK_cont i hw).comp (continuous_apply j) }
  have hM : IsModuleTopology (Br.LLw (D.nbr i w hw)) (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    IsModuleTopology.iso φ
  exact hM.1.symm

end Homeo

section Cyc

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Cyc

section Row

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

end Row

section RowTop

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

end RowTop

section Ms

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem rTwO_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (x : D.nd.X i) : Continuous (rTwO D.nd i r x) := by
  have hχ : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((chiU D.nd i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact hχ.smul (hc x)

theorem locC_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  have h1 : Continuous fun g : Br.G D.nbr i w hw =>
      rTwO D.nd i r x ((Br.iota D.nbr i w hw g : _) : GE D.nd) :=
    (rTwO_cont i r hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact ((h1.matrix_map (D.nbr i w hw).eO_cont).matrix_map continuous_subtype_val).matrix_map hinc

end Ms

end Formalism.MainNotions.N.KOrb

end
