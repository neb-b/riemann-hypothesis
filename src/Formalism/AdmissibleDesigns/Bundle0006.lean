module

public import Formalism.AdmissibleDesigns.TensSubsingleton
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.Bundle0004

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.MultVZeroOfSubsingleton
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Formalism.MainNotions.N.K.TBa

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem multV_zero_of_subsingleton {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [Subsingleton V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = 0 := by
  have hs : ∀ b, Subsingleton ↥(FildR PD ρ τ b) := fun b =>
    ⟨fun x y => Subtype.ext ((tens_subsingleton (x : V ⊗[Qp] BdR)).trans (tens_subsingleton (y : V ⊗[Qp] BdR)).symm)⟩
  unfold multV
  haveI := hs a
  haveI := hs (a + 1)
  rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  rfl

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL O) (hMc : ∀ x, Continuous (Ms x))
include hF hMc

theorem mult_sum_neg : ∀ (m : ℕ) (xs : Fin m → ι), IsCrys PD (sumRep Ms xs) →
    (∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD (sumRep Ms xs) τ a = 0 := by
  intro m
  induction m with
  | zero =>
    intro xs _ _ τ a _
    haveI : Subsingleton (Fin 0 → Fin k → LL) := inferInstance
    exact multV_zero_of_subsingleton PD _ τ a
  | succ m ih =>
    intro xs hc hJ τ a ha
    let A₀ : GRep G Qp LL O := sumG Ms hMc (fun a => xs a.succ)
    let A₁ : GRep G Qp LL O := sumG Ms hMc xs
    let A₂ : GRep G Qp LL O := matG Ms hMc (xs 0)
    let ι₀ : A₀.V →ₗ[LL] A₁.V := consZ (W := Fin k → LL) m
    let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0
    let σ₀ : A₂.V →ₗ[LL] A₁.V := consV (W := Fin k → LL) m
    have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := fun g x => funext fun a => by
      cases a using Fin.cases
      · show (0 : Fin k → LL) = (Ms (xs 0) g).mulVec 0
        rw [Matrix.mulVec_zero]
      · rfl
    have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := fun g x => rfl
    have hinj : Function.Injective ι₀ := consZ_inj (W := Fin k → LL) m
    have hsurj : Function.Surjective π₀ := fun v => ⟨σ₀ v, proj_consV (W := Fin k → LL) m v⟩
    have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := range_consZ (W := Fin k → LL) m
    have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
    obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
    have h0 : multV PD A₀.ρ τ a = 0 :=
      ih (fun a => xs a.succ) hc0 (fun j => hJ j.succ) τ a ha
    have h2 : multV PD A₂.ρ τ a = 0 := by
      by_contra hne
      have := hJ 0 τ a (jump_of_mult PD _ τ a hne)
      omega
    show multV PD A₁.ρ τ a = 0
    rw [hadd τ a, h0, h2, add_zero]

theorem decomp_neg (A₁ A₀ : GRep G Qp LL O) {m : ℕ} (xs : Fin m → ι)
    (e : A₁.V ≃ₗ[LL] A₀.V × (Fin m → Fin k → LL))
    (he : ∀ g v, e (A₁.ρ g v) = (A₀.ρ g (e v).1, sumRep Ms xs g (e v).2))
    (hc : IsCrys PD A₁.ρ)
    (hJ : ∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) :
    IsCrys PD A₀.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD A₁.ρ τ a = multV PD A₀.ρ τ a := by
  let A₂ : GRep G Qp LL O := sumG Ms hMc xs
  let ι₀ : A₀.V →ₗ[LL] A₁.V := e.symm.toLinearMap ∘ₗ LinearMap.inl LL A₀.V (Fin m → Fin k → LL)
  let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.snd LL A₀.V (Fin m → Fin k → LL) ∘ₗ e.toLinearMap
  have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := by
    intro g x
    apply e.injective
    show e (e.symm (A₀.ρ g x, 0)) = e (A₁.ρ g (e.symm (x, 0)))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_zero]
  have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := by
    intro g x
    show (e (A₁.ρ g x)).2 = sumRep Ms xs g (e x).2
    rw [he]
  have hinj : Function.Injective ι₀ := by
    intro x y h
    have h' : e.symm (x, 0) = e.symm (y, 0) := h
    have := congrArg Prod.fst (e.symm.injective h')
    exact this
  have hsurj : Function.Surjective π₀ := by
    intro y
    refine ⟨e.symm (0, y), ?_⟩
    show (e (e.symm (0, y))).2 = y
    rw [LinearEquiv.apply_symm_apply]
  have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      show (e (e.symm (x, 0))).2 = 0
      rw [LinearEquiv.apply_symm_apply]
    · intro hv
      have hv' : (e v).2 = 0 := hv
      refine ⟨(e v).1, ?_⟩
      show e.symm ((e v).1, 0) = v
      rw [← hv']
      exact e.symm_apply_apply v
  have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
  obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
  refine ⟨hc0, fun τ a ha => ?_⟩
  have h2 : multV PD A₂.ρ τ a = 0 := mult_sum_neg PD Ms hF hMc m xs hc2 hJ τ a ha
  rw [hadd τ a, h2, add_zero]

end Gen

section GenNT

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

section DR

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem isDR_congr (h : IsDR PD ρ) : IsDR PD ρ' := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsDR at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq.symm

end DR

section MatT

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {k : ℕ}
  (M : G →* Matrix (Fin k) (Fin k) LL) (ρ' : Representation LL G V) (e : V ≃ₗ[LL] (Fin k → LL))
  (he : ∀ g x, e (ρ' g x) = matRep M g (e x))
include he

theorem crys_of_mat (h : IsCrys PD (matRep M)) : IsCrys PD ρ' := by
  refine Norm.isCrys_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem multV_mat (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ' τ a = multV PD (matRep M) τ a :=
  Norm.multV_congr PD e he τ a

theorem dR_of_mat (h : IsDR PD (matRep M)) : IsDR PD ρ' := by
  refine isDR_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

end MatT

end GenNT

end Formalism.MainNotions.N.K.Font

end
end

-- bundled from Formalism.AdmissibleDesigns.NormalizedRingData
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem normalized_ring_data (hN : NormAt D.nd r ρ π)
    (hG1 : ∀ (γ : GE D.nd) (k : ℕ), (fun x : D.nd.X i => ((rO D.nd i r x γ).charpolyRev).coeff k) ∈ D.nd.T i)
    (hres : Submodule.span (kk D.nd i)
      (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤)
    (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hI : IdemHyp (D.nd.O i) (D.nd.T i) (repX D.nd r) π (blk D.R) eB e₁)
    (hX : DistinctEigenvalueCornerPerturbation (D.nd.O i) (D.nd.T i) (repX D.nd r) π D.R.t g0 eB s) :
    ∃ Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (blk D.R),
      RingDef (D.nd.O i) (D.nd.T i) (repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd ∧
      vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
        Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ∧
      ∃ (_ : IsNoetherian Dd.R' Dd.R')
        (_ : ∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'))
        (_ : ∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k)),
        Dd.Top (D.nd.T i) (one_le_letterBlockLength D.R) ∧
        ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := by
  obtain ⟨Dd, hD, ⟨i1, i2, -, i4, i5⟩, i3, hT⟩ := ring_objects_exist (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd)
    (repX D.nd r) π D.R.t (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX
  have hFree := fun Z => displayFree (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd) (repX D.nd r) π D.R.t
    (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX Dd hD hT Z
  have hp : Dd.p Dd.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  have hv : vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
      Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) := by
    rw [hp, Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
  refine ⟨Dd, hD, hv, i1, i2, i3, i4, i5, hT, ?_⟩
  intro _ _ _ _ _ _ _
  exact realDisplayAllK_of (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
    Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ Dd.δ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
    (epsU D.nd i) g0 _ (D.nd.T i) Dd.T' Dd.q Dd.b Dd.π' Dd.ρπ Dd.sE Dd.tE (chiU D.nd i 1 g0) hT
    (hFree (D.nd.Z i : Set (D.nd.X i))) (Formalism.RepresentationBoundsCohomology.SF.deltaO_eq hD) hv.symm

end Formalism.MainNotions.N.K

end
end

-- bundled from Formalism.AdmissibleDesigns.SmulEval
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Eval
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

structure EvS (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) : Prop where
  r_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
  chi_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    (((Dd.χ g : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)
  smul_eval : ∀ (f : Dd.T') (a : Dd.R') (x' : Dd.X'),
    ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x'
  blk_smul : ∀ (f : Dd.T') k (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k), f • m = ((f : Dd.X' → D.nd.O i) Dd.π') • m
  ρπ_eval : ∀ a : Dd.R', (Dd.ρπ a).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
    (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) Dd.π'
  ρk_eval : ∀ (a : Dd.R') k, (Dd.ρπ a).toSquareBlock (RepresentationBoundsCohomology.blk D.R) k = Dd.ρk k a
  pπ : Dd.p Dd.π' = π

theorem evS_of (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    EvS r π Dd := by
  obtain ⟨-, -, -, -, h4, -, h6, -, h8, -, h10, h11, -, -, -, -, h16, h17, -⟩ := hD
  exact ⟨fun g x' => h6 g x', fun g x' => h11 g x', h8, h10, h16, h17, h4⟩

end Eval

section GlobalTheory
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

theorem blkS_eq {c' : Fin D.R.t} (a : Fin D.R.nV) (h : RepresentationBoundsCohomology.blk D.R a = c'.succ) :
    a = (Fin.natAdd D.R.r c' : Fin (D.R.r + D.R.t)) := by
  have h' := h
  simp only [Formalism.MainNotions.N.RepresentationBoundsCohomology.blk, Formalism.MainNotions.N.RepresentationBoundsCohomology.blkG] at h'
  split_ifs at h' with h1
  · exact absurd h'.symm (Fin.succ_ne_zero c')
  · apply Fin.ext
    have h2 := congrArg Fin.val h'
    simp only [Fin.val_succ] at h2
    simp only [Fin.coe_natAdd]
    omega

theorem blkS_act (c' : Fin D.R.t) (a : Dd.R') (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) (hE : EvS r π Dd) :
    a • m = (Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) • m := by
  have hb : RepresentationBoundsCohomology.blk D.R (Fin.natAdd D.R.r c') = c'.succ := by
    simp only [Formalism.MainNotions.N.RepresentationBoundsCohomology.blk, Formalism.MainNotions.N.RepresentationBoundsCohomology.blkG]
    rw [dite_eq_right (by simp)]
    ext
    simp
  have hu : ∀ y : {x : Fin D.R.nV // RepresentationBoundsCohomology.blk D.R x = c'.succ}, y = ⟨Fin.natAdd D.R.r c', hb⟩ :=
    fun y => Subtype.ext (blkS_eq y.1 y.2)
  funext j
  show ∑ k, (Dd.ρk c'.succ a) j k • m k =
    (Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) • m j
  rw [Fintype.sum_eq_single j (fun k hk => absurd ((hu k).trans (hu j).symm) hk),
    ← hE.ρk_eval a c'.succ, hu j]
  rfl

end GlobalTheory

section LocQ
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


variable {i r ρ π Dd} in
theorem rblkS (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd) :
    Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') =
      ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  have h3 : (Dd.ρπ (Dd.r g)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
      (rO D.nd i r π g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := by
    rw [hE.ρπ_eval, hE.r_eval, hE.pπ]
  have h4 := congrFun (congrFun h3 (Fin.natAdd D.R.r c')) (Fin.natAdd D.R.r c')
  have h5 : Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') =
      rO D.nd i r π g (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) h4
  rw [h5]
  exact hN.2.1 g c'


variable {i r ρ π Dd} in
theorem rS_act (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd)
    (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) :
    Dd.r g • m = ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) • m := by
  rw [blkS_act c' (Dd.r g) m hE, rblkS hE hN c' g]

end LocQ

end Formalism.MainNotions.N.K.ShaT

end
end

