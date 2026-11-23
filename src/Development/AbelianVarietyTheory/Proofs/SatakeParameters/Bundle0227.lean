module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0225
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingEquivTranscendental
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceInd

open GlobalTheory.IdemSplit GlobalTheory.CongSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def epsOff (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) : AL L :=
  ∏ v ∈ T, (1 - idemAt L v)

theorem compAt_epsOff_of_mem {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ∈ T) :
    compAt L w (epsOff L T) = 0 := by
  rw [epsOff, map_prod]
  exact Finset.prod_eq_zero hw (by rw [map_sub, map_one, compAt_idemAt_self, sub_self])

theorem epsOff_mem (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    epsOff L T ∈ ALint L :=
  Subring.prod_mem _ fun v _ => Subring.sub_mem _ (one_mem _) (idemAt_mem L v)

theorem epsOff_insert [DecidableEq (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))]
    {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hv : v ∉ T) :
    epsOff L (insert v T) = (1 - idemAt L v) * epsOff L T := by
  rw [epsOff, Finset.prod_insert hv, epsOff]

theorem epsOff_mono {T T' : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (h : T ⊆ T') :
    ∃ c ∈ ALint L, epsOff L T' = c * epsOff L T := by
  classical
  exact ⟨epsOff L (T' \ T), epsOff_mem L _, (Finset.prod_sdiff h).symm⟩

theorem exists_epsOff_mul_mem (z : AL L) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), epsOff L T * z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, h⟩ := GlobalTheory.FormInner.exists_int_off z
  refine ⟨S, ?_⟩
  have e : epsOff L S * z = epsOff L S * Y := by
    apply sub_eq_zero.1
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, map_mul]
    by_cases hw : w ∈ S
    · rw [compAt_epsOff_of_mem L hw]; ring
    · rw [h w hw]; ring
  rw [e]
  exact Subring.mul_mem _ (epsOff_mem L S) hY

theorem gaFold_split {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n)
    (he : idemAt L v * idemAt L v = idemAt L v) (hσ : conjAL L (idemAt L v) = idemAt L v)
    (he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v)
    (hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v) :
    g = gaFold he hσ g * gaFold he' hσ' g := by
  apply Subtype.ext; apply Units.ext
  show (g.1 : Matrix (Fin n) (Fin n) (AL L)) = fold (idemAt L v) _ * fold (1 - idemAt L v) _
  rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

theorem ind_epsOff (n N : ℕ) (p : GAf L n → Prop) (hC : ∀ κ, NG.Cong L n N κ → p κ)
    (hstep : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n),
      TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y))
    (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    ∀ g : GAf L n, (∀ i j, ∃ y ∈ ALint L, epsOff L T * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (N : AL L) * y) → p g := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have hg' : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y := by
      intro i j
      obtain ⟨y, hy, e⟩ := hg i j
      rw [epsOff, Finset.prod_empty, one_mul] at e
      exact ⟨y, hy, e⟩
    apply hC
    refine ⟨fun i j => ?_, hg'⟩
    obtain ⟨y, hy, e⟩ := hg' i j
    have h1 : (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * y := by rw [← e]; ring
    rw [h1]
    exact Subring.add_mem _ (one_apply_mem L i j) (Subring.mul_mem _ (natCast_mem _ _) hy)
  | @insert v T hv ih =>
    intro g hg
    have he : idemAt L v * idemAt L v = idemAt L v := idemAt_mul_self L v
    have he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v := by
      rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
    have hσ : conjAL L (idemAt L v) = idemAt L v := conjAL_idemAt L v
    have hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v := by rw [map_sub, map_one, hσ]
    have hx : TrivOutside {v} (gaFold he hσ g) := by
      intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
        compAt_idemAt_ne L v hw', compAt_one_apply]
      simp
    have hy : TrivOutside {v}ᶜ (gaFold he' hσ' g) := by
      intro w hw
      have hw' : w = v := by simpa using hw
      rw [hw']
      ext i j
      simp only [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_sub, map_one,
        compAt_idemAt_self, compAt_one_apply]
      simp
    have hp : p (gaFold he' hσ' g) := by
      apply ih
      intro i j
      obtain ⟨y, hy, eq⟩ := hg i j
      refine ⟨y, hy, ?_⟩
      rw [epsOff_insert L hv] at eq
      rw [gaFold_val, fold_apply]
      linear_combination eq
    have := hstep v _ _ hx hy hp
    rwa [← gaFold_split L v g he hσ he' hσ'] at this

theorem induction_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  intro L _ _ _ n N hN p hC hstep g
  classical
  have hN' : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 :=
    ⟨algebraMap L (AL L) (N : L)⁻¹, by
      rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hN', map_one]⟩
  have hT : ∀ q : Fin n × Fin n, ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))),
      epsOff L T * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2 -
        (1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2)) ∈ ALint L :=
    fun q => exists_epsOff_mul_mem L _
  choose T hT using hT
  refine ind_epsOff L n N p hC hstep (Finset.univ.biUnion T) g fun i j => ?_
  obtain ⟨c, hc, e⟩ := epsOff_mono L (Finset.subset_biUnion_of_mem T (Finset.mem_univ (i, j)))
  refine ⟨c * (epsOff L (T (i, j)) * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))), Subring.mul_mem _ hc (hT (i, j)), ?_⟩
  rw [e]
  linear_combination (-(c * epsOff L (T (i, j)) * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))) * hu

end GlobalTheory.PlaceInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSplitExactTwistCountProduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BlockSplitProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_mul (α β : ℂˣ) : unrChar k (α * β) = unrChar k α * unrChar k β := by
  refine MonoidHom.ext fun x => ?_
  simp [unrChar_apply, mul_zpow]

theorem twist_detRep (n : Type) [Fintype n] [DecidableEq n] (ψ φ : kˣ →* ℂˣ) :
    twist (detRep n ψ) (detChar n φ) = detRep n (ψ * φ) := by
  refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
  simp [detRep, ofChar_apply, twist_apply, mul_comm, mul_left_comm, mul_assoc]

theorem nonempty_equiv_of_cast {n m : ℕ} (h : n = m) (x : Irr k n) (ψ : kˣ →* ℂˣ)
    (e : Nonempty ((h ▸ x : Irr k m).π.Equiv (detRep (Fin m) ψ))) :
    Nonempty (x.π.Equiv (detRep (Fin n) ψ)) := by
  subst h; exact e

theorem eq_one_of_inSupport {m : ℕ} (τ : Irr k m) (hc : IsCuspidal τ.π) {ψ : kˣ →* ℂˣ}
    (h : InSupport τ.π ψ) : m = 1 ∧ Nonempty (τ.π.Equiv (detRep (Fin m) ψ)) := by
  rcases m with _ | _ | m
  · exact absurd h (Model.not_inSupport_zero _ _)
  · obtain ⟨ω, hω, ⟨φ⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ τ.π τ.smooth τ.irr
    have h1 : InSupport (detRep (Fin 1) ω) ψ :=
      JacquetExact.inSupport_of_isSubquotient k _ _ _ τ.π _ ψ ((isSmooth_ofChar_iff _).2 hω.detChar)
        (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) h
    obtain rfl := (Model.inSupport_one_iff ω ψ).1 h1
    exact ⟨rfl, ⟨φ⟩⟩
  · exact absurd h (Model.not_inSupport_of_isCuspidal hc ψ)

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n s : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a))
    (ψ : kˣ →* ℂˣ) (hc : IsCuspSupport π d (fun a => (σ a).π)) (h : InSupport π ψ) :
    ∃ a, d a = 1 ∧ Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) ψ)) := by
  obtain ⟨-, hσ, e, hsub⟩ := hc
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ π _ ψ (isSmooth_parInd _ _) hsub h
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k (Fin s) (fun a => Fin (d a)) (Fin n) e _
    (fun a => (σ a).π) ψ (fun a => (σ a).smooth) (fun a => (σ a).irr) h1
  exact ⟨a, eq_one_of_inSupport (σ a) (hσ a).2.2 ha⟩

theorem reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)),
      IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) →
      (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
        ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) →
      ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t →
      ∃ (π₁ : Irr k r) (π₂ : Irr k t) (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s),
        (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧
        IsCuspSupport π₁.π (fun a => d (ι₁ a)) (fun a => (σ (ι₁ a)).π) ∧
        IsCuspSupport π₂.π (fun b => d (ι₂ b)) (fun b => (σ (ι₂ b)).π) ∧
        IsSubquotient π.π (prod₂ π₁.π π₂.π) := by
  intro hB hG hU k _ _ _ _ r t s π d σ S hc hS1 hlink hr ht
  have hσ := hc.2.1
  obtain ⟨s₁, s₂, ι₁, ι₂, e₁, e₂, V₁, V₂, _, _, _, _, ρ₁, ρ₂, m1, m2, sm1, sm2, ⟨φ₁⟩, ⟨φ₂⟩, hsub⟩ :=
    _root_.GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  obtain ⟨π₁, π₂, h1, h2, h3⟩ := _root_.GlobalTheory.ProdSubquot.irreducible_subquotient_prod₂ hB k r t V₁ V₂ ρ₁ ρ₂ π sm1 sm2
    ((_root_.GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength hB k s₁ r (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) e₁).of_equiv φ₁.symm)
    ((_root_.GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength hB k s₂ t (fun b => d (ι₂ b)) (fun b => σ (ι₂ b)) e₂).of_equiv φ₂.symm) hsub
  exact ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2,
    ⟨π₁.irr, fun a => hσ (ι₁ a), e₁, h1.trans (IsSubquotient.of_injective φ₁.toIntertwiningMap φ₁.toLinearEquiv.injective)⟩,
    ⟨π₂.irr, fun b => hσ (ι₂ b), e₂, h2.trans (IsSubquotient.of_injective φ₂.toIntertwiningMap φ₂.toLinearEquiv.injective)⟩, h3⟩

end GlobalTheory.BlockSplitProd

open GlobalTheory.BlockSplitProd in
theorem GlobalTheory.BlockSplitProd.main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsSmoothChar χ → IsCuspSupport π.π d (fun a => (σ a).π) → Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} = t → ∃ (π₁ : Irr k r) (π₂ : Irr k t), Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) ∧ ∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α) := by
  intro hB hG hU k _ _ _ _ r t χ π s d σ _ hc hcard
  classical
  let S : Finset (Fin s) := Finset.univ.filter fun a =>
    d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))
  have hS : S.card = t := by
    rw [← hcard, ← Set.ncard_coe_finset]
    congr 1
    ext a
    simp [S]
  have hS1 : ∀ b ∈ S, d b = 1 := fun b hb => (Finset.mem_filter.1 hb).2.1
  have htot : ∑ a, d a = r + t := by
    obtain ⟨e, -⟩ := hc.2.2
    simpa using Fintype.card_congr e
  have ht : ∑ a ∈ S, d a = t := by
    rw [Finset.sum_congr rfl hS1]
    simp [hS]
  have hr : ∑ a ∈ Sᶜ, d a = r := by
    have := Finset.sum_add_sum_compl S d
    omega
  have hlink : ∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ),
      ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α)))) := by
    intro a b ha hb h α ⟨φ⟩
    obtain ⟨hb1, β, ⟨ψ⟩⟩ := (Finset.mem_filter.1 hb).2
    have e1 : twist (detRep (Fin (d b)) (χ * unrChar k β)) (detChar (Fin (d b)) (unrChar k α)) =
        detRep (Fin (d b)) (χ * unrChar k (β * α)) := by
      rw [twist_detRep, unrChar_mul, mul_assoc]
    have ψ' := LocGL.twistEquiv ψ (detChar (Fin (d b)) (unrChar k α))
    rw [e1] at ψ'
    exact ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h.trans hb1, β * α,
      nonempty_equiv_of_cast h (σ a) _ ⟨φ.trans ψ'⟩⟩)
  obtain ⟨π₁, π₂, s₁, s₂, ι₁, ι₂, m1, m2, hc1, hc2, hsub⟩ :=
    reorder hB hG hU k r t s π d σ S hc hS1 hlink hr ht
  have hirr := hU k r t s₁ s₂ π₁ π₂ (fun a => d (ι₁ a)) (fun b => d (ι₂ b)) (fun a => σ (ι₁ a))
    (fun b => σ (ι₂ b)) hc1 hc2 fun a b h α => hlink _ _ (m1 a) (m2 b) h α
  obtain ⟨φ⟩ := IsSubquotient.nonempty_equiv hsub π.irr hirr
  refine ⟨π₁, π₂, ⟨φ.symm⟩, fun α hα => ?_⟩
  obtain ⟨a, ha1, hψ⟩ := exists_eq_of_inSupport hG π₁.π (fun a => d (ι₁ a)) (fun a => σ (ι₁ a)) _ hc1 hα
  exact m1 a (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha1, α, hψ⟩)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.KerShapeD

theorem thetaKernelShapeAtD_ofKer_of_hyp_adapted : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted →
    ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hH hA ep be sg
  intro u μ w hlev hcls i hi c c'
  have hpd : D.what₂.places.resChar w = D.host.d := by
    have h := hcls
    simp only [Host.cls, primeClass] at h
    split_ifs at h with h1 h2 h3 <;> first | exact h3 | cases h
  have hAd : AdPl D w := Or.inr (Or.inr hcls)
  have hlev' : LevFree Y u μ w := hlev
  obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hA w hAd u μ hlev'
  have hStd : ∀ j, j ≤ D.R.m → ∀ cl, GlobalTheory.KerStd.StdBases D (t.ent.lam w) ((t.O u μ).lat j cl).1 (Pm j cl) :=
    fun j hj cl => _root_.GlobalTheory.KerStd.stdBases_of_basR D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j cl).2.1 (fun τ => hBas j hj cl τ)
      (fun τ τ' h => hConj j hj cl τ τ' h)
  have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hH u μ w hlev' i hi c c'
  have hdg : IsDgen D t.cD := by
    rw [← t.O_dgen u μ]
    exact (t.O u μ).dgen_gen
  have hnorm : ∀ τ, ‖(fun _ => (1 : ℂ_[D.what₂.places.resChar w])) τ‖ ≤ ‖TaylorLogMetric.lamC (t.ent.lam w) (t.cD τ)‖ := by
    intro τ
    rw [GlobalTheory.EigenGenerator.norm_dgen_eq_one D t.cD hdg _ (t.ent.lam w) hpd τ]
    simp
  show OrbitPlaces.ShapeD D _ (t.ent.Th u μ w i c c')
  rw [hTh i hi c c', GlobalTheory.atLin_adCoef_eq_stdSer]
  exact _root_.GlobalTheory.Proof.shape_normalisedThetaCombinations_dualBases_at_d.shapeComb hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hcomb.1 _ (t.ent.lam w) hpd
    t.cD hdg (Pm i c) (Pm (i + 1) c') _ (hStd i hi.le c) (hStd (i + 1) hi c') hnorm _ hcomb.2

end GlobalTheory.Ggeo.KerShapeD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PtLocalPin

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_fixed_of_finset {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i), f ≠ 0 →
      (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) →
      ∃ S' ∈ t, ∃ g ∈ S', g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf hf0 _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    exact absurd hf hf0
  | insert a t ha ih =>
    intro hsub f hf hf0 hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ y = y := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ z = z := by
        intro κ hκ hκt
        have e := hfix κ hκ hκt
        rw [map_add (f := _), hyfix κ hκ hκt] at e
        exact add_left_cancel e
      by_cases hy0 : y = 0
      · subst hy0
        rw [zero_add] at hf0
        obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF z hz hf0 hzfix
        exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩
      · exact ⟨a, Finset.mem_insert_self a t, y, hy, hy0, hyfix⟩
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      obtain ⟨S', hS', g, hg, hg0, hgf⟩ := ih htF f ((sup_le hle le_rfl) hf) hf0 hfix
      exact ⟨S', Finset.mem_insert_of_mem hS', g, hg, hg0, hgf⟩

theorem fixed_of_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g' : GAf L n → W)
    (hg' : g' ∈ S') (hg0 : g' ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g' = g') :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨T, hT⟩ := hiso
  set g : S := T.symm ⟨g', hg'⟩ with hgdef
  have hTg : T g = ⟨g', hg'⟩ := T.apply_symm_apply _
  refine ⟨g, g.2, fun h => hg0 ?_, fun κ hκ ht => ?_⟩
  · have h0 : g = 0 := Subtype.ext h
    rw [h0, map_zero] at hTg
    exact (congrArg Subtype.val hTg).symm
  · have e := hT κ g ⟨_, hS.stable κ _ g.2⟩ rfl
    rw [hTg] at e
    have e' : T ⟨NG.rt L n κ g, hS.stable κ _ g.2⟩ = T g := by
      rw [hTg]
      exact Subtype.ext (e.trans (hfix κ hκ ht))
    exact congrArg Subtype.val (T.injective e')

theorem exists_fixed_of_isoTyp {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    (hS : NG.IsIrrRep ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (f : GAf L n → W)
    (hf : f ∈ NG.isoTyp ρ S) (hf0 : f ≠ 0) (hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    ∃ g ∈ S, g ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ g = g := by
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  obtain ⟨S', hS', g', hg', hg0, hgf⟩ := exists_fixed_of_finset v t ht f hft hf0 hfix
  exact fixed_of_iso hS.1 (ht hS').2 v g' hg' hg0 hgf

end Gen

theorem coeff_eq {N n : ℕ} (hN : N ≠ 0) {c c' : ℕ → ℂ}
    (h : (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c k) * X ^ (n - k) : ℂ[X]) =
      X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * c' k) * X ^ (n - k))
    {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n) : c k = c' k := by
  have key : ∀ d : ℕ → ℂ, (X ^ n + ∑ j ∈ Finset.Icc 1 n,
      C ((-1 : ℂ) ^ j * ((N : ℂ)) ^ (j * (j - 1) / 2) * d j) * X ^ (n - j) : ℂ[X]).coeff (n - k) =
        (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) * d k := by
    intro d
    rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff, Finset.sum_eq_single k]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro j hj hjk
      rw [Finset.mem_Icc] at hj
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro hk
      exact absurd (Finset.mem_Icc.2 ⟨h1, h2⟩) hk
  have e := congrArg (fun p : ℂ[X] => p.coeff (n - k)) h
  rw [key c, key c'] at e
  have hne : (-1 : ℂ) ^ k * ((N : ℂ)) ^ (k * (k - 1) / 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hN))
  exact mul_left_cancel₀ hne e

end GlobalTheory.PtLocalPin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TorsionTaylorAlgebraicLatticeExistsOfCm
section
namespace GlobalTheory.CurveThetaInert

theorem torsionTaylorAlgebraic_latticeExists_of_cm (h2 : Formalism.L2.Th1.CM.CM2) :
    Formalism.L2.KerInert.AlgTAll ∧ Formalism.L2.KerInert.GenusOneModelExistsLattice ∧ Formalism.L2.KerInert.Rep.CurveDict :=
  ⟨GlobalTheory.ThLoc.algTAll,
    GlobalTheory.InertGenusOne.datum_exists_lattice h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4,
    GlobalTheory.CurveDictionary.curveDict_of_cm h2 ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree ReciprocityTheory.ChartRestriction.L1.cm4⟩

end GlobalTheory.CurveThetaInert
end

