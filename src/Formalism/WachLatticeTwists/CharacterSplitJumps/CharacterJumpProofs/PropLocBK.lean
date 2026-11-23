module

public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
public import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Imports
public import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
public import Formalism.WachLatticeTwists.TorsionLengthCounts.Bundle0001
public import Formalism.WachLatticeTwists.HodgeTateChains.H2KilledByTateDuality
public import Formalism.WachLatticeTwists.HodgeTateChains.Statement
public import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.Bundle0001
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice

@[expose] public section

open Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem bkbConv : StatBKbConv := by
  intro O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' h1 h2 h3 h4
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_annih]
    intro t ht
    rw [h3, (h1 a).1 ha _ ht, Submodule.Quotient.mk_zero]
  · intro hx
    rw [mem_annih] at hx
    let ψ : HT' →ₗ[O] HV' ⧸ HfV' := (HfV'.mkQ.restrictScalars O) ∘ₗ j'
    have hle : LinearMap.ker ψ ≤ LinearMap.ker (pr x) := by
      intro t ht
      rw [LinearMap.mem_ker] at ht ⊢
      apply hx t
      show j' t ∈ HfV'
      exact (Submodule.Quotient.mk_eq_zero HfV' (x := j' t)).1 ht
    let φ0 := (LinearMap.ker ψ).liftQ (pr x) hle
    let e := ψ.quotKerEquivRange
    let φbar : LinearMap.range ψ →ₗ[O] KO O := φ0 ∘ₗ e.symm.toLinearMap
    have hφ : ∀ t, φbar ⟨ψ t, LinearMap.mem_range_self ψ t⟩ = pr x t := by
      intro t
      show φ0 (e.symm ⟨ψ t, LinearMap.mem_range_self ψ t⟩) = pr x t
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      try rfl
    haveI hnz : NoZeroSMulDivisors O (HV' ⧸ HfV') := by
      refine ⟨fun {c v} hcv => ?_⟩
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        have hc' : algebraMap O (FractionRing O) c ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hc
        have h' : algebraMap O (FractionRing O) c • v = 0 := by
          rw [algebraMap_smul]
          exact hcv
        exact (smul_eq_zero.1 h').resolve_left hc'
    haveI : Module.Free O (LinearMap.range ψ) := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis O (LinearMap.range ψ)
    have hcex : ∀ i, ∃ y : FractionRing O, Formalism.RepresentationBoundsCohomology.LOC.toKO O y = φbar (b i) :=
      fun i => Submodule.mkQ_surjective _ _
    choose c hc using hcex
    have hli0 : LinearIndependent O (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) :=
      b.linearIndependent.map' (LinearMap.range ψ).subtype (Submodule.ker_subtype _)
    have hli : LinearIndependent (FractionRing O)
        (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) := by
      first
      | exact (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hli0
      | exact (LinearIndependent.iff_fractionRing (R := O) (K := FractionRing O)).1 hli0
    obtain ⟨G, hG⟩ : ∃ G : (HV' ⧸ HfV') →ₗ[FractionRing O] FractionRing O,
        ∀ i, G ((b i : LinearMap.range ψ) : HV' ⧸ HfV') = c i := by
      obtain ⟨G, hG⟩ :=
        LinearMap.exists_extend ((Finsupp.linearCombination (FractionRing O) c) ∘ₗ hli.repr)
      refine ⟨G, fun i => ?_⟩
      have h := LinearMap.congr_fun hG ⟨_, Submodule.subset_span ⟨i, rfl⟩⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single i _ rfl,
        Finsupp.linearCombination_single, one_smul] at h
      exact h
    obtain ⟨a, ha⟩ := h2 (G ∘ₗ HfV'.mkQ)
    have haV : a ∈ HfV := (h1 a).2 fun bb hbb => by
      rw [ha, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero HfV').2 hbb, map_zero]
    have key : (Formalism.RepresentationBoundsCohomology.LOC.toKO O) ∘ₗ (G.restrictScalars O) ∘ₗ (LinearMap.range ψ).subtype = φbar :=
      b.ext fun i => by
        show Formalism.RepresentationBoundsCohomology.LOC.toKO O (G ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) = φbar (b i)
        rw [hG i, hc i]
    have hpr : ∀ t, pr (q a) t = pr x t := by
      intro t
      rw [h3, ha, ← hφ t]
      exact LinearMap.congr_fun key ⟨ψ t, LinearMap.mem_range_self ψ t⟩
    refine ⟨a, haV, ?_⟩
    have hz := h4 (q a - x) (fun t => by rw [map_sub, LinearMap.sub_apply, hpr t, sub_self])
    exact sub_eq_zero.1 hz

theorem rowBK : StatRowBK := by
  intro O _ _ _ X _ _ Hc HV Cs HV' _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' F Fs h1 h2 h3 h4 hF hFs
  rw [hF, hFs, bkbConv O Hc HV Cs HV' q j' pr pair HfV HfV' h1 h2 h3 h4]

end Formalism.RepresentationBoundsCohomology.JT
