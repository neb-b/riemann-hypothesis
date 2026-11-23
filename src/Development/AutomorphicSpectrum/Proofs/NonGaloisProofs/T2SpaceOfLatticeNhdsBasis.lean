module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0069

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.FinT

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {LL O V : Type} [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_smulTop (L : Lattice (O := O) ρ) (ϖ : O) (x : ↥L.T) :
    x ∈ (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, ϖ • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem fg_Z1T [TopologicalSpace LL] [ContinuousSMul LL V] [IsTopologicalAddGroup V] [T2Space V] (L : Lattice (O := O) ρ) {ϖ : O}
    (h0 : algebraMap O LL ϖ ≠ 0)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V)))
    (hK : IsCompact (Set.range (algebraMap O LL)))
    (hI : StableSub L (Ideal.span {ϖ ^ 1} • ⊤ : Submodule O ↥L.T)) (hfin : Finite ↥(quotientCocycles L _ hI)) :
    (latticeCocycles L).FG :=
  _root_.UpperTheory.Reformulated.B.Gub2.fg_Z1T L h0 hB hK hI hfin

theorem t2Space_of_lattice_nhds_basis [IsTopologicalAddGroup V] [IsNoetherianRing O] [IsLocalRing O] (L : Lattice (O := O) ρ) {ϖ : O}
    (hϖ : ¬ IsUnit ϖ)
    (hB : (nhds (0 : V)).HasBasis (fun _ : ℕ => True) (fun n => (fun x => ϖ ^ n • x) '' (L.T : Set V))) :
    T2Space V := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => ?_
  by_contra hcon
  push_neg at hcon
  have hin : ∀ n : ℕ, ∃ t ∈ L.T, ϖ ^ n • t = x := fun n => hcon _ (hB.mem_of_mem (i := n) trivial)
  haveI : Module.Finite O ↥L.T := Module.Finite.iff_fg.2 L.fg
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥L.T) (Ideal.span {ϖ})
    (fun h => hϖ (Ideal.span_singleton_eq_top.1 h))
  obtain ⟨t₀, ht₀, he₀⟩ := hin 0
  have hxT : x ∈ L.T := by
    rw [pow_zero, one_smul] at he₀
    exact he₀ ▸ ht₀
  have hmem : (⟨x, hxT⟩ : ↥L.T) ∈ (⨅ i : ℕ, (Ideal.span {ϖ}) ^ i • (⊤ : Submodule O ↥L.T)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨t, ht, he⟩ := hin n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨t, ht⟩, trivial, Subtype.ext he⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hx (congrArg Subtype.val hmem)

def toV (L : Lattice (O := O) ρ) : LatticeCohomology L →ₗ[O] H1V ρ :=
  Submodule.liftQ _
    (((Submodule.mkQ ((B1 ρ).comap (continuousCocycles ρ).subtype)).restrictScalars O) ∘ₗ
      { toFun := fun c => ⟨(c : G → V), c.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
    (by
      rintro c ⟨x, _, hx⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨x, hx⟩)

theorem toV_mk (L : Lattice (O := O) ρ) (c : ↥(latticeCocycles L)) :
    toV L (Submodule.Quotient.mk c) = Submodule.Quotient.mk ⟨(c : G → V), c.2.1⟩ := rfl

theorem isLocalized_toV [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) {ϖ : O} (h0 : ϖ ≠ 0)
    (hInt : ∀ c : G → V, Continuous c → ∃ n : ℕ, ∀ g, ϖ ^ n • c g ∈ L.T) :
    IsLocalizedModule (nonZeroDivisors O) (toV L) := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    have hs : algebraMap O LL (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro x y hxy
      have hxy' : (s : O) • x = (s : O) • y := hxy
      rw [← algebraMap_smul LL (s : O) x, ← algebraMap_smul LL (s : O) y] at hxy'
      exact smul_right_injective _ hs hxy'
    · intro y
      refine ⟨(algebraMap O LL (s : O))⁻¹ • y, ?_⟩
      change (s : O) • ((algebraMap O LL (s : O))⁻¹ • y) = y
      rw [← algebraMap_smul LL (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨n, hn⟩ := hInt (c : G → V) c.2.1
    have hz : ϖ ^ n • (c : G → V) ∈ latticeCocycles L :=
      ⟨(continuousCocycles ρ).restrictScalars O |>.smul_mem _ c.2, fun g _ => hn g⟩
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hz⟩, ⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩⟩, ?_⟩
    rfl
  · intro x₁ x₂ h
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x₁
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x₂
    rw [toV_mk, toV_mk, Submodule.Quotient.eq] at h
    obtain ⟨v, hv⟩ := h
    obtain ⟨n, hn⟩ := hInt (fun _ => v) continuous_const
    refine ⟨⟨ϖ ^ n, pow_mem (mem_nonZeroDivisors_of_ne_zero h0) n⟩, ?_⟩
    rw [Submonoid.mk_smul, Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    refine ⟨ϖ ^ n • v, hn 1, ?_⟩
    funext g
    have hvg : ρ g v - v = (a : G → V) g - (b : G → V) g := congrFun hv g
    change ρ g (ϖ ^ n • v) - ϖ ^ n • v = ϖ ^ n • (a : G → V) g - ϖ ^ n • (b : G → V) g
    rw [← smul_sub, ← hvg, ← algebraMap_smul LL (ϖ ^ n) v, map_smul, ← smul_sub, algebraMap_smul]

end Gen

end GlobalTheory.CompanionTheory.LocDual.FinT
