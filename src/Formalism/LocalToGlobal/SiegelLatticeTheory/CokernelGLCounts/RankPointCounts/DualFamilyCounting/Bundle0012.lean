module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FirstFamilyOperatorEnd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0040
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0011
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0035

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.BigLineBundleMoriwaki
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def ProjInto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ x ∈ Λ, X.projection Y hc x ∈ locF 𝔭 (dualIn h X L)

def ProjOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ (X Y : Submodule K V) (hc : IsCompl X Y), (∀ x ∈ X, ∀ y ∈ Y, h x y = 0) →
    ∀ L : Submodule (𝓞 K) V, IsLatIn X L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ Λ : Submodule (𝓞 K) V, (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      dualF h 𝔭 Λ = Λ → Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L →
      ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, X.projection Y hc x = v

def FibCount : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T ≠ 0 → fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭

end Formalism.L2.SG.Pf.G6

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G6

theorem glueLoc_of (hi : ProjInto) (ho : ProjOnto) (hn : FibCount) : GlueLoc := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭
  refine ⟨fun hne => ⟨?_, hn K F V hK hF h hs hnd U hcU M T hM hT 𝔭 h𝔭 hne⟩,
    fun g hg => fibP_gmap hM 𝔭 T hg⟩
  obtain ⟨⟨Λ, hΛ0, hΛd, hΛU, hΛW⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have oU : ∀ x ∈ U, ∀ y ∈ orthK h U, h x y = 0 := fun x hx y hy => mem_orthK.mp hy x hx
  have oW : ∀ x ∈ orthK h U, ∀ y ∈ U, h x y = 0 := by
    intro x hx y hy
    have e := hs.eq x y
    rw [oU y hy x hx] at e
    simpa using e
  exact discIso_of_proj h hcU hΛU hΛW
    (hi K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (ho K F V hK hF h hs hnd U (orthK h U) hcU oU M hM 𝔭 h𝔭 Λ hΛ0 hΛd hΛU)
    (hi K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)
    (ho K F V hK hF h hs hnd (orthK h U) U hcU.symm oW T hT 𝔭 h𝔭 Λ hΛ0 hΛd hΛW)

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardQuotSmulTopCongr
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G2

open Formalism.HermitianLattices.Ext.L3

theorem smul_top_pi {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (J : Ideal R) :
    (J • ⊤ : Submodule R (∀ i, N i)) =
      Submodule.pi Set.univ (fun i => J • (⊤ : Submodule R (N i))) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_pi]
    intro i _
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro v hv
    rw [Submodule.mem_pi] at hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have h1 : Pi.single i (v i) ∈ (J • (⊤ : Submodule R (N i))).map (LinearMap.single R N i) :=
      Submodule.mem_map_of_mem (hv i (Set.mem_univ i))
    rw [Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1

theorem card_quot_smul_top_congr {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) (J : Ideal R) :
    Nat.card (M ⧸ (J • ⊤ : Submodule R M)) = Nat.card (N ⧸ (J • ⊤ : Submodule R N)) := by
  refine Nat.card_congr (Submodule.Quotient.equiv _ _ f ?_).toEquiv
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem card_quot_quot {A : Type*} [CommRing A] (E J : Ideal A) :
    Nat.card ((A ⧸ E) ⧸ (J • ⊤ : Submodule A (A ⧸ E))) = Nat.card (A ⧸ (E ⊔ J)) := by
  have h1 : (J • ⊤ : Submodule A (A ⧸ E)) = Submodule.map E.mkQ J := by
    conv_lhs => rw [← Submodule.range_mkQ E, LinearMap.range_eq_map, ← Submodule.map_smul'',
      Ideal.smul_eq_mul, Ideal.mul_top]
  rw [h1]
  exact Nat.card_congr (Submodule.quotientQuotientEquivQuotientSup E J).toEquiv

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm (extP K 𝔭) := by
  have hc := Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow (K := K) 𝔭 1
  rw [pow_one, pow_one] at hc
  have h1 : extP K 𝔭 ≠ ⊤ := fun h => h𝔭.ne_top (by rw [← hc, h, Ideal.comap_top])
  have h0 : extP K 𝔭 ≠ ⊥ := by
    intro h
    have hne : 𝔭 ≠ ⊥ := fun h' =>
      NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.mpr (h' ▸ h𝔭))
    apply hne
    rw [← hc, h]
    ext t
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro ht
      have h2 : algebraMap F K (t : F) = 0 := by
        have h3 := congrArg (algebraMap (𝓞 K) K) ht
        rw [map_zero] at h3
        exact h3
      have h4 : (t : F) = 0 := (algebraMap F K).injective (by rw [h2, map_zero])
      exact_mod_cast h4
    · intro ht
      rw [ht, map_zero]
  have ha0 : Ideal.absNorm (extP K 𝔭) ≠ 0 := fun h => h0 (Ideal.absNorm_eq_zero_iff.mp h)
  have ha1 : Ideal.absNorm (extP K 𝔭) ≠ 1 := fun h => h1 (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem card_pi_quot (𝔭 : Ideal (𝓞 F)) {κ : Type} [Fintype κ] [DecidableEq κ] (e : κ → ℕ) (j : ℕ) :
    Nat.card ((∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i) ⧸
        (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (∀ i, 𝓞 K ⧸ extP K 𝔭 ^ e i))) =
      Ideal.absNorm (extP K 𝔭) ^ ∑ i, min (e i) j := by
  rw [smul_top_pi, Nat.card_congr (Submodule.quotientPi
    (fun i => (extP K 𝔭 ^ j • ⊤ : Submodule (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ e i)))).toEquiv,
    Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hsup : extP K 𝔭 ^ e i ⊔ extP K 𝔭 ^ j = extP K 𝔭 ^ min (e i) j := by
    rcases le_total (e i) j with h | h
    · rw [min_eq_left h, sup_eq_left.mpr (Ideal.pow_le_pow_right h)]
    · rw [min_eq_right h, sup_eq_right.mpr (Ideal.pow_le_pow_right h)]
  rw [card_quot_quot, hsup, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_pow]

end Formalism.L2.SG.Pf.G2
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOnto
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def diagQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (algebraMap (𝓞 F) (𝓞 K) (a i))

def phiQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Y + Yᴴ + Yᴴ * diagQ K 𝔭 k a * Y

def kerSet (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Set (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
  {X | Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a ∧ ∃ Y, X = 1 + Y * diagQ K 𝔭 k a}

def PhiCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 1 ≤ k → ∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
      (Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} : ℝ) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * k) * alphaStd K 𝔭 (m - cJof 𝔭 a)

def KerCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → ∀ N : ℕ,
      (∀ T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Tᴴ = T →
        (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) →
        Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) // phiQ K 𝔭 k a Y = T} = N) →
      Nat.card (kerSet K 𝔭 k a) = N

def DiscOnto : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k →
      akCount h L 𝔭 k = discAut h ⊤ L 𝔭 * Nat.card (kerSet K 𝔭 k a)

end Formalism.L2.SG.Pf.G5
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLatticeLocF
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := fun x hx => hL.2 ▸ Submodule.subset_span hx

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) :=
  Submodule.IsLattice.of_fg K (hA.1.sup hB.1)

theorem prO_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V} (hz : z ∈ A ⊔ B) : prO hc z ∈ A := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  rw [map_add (f := _), prO_apply, prO_apply, Submodule.projection_apply_of_mem_left hc (hA a ha),
    (Submodule.projection_apply_eq_zero_iff hc).2 (hB b hb), add_zero]
  exact ha

theorem prO_locF {X Y : Submodule K V} (hc : IsCompl X Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime)
    {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ y ∈ B, y ∈ Y) {z : V}
    (hz : z ∈ locF 𝔭 (A ⊔ B)) : prO hc z ∈ locF 𝔭 A := by
  obtain ⟨t, ht, htz⟩ := (LocF.mem_locF_iff hp _ z).1 hz
  refine (LocF.mem_locF_iff hp _ _).2 ⟨t, ht, ?_⟩
  rw [← LinearMap.map_smul]
  exact prO_sup hc hA hB htz

theorem discMod_finite [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hc : IsCompl U (orthK h U)) {M T Λ₀ N₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T)
    (hN₀ : Submodule.IsLattice K N₀) (hΛ₀ : locF 𝔭 N₀ = Λ₀)
    (hW : Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T)
    (hiW : ∀ x ∈ Λ₀, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T))
    (hpr : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ₀, prO hc.symm x = v) :
    Finite (DiscMod h (orthK h U) T 𝔭) := by
  subst hΛ₀
  have hp := h𝔭.isPrime
  have hTM : Submodule.IsFullLattice K (T ⊔ M) := by
    refine { toIsLattice := isLattice_sup hc.symm hT hM, span_eq_top := ?_ }
    rw [eq_top_iff, ← hc.symm.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))
  obtain ⟨r, hr⟩ := LIOrb.exists_pow_smul_le hN₀ hTM h𝔭
  have hsurj := toDisc_surj h hc.symm T (locF 𝔭 N₀) 𝔭 hiW hpr
  have hker : ((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)) ≤
      LinearMap.ker (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) := by
    rw [Submodule.smul_le]
    intro a ha y _
    rw [mem_ker_toDisc]
    have h1 : a • (y : V) ∈ locF 𝔭 (T ⊔ M) := hr (Submodule.smul_mem_smul ha y.2)
    exact prO_locF hc.symm hp (mem_of_isLatIn hT) (mem_of_isLatIn hM) h1
  haveI := LIOrb.finite_quot hN₀ h𝔭 r
  refine Finite.of_surjective (((extP K 𝔭) ^ r • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 N₀)).liftQ
    (toDisc h hc.symm T (locF 𝔭 N₀) 𝔭 hiW) hker) ?_
  intro d
  obtain ⟨y, rfl⟩ := hsurj d
  exact ⟨Submodule.Quotient.mk y, Submodule.liftQ_apply _ _ _⟩

theorem exists_lattice_locF {Λ L₁ L₂ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hL₁ : Submodule.IsFullLattice K L₁) (hL₂ : L₂.FG) (hΛ : locF 𝔭 Λ = Λ) (h1 : L₁ ≤ Λ)
    (h2 : Λ ≤ locF 𝔭 L₂) : ∃ Λ', Submodule.IsLattice K Λ' ∧ locF 𝔭 Λ' = Λ := by
  refine ⟨(L₁ ⊔ L₂) ⊓ Λ, ⟨(hL₁.fg.sup hL₂).of_le inf_le_left, ?_⟩, ?_⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · have e := LIOrb.IA.locF_inf 𝔭 h𝔭.isPrime (L₁ ⊔ L₂) Λ
    rw [hΛ] at e
    rw [e]
    exact le_antisymm inf_le_right (le_inf (h2.trans (LocF.locF_mono 𝔭 le_sup_right)) le_rfl)

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLocFEq
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def fibS (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    Set (Submodule (𝓞 K) V) :=
  {Λ | (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T}

theorem fibP_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T : Submodule (𝓞 K) V) :
    fibP h U 𝔭 M T = Nat.card (fibS h U 𝔭 M T) := rfl

theorem isLattice_sup {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : IsLatIn X A) (hB : IsLatIn Y B) : Submodule.IsLattice K (A ⊔ B) := by
  refine ⟨hA.1.sup hB.1, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem exists_locF_eq {A B : Submodule (𝓞 K) V} (hA : Submodule.IsFullLattice K A)
    (hB : Submodule.IsFullLattice K B) :
    ∃ s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, ∀ 𝔭 ∉ s, locF 𝔭.1 A = locF 𝔭.1 B := by
  obtain ⟨n, hn, hnA⟩ := LocF.exists_zsmul_le hA.toIsLattice hB
  obtain ⟨m, hm, hmB⟩ := LocF.exists_zsmul_le hB.toIsLattice hA
  have hc : ((n * m : ℤ) : 𝓞 F) ≠ 0 := by
    exact_mod_cast mul_ne_zero hn hm
  obtain ⟨s, hs⟩ := (LocalFactorEquality.finite_vF_ne_zero hc).exists_finset
  refine ⟨s, fun 𝔭 h𝔭 => ?_⟩
  have hv : vF 𝔭.1 ((n * m : ℤ) : 𝓞 F) = 0 := by
    by_contra hne
    exact h𝔭 ((hs 𝔭).2 hne)
  have hnm := LocalizedFibreSets.notMem_of_vF_zero 𝔭.2 hc hv
  have hp := 𝔭.2.isPrime
  have hn' : ((n : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_right _ h1)
  have hm' : ((m : ℤ) : 𝓞 F) ∉ 𝔭.1 := fun h1 => hnm (by rw [Int.cast_mul]; exact 𝔭.1.mul_mem_left _ h1)
  have key : ∀ {A B : Submodule (𝓞 K) V} (k : ℤ), ((k : ℤ) : 𝓞 F) ∉ 𝔭.1 → (∀ x ∈ A, k • x ∈ B) →
      locF 𝔭.1 A ≤ locF 𝔭.1 B := by
    intro A B k hk hkA x hx
    obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
    refine (LocF.mem_locF_iff hp B x).2 ⟨(k : 𝓞 F) * t, fun h1 => (hp.mem_or_mem h1).elim hk ht, ?_⟩
    rw [map_mul, mul_smul, LocF.algebraMap_intCast_smul]
    exact hkA _ htx
  exact le_antisymm (key n hn' hnA) (key m hm' hmB)

private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma algebraMap_ne_zero_of_mem_closure_prime_compl {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy

theorem locF_sup_inf {X Y : Submodule K V} (hc : IsCompl X Y) {A B : Submodule (𝓞 K) V}
    (hA : ∀ x ∈ A, x ∈ X) (hB : ∀ x ∈ B, x ∈ Y) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (A ⊔ B) ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 A := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
    have hxX : x ∈ X := hx2
    have hsX : s • x ∈ X := by
      rw [← algebraMap_smul K s x]; exact X.smul_mem _ hxX
    have hbX : b ∈ X := by
      have : b = s • x - a := by rw [← hab]; abel
      rw [this]; exact X.sub_mem hsX (hA a ha)
    have hb0 : b = 0 := by
      have := hc.inf_eq_bot
      have hmem : b ∈ X ⊓ Y := ⟨hbX, hB b hb⟩
      rw [this] at hmem
      exact (Submodule.mem_bot K).mp hmem
    refine (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, ?_⟩
    rw [← hab, hb0, add_zero]; exact ha
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, Submodule.mem_sup_left hsx⟩, ?_⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := algebraMap_ne_zero_of_mem_closure_prime_compl hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    show x ∈ X
    rw [e]
    exact X.smul_mem _ (hA _ hsx)

theorem dualF_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔭 : Ideal (𝓞 F)) {A B : Submodule (𝓞 K) V} (hAB : A ≤ B) :
    dualF h 𝔭 B ≤ dualF h 𝔭 A := by
  intro x hx
  have hx' : ∀ y ∈ B, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  change ∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  exact fun y hy => hx' y (hAB hy)

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfOf
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def GlueLocal : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U) →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

end Formalism.L2.SG.Pf.G7
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExp
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def IsomFixOfExp : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ T T' : Submodule (𝓞 K) V, IsLatIn (orthK h U) T → IsLatIn (orthK h U) T' →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h (orthK h U) T 𝔭 b a → IsJordanIn h (orthK h U) T' 𝔭 b' a' →
      (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T'

end Formalism.L2.SG.Pf.G8
end
end

