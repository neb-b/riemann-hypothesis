module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0029
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscIsoOfProj
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def prO {X Y : Submodule K V} (hc : IsCompl X Y) : V →ₗ[𝓞 K] V :=
  (X.projection Y hc).restrictScalars (𝓞 K)

theorem prO_apply {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x = X.projection Y hc x := rfl

theorem prO_add {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x + prO hc.symm x = x :=
  Submodule.projection_add_projection_eq_self hc x

def toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y) (L Λ : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L)) :
    ↥Λ →ₗ[𝓞 K] DiscMod h X L 𝔭 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ (prO hc ∘ₗ Λ.subtype) (fun x => hP x x.2)

theorem toDisc_surj (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (hS : ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, prO hc x = v) :
    Function.Surjective (toDisc h hc L Λ 𝔭 hP) := by
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨v, hv⟩
  obtain ⟨x, hx, e⟩ := hS v hv
  exact ⟨⟨x, hx⟩, Subtype.ext e⟩

theorem mem_ker_toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (x : ↥Λ) : x ∈ LinearMap.ker (toDisc h hc L Λ 𝔭 hP) ↔ prO hc (x : V) ∈ locF 𝔭 L := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

theorem prO_mem_iff {X Y : Submodule K V} (hc : IsCompl X Y) {L Λ : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (hX : Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L) (x : V) :
    prO hc x ∈ locF 𝔭 L ↔ prO hc x ∈ Λ := by
  rw [← hX, Submodule.mem_inf]
  constructor
  · exact fun H => H.1
  · intro H
    exact ⟨H, Submodule.projection_apply_mem hc x⟩

theorem discIso_of_proj (h : V →ₗ⋆[K] V →ₗ[K] K) {U W : Submodule K V} (hc : IsCompl U W)
    {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M) (hW : Λ ⊓ W.restrictScalars (𝓞 K) = locF 𝔭 T)
    (hPU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M))
    (hSU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v)
    (hPW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h W T))
    (hSW : ∀ v ∈ locF 𝔭 (dualIn h W T), ∃ x ∈ Λ, prO hc.symm x = v) :
    Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h W T 𝔭) := by
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hPU) = LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hPW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hU, prO_mem_iff hc.symm hW]
    have e := prO_add hc (x : V)
    constructor
    · intro H
      have : prO hc.symm (x : V) = (x : V) - prO hc (x : V) := eq_sub_of_add_eq' e
      rw [this]
      exact Λ.sub_mem x.2 H
    · intro H
      have : prO hc (x : V) = (x : V) - prO hc.symm (x : V) := eq_sub_of_add_eq e
      rw [this]
      exact Λ.sub_mem x.2 H
  exact ⟨((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hPU hSU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hPW hSW))⟩

end Formalism.L2.SG.Pf.G6
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B := by
  constructor
  · intro e
    rw [← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g A, ← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g B, e]
  · rintro rfl
    rfl

theorem gmap_inf (g : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap g A ⊓ Formalism.HermitianLatticesTheory.gmap g B := by
  ext x
  simp only [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]

theorem gmap_eq_self_of_fix (g : V ≃ₗ[K] V) {A : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, g x = x) :
    Formalism.HermitianLatticesTheory.gmap g A = A := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · intro hx
    have e := hA _ hx
    rw [LinearEquiv.apply_symm_apply] at e
    rw [e]
    exact hx
  · intro hx
    have e := hA _ hx
    have : g.symm x = x := by
      conv_lhs => rw [← e]
      simp
    rw [this]
    exact hx

theorem mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {v : V} :
    v ∈ orthK h U ↔ ∀ u ∈ U, h u v = 0 := by
  simp [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem map_mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {v : V} (hv : v ∈ orthK h U) : g v ∈ orthK h U := by
  rw [mem_orthK] at hv ⊢
  intro u hu
  have e1 : h (g u) (g v) = h u v := hg.1 u v
  rw [hg.2 u hu] at e1
  rw [e1, hv u hu]

theorem gmap_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g ((orthK h U).restrictScalars (𝓞 K)) = (orthK h U).restrictScalars (𝓞 K) := by
  have hgi : g⁻¹ ∈ isomFix h U := (isomFix h U).inv_mem hg
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem]
  constructor
  · intro hx
    have := map_mem_orthK hg hx
    simpa using this
  · intro hx
    exact map_mem_orthK hgi hx

theorem gmap_U {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
  gmap_eq_self_of_fix g fun x hx => hg.2 x hx

theorem dualF_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g (dualF h 𝔭 Λ) := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  change (∀ y ∈ Formalism.HermitianLatticesTheory.gmap g Λ, h y x ∈ _) ↔ ∀ y ∈ Λ, h y (g.symm x) ∈ _
  constructor
  · intro H y hy
    have := H (g y) (by rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; simpa using hy)
    have e : h (g y) (g (g.symm x)) = h y (g.symm x) := hg y (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at e
    rwa [e] at this
  · intro H y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := H _ hy
    have e : h (g (g.symm y)) (g (g.symm x)) = h (g.symm y) (g.symm x) := hg _ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    rwa [e]

theorem le_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := by
  intro x hx
  rw [← hL.2]
  exact Submodule.subset_span hx

theorem fibP_gmap [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V) {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T := by
  have hMg : Formalism.HermitianLatticesTheory.gmap g M = M := gmap_eq_self_of_fix g fun x hx => hg.2 x (le_of_isLatIn hM x hx)
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap g
      invFun := Formalism.HermitianLatticesTheory.gmap g.symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => by
        have := Formalism.HermitianLatticesTheory.isomAct_gmap_symm g.symm Λ
        simpa using this }
  unfold fibP
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ ((∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Formalism.HermitianLatticesTheory.gmap g Λ) ∧
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g Λ ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T))
  have e1 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_U hg]
  have e2 : locF 𝔭 M = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) := by rw [LocalizedFibreSets.gmap_locF, hMg]
  have e3 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_orthK hg]
  have e4 : locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) := (LocalizedFibreSets.gmap_locF g 𝔭 T).symm
  rw [dualF_gmap hg.1, gmap_eq_iff, e1, e3, e4, gmap_eq_iff]
  conv_rhs => rw [e2, gmap_eq_iff]
  refine and_congr_left fun _ => ?_
  have lattice_gmap (a : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
      Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap a L) :=
    Submodule.IsLattice.of_fg K (hL.fg.map _)
  constructor
  · rintro ⟨Λ₀, h0, e0⟩
    exact ⟨Formalism.HermitianLatticesTheory.gmap g Λ₀, lattice_gmap g h0, by rw [← LocalizedFibreSets.gmap_locF, e0]⟩
  · rintro ⟨Λ₀, h0, e0⟩
    refine ⟨Formalism.HermitianLatticesTheory.gmap g.symm Λ₀, lattice_gmap g.symm h0, ?_⟩
    rw [← LocalizedFibreSets.gmap_locF, e0, Formalism.HermitianLatticesTheory.isomAct_gmap_symm]

end Formalism.L2.SG.Pf.G6
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

def NondegOn {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : Prop :=
  ∀ x ∈ X, (∀ y ∈ X, h x y = 0) → x = 0

def JordanExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm →
    (∀ (X : Submodule K V) (L : Submodule (𝓞 K) V), NondegOn h X → IsLatIn X L →
      Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X L 𝔭 b a) ∧
    (∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∀ b a, IsJordanIn h ⊤ L 𝔭 b a → vd h L 𝔭 = vJof 𝔭 a)

def JordanInv : Prop :=
  ∀ (K F V V' : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K),
    h.IsSymm → h'.IsSymm → ∀ (X : Submodule K V) (X' : Submodule K V') (L : Submodule (𝓞 K) V)
    (L' : Submodule (𝓞 K) V'), IsLatIn X L → IsLatIn X' L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ b a b' a', IsJordanIn h X L 𝔭 b a → IsJordanIn h' X' L' 𝔭 b' a' →
      Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h' X' L' 𝔭) →
      ∀ j : ℕ, ∑ i, min (vF 𝔭 (a i)) j = ∑ i, min (vF 𝔭 (a' i)) j

def JordanIsom : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L L' : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Submodule.IsLattice K L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h ⊤ L 𝔭 b a → IsJordanIn h ⊤ L' 𝔭 b' a' → (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L'

def AlphaDisc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
      alphaL h L 𝔭 = (discAut h ⊤ L 𝔭 : ℝ) * alphaStd K 𝔭 (finrank K V - cJof 𝔭 a)

def GlueLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      (fibP h U 𝔭 M T ≠ 0 →
        Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭) ∧
        fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭) ∧
      ∀ g ∈ isomFix h U, fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T

def GlueExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U)) →
      (GlueSet h U M).Nonempty

def GlueProd : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → ∀ Λ₀ ∈ GlueSet h U M,
    ∀ T : Submodule (𝓞 K) V, IsLatIn (orthK h U) T →
      ((∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) ↔
        SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T) ∧
      Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T

def GlueMass : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M → (GlueSet h U M).Nonempty →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V), (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
        (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
        (∀ Λ ∈ s, (stabFix h U Λ).Finite) ∧
        ∑ Λ ∈ s, ((Nat.card (stabFix h U Λ) : ℕ) : ℝ)⁻¹ =
          c * nM F h U M ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h U M 𝔭.1)

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.ProjectionDiscriminantModule

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_dualF {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (L : Submodule (𝓞 K) V) : locF 𝔭 (dualF h 𝔭 L) = dualF h 𝔭 L := by
  have hp := h𝔭.isPrime
  refine le_antisymm ?_ (LocF.le_locF 𝔭 _)
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp _ x).1 hx
  show ∀ y ∈ L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  have e : h y (algebraMap (𝓞 F) (𝓞 K) t • x) = algebraMap (𝓞 F) (𝓞 K) t • h y x := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, LinearMap.map_smul, algebraMap_smul]
  have h1 := (show ∀ y ∈ L, h y (algebraMap (𝓞 F) (𝓞 K) t • x) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    from htx) y hy
  rw [e] at h1
  obtain ⟨s, hs, hs_mem⟩ := (LocF.mem_locF_iff hp (1 : Submodule (𝓞 K) K) _).1 h1
  have hst : s * t ∉ 𝔭 := fun hm => (hp.mem_or_mem hm).elim hs ht
  refine (LocF.mem_locF_iff hp _ _).2 ⟨s * t, hst, ?_⟩
  simpa only [map_mul, mul_smul] using hs_mem

end Formalism.L2.SG.Pf.ProjectionDiscriminantModule
end
end

