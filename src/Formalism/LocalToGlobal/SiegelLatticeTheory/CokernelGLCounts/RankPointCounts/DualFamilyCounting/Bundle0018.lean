module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0035
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def VolOrdV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ¬ TypAt X v →
    localVolumeUnit X ψ v / ZZX X u u' ψ v =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))

def VolTypV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → ∀ v : PlX X, TypAt X v → localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))

def OmV : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    (omAt X.B.I.cm.sig X.B.I.J ψ v ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
      {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
        Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal =
      absV v (dV v) ^ ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) *
        aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')

def CondAll : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

def DiffProd : Prop :=
  HasProd (fun v : PlX X => absV v (dV v)) (|(NumberField.discr X.B.I.F : ℝ)|⁻¹)

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualEquivSymmApply
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual {Y : Type} [AddCommGroup Y] [Module K Y] [Module (𝓞 K) Y] [IsScalarTower (𝓞 K) K Y]
    {B : Y →ₗ⋆[K] Y →ₗ[K] K} {L : Submodule (𝓞 K) Y} {x : Y} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}

theorem push_dualIn (L : Submodule (𝓞 K) ↥X) :
    push X (dualIn (formOn h X) ⊤ L) = dualIn h X (push X L) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_dual.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact mem_dual.mp hx.2 y hy
  · rintro ⟨hvX, hv⟩
    refine ⟨⟨v, hvX⟩, ⟨by simp, mem_dual.mpr fun y hy => ?_⟩, rfl⟩
    exact mem_dual.mp hv _ (coe_mem_push.mpr hy)

variable {𝔭 : Ideal (𝓞 F)}

theorem map_incl_dual (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    (locF 𝔭 (dualIn (formOn h X) ⊤ L)).map (incl X) = locF 𝔭 (dualIn h X (push X L)) := by
  change push X _ = _
  rw [push_locF X hp, push_dualIn]

def dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L)) ≃ₗ[𝓞 K] ↥(locF 𝔭 (dualIn h X (push X L))) :=
  (Submodule.equivMapOfInjective (incl X) (incl_injective X) _).trans
    (LinearEquiv.ofEq _ _ (map_incl_dual hp L))

theorem dualEquiv_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    ((dualEquiv (h := h) hp L x : ↥(locF 𝔭 (dualIn h X (push X L)))) : V) = ((x : ↥X) : V) := rfl

theorem dualEquiv_symm_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    ((((dualEquiv (h := h) hp L).symm y : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) : ↥X) : V) = (y : V) := by
  have := dualEquiv_apply hp L ((dualEquiv (h := h) hp L).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem map_dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ((locF 𝔭 L).comap (locF 𝔭 (dualIn (formOn h X) ⊤ L)).subtype).map
        (dualEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) =
      (locF 𝔭 (push X L)).comap (locF 𝔭 (dualIn h X (push X L))).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← coe_mem_push (X := X), push_locF X hp]
  exact Iff.of_eq (congrArg (fun v => v ∈ locF 𝔭 (push X L)) (dualEquiv_symm_apply (h := h) hp L y))

def discEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    DiscMod (formOn h X) ⊤ L 𝔭 ≃ₗ[𝓞 K] DiscMod h X (push X L) 𝔭 :=
  Submodule.Quotient.equiv _ _ (dualEquiv (h := h) hp L) (map_dualEquiv (h := h) hp L)

theorem discEquiv_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    discEquiv (h := h) hp L (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dualEquiv (h := h) hp L x) := rfl

theorem discEquiv_symm_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    (discEquiv (h := h) hp L).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y) := rfl

def endEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    Module.End (𝓞 K) (DiscMod (formOn h X) ⊤ L 𝔭) ≃ Module.End (𝓞 K) (DiscMod h X (push X L) 𝔭) where
  toFun P := (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _)
  invFun P := ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _)
  left_inv P := by
    apply LinearMap.ext
    intro z
    simp
  right_inv P := by
    apply LinearMap.ext
    intro z
    simp

theorem discAut_push (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    discAut h X (push X L) 𝔭 = discAut (formOn h X) ⊤ L 𝔭 := by
  unfold discAut
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (endEquiv (h := h) hp L) ?_)
  intro P
  constructor
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x)) := by
      rw [← discEquiv_symm_mk, hx, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have hy' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y)) := by
      rw [← discEquiv_symm_mk, hy, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_symm_apply] using this
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk (dualEquiv (h := h) hp L x') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L x)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hx, discEquiv_mk]
    have hy' : Submodule.Quotient.mk (dualEquiv (h := h) hp L y') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L y)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hy, discEquiv_mk]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_apply] using this

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibPNeZeroOfGenus
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isLatIn_cut {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) (X : Submodule K V) :
    IsLatIn X (Λ ⊓ X.restrictScalars (𝓞 K)) := by
  refine ⟨?_, le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    exact Submodule.FG.of_le_of_isNoetherian (inf_le_left : Λ ⊓ X.restrictScalars (𝓞 K) ≤ Λ)
  · obtain ⟨r, hr, hrx⟩ := StabilizerLattices.exists_smul_mem hΛ x
    have h1 : r • x ∈ Λ ⊓ X.restrictScalars (𝓞 K) := ⟨hrx, (X.restrictScalars (𝓞 K)).smul_mem r hx⟩
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    have e : x = (algebraMap (𝓞 K) K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem nondegenerate_of {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) :
    h.Nondegenerate := by
  constructor
  · exact hnd
  · intro y hy
    refine hnd y fun x => ?_
    rw [← hs.eq x y, hy x, map_zero]

theorem finite_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    (fibS h U 𝔭 M T).Finite := by
  have hp := h𝔭.isPrime
  have hN := isLattice_sup hUc hM hT
  have hNfull : Submodule.IsFullLattice K (M ⊔ T) := by
    refine { toIsLattice := hN, span_eq_top := ?_ }
    apply top_unique
    rw [← hUc.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [← hM.2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)
    · rw [← hT.2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right)
  letI := hNfull
  letI hDfull : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondegenerate_of hs hnd) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hNfull).1
  have hD := hDfull.toIsLattice
  have hND : Submodule.IsFullLattice K ((M ⊔ T) ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) := inferInstance
  have key : ∀ Λ ∈ fibS h U 𝔭 M T, locF 𝔭 (M ⊔ T) ≤ Λ ∧ Λ ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) ∧
      locF 𝔭 Λ = Λ := by
    rintro Λ ⟨⟨Λ', -, rfl⟩, h1, h2, h3⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ' := by
      have hs' : M ⊔ T ≤ locF 𝔭 Λ' := sup_le
        ((LocF.le_locF 𝔭 M).trans (h2 ▸ inf_le_left)) ((LocF.le_locF 𝔭 T).trans (h3 ▸ inf_le_left))
      exact (LocF.locF_mono 𝔭 hs').trans (LocF.locF_idem 𝔭 Λ').le
    refine ⟨hle, ?_, LocF.locF_idem 𝔭 Λ'⟩
    rw [G7.locF_dual hF h hN.fg hp]
    calc locF 𝔭 Λ' = dualF h 𝔭 (locF 𝔭 Λ') := h1.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
  refine Set.Finite.of_finite_image (f := fun Λ => Λ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T))
    ((BrB.finite_between hND hD inf_le_right).subset ?_) ?_
  · rintro _ ⟨Λ, hΛ, rfl⟩
    obtain ⟨k1, -, -⟩ := key Λ hΛ
    exact ⟨inf_le_inf_right _ ((LocF.le_locF 𝔭 _).trans k1), inf_le_right⟩
  · intro Λ₁ h1 Λ₂ h2 he
    obtain ⟨-, a1, b1⟩ := key Λ₁ h1
    obtain ⟨-, a2, b2⟩ := key Λ₂ h2
    have e1 : locF 𝔭 (Λ₁ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₁ := by
      rw [LIOrb.locF_inf_locF h𝔭, b1]; exact inf_eq_left.2 a1
    have e2 : locF 𝔭 (Λ₂ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₂ := by
      rw [LIOrb.locF_inf_locF h𝔭, b2]; exact inf_eq_left.2 a2
    rw [← e1, ← e2]
    exact congrArg (locF 𝔭) he

theorem fibP_ne_zero_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    fibP h U 𝔭 M T ≠ 0 ↔ (fibS h U 𝔭 M T).Nonempty := by
  have hfin := finite_fibS hF hs hnd hUc hM hT h𝔭
  rw [fibP_eq, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨x, hx⟩, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨⟨x, hx⟩⟩, hfin.to_subtype⟩

theorem fibP_congr (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M : Submodule (𝓞 K) V)
    {T T' : Submodule (𝓞 K) V} (e : locF 𝔭 T = locF 𝔭 T') : fibP h U 𝔭 M T = fibP h U 𝔭 M T' := by
  unfold fibP
  rw [e]

theorem fibP_ne_zero_of_genus (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hg : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : fibP h U 𝔭 M T ≠ 0 := by
  obtain ⟨g, hg, he⟩ := hg 𝔭 h𝔭
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1, span_eq_top :=
      GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs (nondegenerate_of hs hnd) hΛ₀.1 hΛ₀.2.1 }
  have hT₀ := isLatIn_cut hΛ₀full (orthK h U)
  rw [← fibP_congr h U 𝔭 M (show locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))) = locF 𝔭 T
      by rw [← LocalizedFibreSets.gmap_locF, he]), G6.fibP_gmap hM 𝔭 _ hg,
    fibP_ne_zero_iff hF hs hnd hUc hM hT₀ h𝔭]
  exact ⟨_, locF_mem_fibS hF hΛ₀.1 hΛ₀.2.1 hΛ₀.2.2 rfl h𝔭⟩

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def IsGlueDataPre {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (a : Fin n → 𝓞 F)
    (π : 𝓞 F) (w : Fin m → V) (c : Fin m → F) (τ : Fin n → Fin m) : Prop :=
  (∀ j, w j ∈ orthK h U) ∧ (∀ j k, j ≠ k → h (w j) (w k) = 0) ∧
  (∀ j, h (w j) (w j) = algebraMap F K (c j) ∧ c j ≠ 0) ∧
  (∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) ∧
  (∃ s₀ : 𝓞 F, IsUnif0 𝔭 π s₀) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 →
    InP 𝔭 (2 * vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i)))) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m) ∧
  (∀ j : Fin m, (j : ℕ) + 1 < m → (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) →
    InP 𝔭 0 (algebraMap F K (c j)) ∧ InP 𝔭 0 (algebraMap F K (c j)⁻¹))

def GlueVecsPre : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
      ∃ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
        (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ

def LastRescale : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∃ (w' : Fin (finrank K (orthK h U)) → V) (c' : Fin (finrank K (orthK h U)) → F),
        IsGlueData h U 𝔭 a π w' c' τ

theorem glueVecs_of (h1 : GlueVecsPre) (h2 : LastRescale) : GlueVecs := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  obtain ⟨π, w, c, τ, hg⟩ := h1 K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  obtain ⟨w', c', hg'⟩ := h2 K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  exact ⟨π, w', c', τ, hg'⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsomFixOfExpOf
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  ((Submodule.prodEquivOfIsCompl U W hUc).symm.trans ((LinearEquiv.refl K U).prodCongr g)).trans
    (Submodule.prodEquivOfIsCompl U W hUc)

theorem extU_apply {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (x : U) (y : W) :
    extU hUc g ((x : V) + y) = x + g y := by
  have e : (Submodule.prodEquivOfIsCompl U W hUc).symm ((x : V) + y) = (x, y) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extU, LinearEquiv.trans_apply, e, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl']

theorem extU_mem {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {g : orthK h U ≃ₗ[K] orthK h U} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (resF h (orthK h U))) :
    extU hUc g ∈ isomFix h U := by
  have horth : ∀ u ∈ U, ∀ w ∈ orthK h U, h u w = 0 := by
    intro u hu w hw
    simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hw
    exact hw u hu
  have horth' : ∀ u ∈ U, ∀ w ∈ orthK h U, h w u = 0 := by
    intro u hu w hw
    rw [← hs.eq u w, horth u hu w hw, map_zero]
  have hdec : ∀ x : V, ∃ a : U, ∃ b : orthK h U, (a : V) + b = x := by
    intro x
    have hx : x ∈ U ⊔ orthK h U := by rw [hUc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  have hg' : ∀ x y, resF h (orthK h U) (g x) (g y) = resF h (orthK h U) x y := hg
  change extU hUc g ∈ Formalism.HermitianLatticesTheory.isom h ∧ ∀ u ∈ U, extU hUc g u = u
  refine ⟨?_, ?_⟩
  · change ∀ x y, h (extU hUc g x) (extU hUc g y) = h x y
    intro x y
    obtain ⟨a, b, rfl⟩ := hdec x
    obtain ⟨c, d, rfl⟩ := hdec y
    rw [extU_apply, extU_apply]
    have hgb : h (g b) (g d) = h b d := by
      have := hg' b d
      simpa only [resF_apply] using this
    simp only [map_add (f := _), LinearMap.add_apply, horth _ a.2 _ (g d).2, horth _ a.2 _ d.2,
      horth' _ c.2 _ (g b).2, horth' _ c.2 _ b.2, hgb]
  · intro u hu
    have := extU_apply hUc g ⟨u, hu⟩ 0
    simpa using this

theorem gmap_extU {U W : Submodule K V} (hUc : IsCompl U W) (g : W ≃ₗ[K] W) (X : Submodule (𝓞 K) W) :
    Formalism.HermitianLatticesTheory.gmap (extU hUc g) (X.map (incO W)) = (Formalism.HermitianLatticesTheory.gmap g X).map (incO W) := by
  have key : ∀ w : W, extU hUc g (w : V) = (g w : V) := by
    intro w
    have := extU_apply hUc g 0 w
    simpa using this
  ext v
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, (key x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, ⟨x, hx, rfl⟩, key x⟩

theorem isomFixOfExp_of (hJ : JordanIsom) : IsomFixOfExp := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hN U hUc hpos T T' hT hT' 𝔭 h𝔭 b a b' a' hb hb' hv
  haveI := h𝔭.isPrime
  have hs' : (resF h (orthK h U)).IsSymm := by
    exact ⟨fun x y => by simpa only [resF_apply] using hs.eq (x : V) y⟩
  have hd' : IsTotPosDef (resF h (orthK h U)) := by
    intro x hx φ
    rw [resF_apply]
    exact hpos x x.2 (by simpa using hx) φ
  obtain ⟨g, hg, hgL⟩ := hJ K F (orthK h U) hK hF (resF h (orthK h U)) hs' hd'
    (latW (orthK h U) T) (latW (orthK h U) T') (isLattice_latW hT).toIsLattice
    (isLattice_latW hT').toIsLattice 𝔭 h𝔭 _ _ _ _
    (isJordanIn_res hT hb) (isJordanIn_res hT' hb') (fun i => hv _)
  refine ⟨extU hUc g, extU_mem hs hUc hg, ?_⟩
  rw [← locF_latW hT 𝔭, gmap_extU, hgL, locF_latW hT' 𝔭]

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXHU
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem haarUnique_holds : Formalism.L2.SG.Pf.LsNc5.HaarUnique := by
  intro D X u μ ν hμ hν
  obtain ⟨hσ, h0, hc, hi⟩ := hμ
  obtain ⟨hσ', h0', hc', hi'⟩ := hν
  haveI := hσ
  haveI := hσ'
  have hco : (ProductExactness.NinfG X u : Set X.B.I.Ginf) = X.NinfU u := ProductExactness.NinfG_coe X u
  rw [← hco] at hc hi hc' hi'
  obtain ⟨κ, -, -, hκ⟩ := ProductExactness.PiM.uniq_on_closed (ProductExactness.NinfG X u) (ProductExactness.NinfG_closed X u) μ ν hc hc' hi hi' h0 h0'
  exact ⟨κ, hκ⟩

end Formalism.L2.SG.Pf.NcReal.JX
end
end

