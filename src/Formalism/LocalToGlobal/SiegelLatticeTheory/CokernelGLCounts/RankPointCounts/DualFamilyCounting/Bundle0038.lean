module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0022
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0008
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldMore
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0037
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBRa
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def aaLbS (b : Fin D.R.rS) : Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}

def TrDetUnimod : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {N : ℕ}
    (m : Module.Basis (Fin N) ℤ ((aaLbS X b).restrictScalars ℤ)),
    N = Module.finrank ℚ D.host.E * (D.R.k + 1) →
    |(Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))).det| =
      |(discr D.host.E : ℚ)| ^ (D.R.k + 1) * (FractionalIdeal.absNorm (aaD D b) : ℚ) ^ (2 * (D.R.k + 1))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensJordanL
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section JL

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M) (p : PlF D)

theorem jl_bc_smulO (o : 𝓞 D.host.E) (x : (VS D).V) :
    L.bc p (o • x) = (D.s.atP p).ιE (o : D.host.E) • L.bc p x := by
  rw [← L.bc_smul p]
  congr 1
  first
    | rfl
    | exact (algebraMap_smul D.host.E o x).symm

theorem jl_iE_mem (hA : Agree δ M p) (o : 𝓞 D.host.E) : (D.s.atP p).ιE (o : D.host.E) ∈ (M p).L.O := by
  rw [hA.2.2.2.1]
  exact PI.CntNotIntW.iE_mem_O D p o

theorem jl_latP_span (hA : Agree δ M p) (S : Set (VS D).V) :
    lattice₂ L p (Submodule.span (𝓞 D.host.E) S) = Submodule.span (M p).L.O (L.bc p '' S) := by
  unfold lattice₂
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.span_induction
      (p := fun x _ => L.bc p x ∈ Submodule.span (M p).L.O (L.bc p '' S)) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Submodule.subset_span ⟨y, hy, rfl⟩
    · rw [map_zero]
      exact zero_mem _
    · intro y z _ _ hy hz
      rw [map_add (f := _)]
      exact add_mem hy hz
    · intro o y _ hy
      rw [jl_bc_smulO L p o y]
      exact Submodule.smul_mem _ (⟨_, jl_iE_mem p hA o⟩ : (M p).L.O) hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem jl_closure {s : 𝓞 D.host.E}
    (hs : s ∈ Submonoid.closure {s : 𝓞 D.host.E | ∃ t : 𝓞 D.host.F, t ∉ p.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = s}) :
    ∃ t : 𝓞 D.host.F, t ∉ p.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', rfl⟩ := hy
    exact ⟨t * t', fun h => (p.isPrime.mem_or_mem h).elim ht ht', map_mul _ _ _⟩

theorem jl_latP_le (hA : Agree δ M p) {A B : Submodule (𝓞 D.host.E) (VS D).V}
    (h : locF (F := D.host.F) (K := D.host.E) p.asIdeal A ≤ locF (F := D.host.F) (K := D.host.E) p.asIdeal B) :
    lattice₂ L p A ≤ lattice₂ L p B := by
  unfold lattice₂
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  have haA : a ∈ locF (F := D.host.F) (K := D.host.E) p.asIdeal A :=
    ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
  obtain ⟨s, hs, hsb⟩ := h haA
  obtain ⟨t, ht, rfl⟩ := jl_closure p hs
  have hne := Formalism.L2.SG.Pf.LocUnramP.iotaF_ne p t ht
  have hcc : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  have hE : (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E)) =
      ((t : D.host.F) : D.host.E) := rfl
  have hbc : L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) • L.bc p a := by
    rw [jl_bc_smulO, hE, Formalism.L2.SG.Pf.LocUnramP.iotaE_alg]
  have hmem : L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) ∈
      Submodule.span (M p).L.O (L.bc p '' (B : Set (VS D).V)) :=
    Submodule.subset_span ⟨_, hsb, rfl⟩
  have hy : ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] :=
    Formalism.L2.SG.Pf.LocUnramP.iotaF_inv_mem p t ht
  have hc'O : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ (M p).L.O := by
    rw [hA.2.2.2.1, (D.s.atP p).O_def]
    have hI : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF (t : D.host.F))⁻¹ :=
      isIntegral_algebraMap (x := (⟨_, hy⟩ : 𝒪[(D.s.atP p).Fp]))
    exact hI.algebraMap
  have e : L.bc p a = (⟨_, hc'O⟩ : (M p).L.O) • L.bc p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • a) := by
    rw [hbc, Subring.smul_def, smul_smul]
    simp only [hcc, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end JL

section BaseDensityIntegrable

variable {D : Formalism.BasicNotions.D7} (p : PlF D)

theorem jl_not_inv_mem (t : 𝓞 D.host.F) (ht : t ∈ p.asIdeal) (ht0 : (D.s.atP p).ιF (t : D.host.F) ≠ 0) :
    ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∉ 𝒪[(D.s.atP p).Fp] := by
  intro hmem
  have hc := (D.s.atP p).val 1 (t : D.host.F)
  rw [map_one, map_one] at hc
  have h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (D.s.atP p).ιF (t : D.host.F) := by
    rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (D.s.atP p).Fp)]
    rw [Valuation.mem_integer_iff] at hmem
    calc ValuativeRel.valuation _ 1 = ValuativeRel.valuation _
          ((D.s.atP p).ιF (t : D.host.F) * ((D.s.atP p).ιF (t : D.host.F))⁻¹) := by
          rw [mul_inv_cancel₀ ht0]
      _ = ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) *
          ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F))⁻¹ := map_mul _ _ _
      _ ≤ ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) * 1 := mul_le_mul' le_rfl hmem
      _ = ValuativeRel.valuation _ ((D.s.atP p).ιF (t : D.host.F)) := mul_one _
  have h2 := hc.mp h1
  have h3 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.F) p t).mpr ht
  exact absurd h2 (not_le.mpr h3)

theorem jl_unit_iff (t : 𝓞 D.host.F) :
    IsUnit (⟨(D.s.atP p).ιF (t : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p t⟩ : 𝒪[(D.s.atP p).Fp]) ↔
      t ∉ p.asIdeal := by
  constructor
  · intro hu ht
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    have hy' : (D.s.atP p).ιF (t : D.host.F) * (y : (D.s.atP p).Fp) = 1 := by
      have h := congrArg Subtype.val hy
      simpa using h
    have hne : (D.s.atP p).ιF (t : D.host.F) ≠ 0 := left_ne_zero_of_mul_eq_one hy'
    apply jl_not_inv_mem p t ht hne
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  · intro ht
    have hne := Formalism.L2.SG.Pf.LocUnramP.iotaF_ne p t ht
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, Formalism.L2.SG.Pf.LocUnramP.iotaF_inv_mem p t ht⟩, ?_⟩
    apply Subtype.ext
    simp [mul_inv_cancel₀ hne]

theorem jl_dvd_iff (ϖ : 𝒪[(D.s.atP p).Fp]) (hϖ : Irreducible ϖ) (t : 𝓞 D.host.F) :
    ϖ ∣ (⟨(D.s.atP p).ιF (t : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p t⟩ : 𝒪[(D.s.atP p).Fp]) ↔
      t ∈ p.asIdeal := by
  haveI := (D.s.atP p).lf
  rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    jl_unit_iff, not_not]

end BaseDensityIntegrable

theorem jordan_decomposition_holds : DualityBasisChange.JordanL := by
  intro D δ M hA L u u' hT F0 what₂ hR F' hz hP hI p ϖ hϖ
  obtain ⟨hKc, hFc, -⟩ := field_dictionary_holds D
  obtain ⟨hC, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ F' hz rfl hP
  obtain ⟨hLat, -⟩ := (mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR _ F' hz rfl hP
  have hNd : NondegOn (VS D).hT (UPair D F0 F') := by
    intro x hx hxy
    have hxo : x ∈ orthK (VS D).hT (UPair D F0 F') := by
      simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]
      intro y hy
      rw [← (VS D).herm.eq x y, hxy y hy, map_zero]
    exact (Submodule.disjoint_def.1 hC.disjoint) x hx hxo
  obtain ⟨hJ1, -⟩ := jordan_splitting_exists D.host.E D.host.F (VS D).V hKc hFc (VS D).hT (VS D).herm
  have hne : {c | ∃ b a, IsJordanIn (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal b a ∧
      c = cJof p.asIdeal a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := hJ1 _ _ hNd hLat hI p.asIdeal p.isMaximal
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hc⟩ := Nat.sInf_mem hne
  have hcJ : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal = cJof p.asIdeal a := hc
  obtain ⟨hbU, hloc, horth, hdiag, ha0⟩ := hba
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hcard : D.R.rS + 1 + (D.R.rS + 1) = finrank D.host.E (UPair D F0 F') := by rw [hUr, hm]; ring
  let e : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) ≃ Fin (finrank D.host.E (UPair D F0 F')) :=
    finSumFinEquiv.trans (finCongr hcard)
  refine ⟨fun i => L.bc p (b (e i)),
    fun i => ⟨(D.s.atP p).ιF ((a (e i) : 𝓞 D.host.F) : D.host.F), Formalism.L2.SG.Pf.LocUnramP.iotaF_mem p (a (e i))⟩,
    ?_, ?_, ?_, ?_⟩
  ·
    have h1 : Submodule.span (M p).L.O (Set.range fun i => L.bc p (b (e i))) =
        lattice₂ L p (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
      rw [jl_latP_span L p (hA p), ← Set.range_comp]
      congr 1
      ext y
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨e.symm j, by simp⟩
    rw [h1]
    exact le_antisymm (jl_latP_le L p (hA p) hloc.le) (jl_latP_le L p (hA p) hloc.ge)
  ·
    intro i j hij
    rw [L.bc_form p]
    show (D.s.atP p).ιE ((VS D).hT (b (e i)) (b (e j))) = 0
    rw [horth _ _ (fun h => hij (e.injective h)), map_zero]
  ·
    intro i
    rw [L.bc_form p]
    show (D.s.atP p).ιE ((VS D).hT (b (e i)) (b (e i))) = _
    rw [hdiag, ← Formalism.L2.SG.Pf.LocUnramP.iotaE_alg p]
    rfl
  ·
    rw [hcJ]
    unfold cJof
    refine Finset.card_equiv e (fun i => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [jl_dvd_iff p ϖ hϖ (a (e i))]
    have h0 := ha0 (e i)
    have hm1 := unitaryAbsoluteValueBounds.mem_pow_iff_le_vF (F := D.host.F) p.isMaximal h0 1
    rw [pow_one] at hm1
    rw [hm1]
    constructor <;> intro h <;> omega

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLastDual
section
namespace Formalism.L2.SG.Pf.GluingBases

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueVecs_of_last (hL : LastUnit) : GlueVecs :=
  glueVecs_of gluing_vectors_exist (lastRescale_of hL)

end Formalism.L2.SG.Pf.GluingBases

namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_of_last_dual (hL : Formalism.L2.SG.Pf.GluingBases.LastUnit) (hD : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of_fam jordan_splitting_exists (Formalism.L2.SG.Pf.GluingBases.glueVecs_of_last hL)
    Formalism.L2.SG.Pf.GluingBases.family_top_holds Formalism.L2.SG.Pf.GluingBases.family_gram_holds hD

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ImportsBis
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem card_eq [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hc M T 𝔭 Λ)
    (h0 : InFib h U 𝔭 M T Λ₀) :
    Nat.card {Λ // InFib h U 𝔭 M T Λ} =
      Nat.card {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) // FP P} := by
  classical
  have G0 : Good hc M T 𝔭 Λ₀ := hgood Λ₀ h0
  have hd₀ : dualF h 𝔭 Λ₀ = Λ₀ := h0.2.1

  have hTW : ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ orthK h U := by
    intro d hd
    have : d ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [G0.cW]; exact hd
    exact this.2
  have hTL : ∀ {Λ : Submodule (𝓞 K) V}, Good hc M T 𝔭 Λ → ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ Λ := by
    intro Λ hG d hd
    have : d ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [hG.cW]; exact hd
    exact this.1
  have hsW : ∀ {d : V}, d ∈ orthK h U → prO hc.symm d = d := fun hd =>
    (mem_W_of_prO_zero (hc := hc) (orth_projection_of_mem_compl hd)).2

  have hFP : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), FP (isoOf G0 (hgood Λ hΛ)) := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    refine fp_of (hc := hc) hs hd₀ hΛ.2.1 _ ?_
    intro b x' hx'
    obtain ⟨z, hz, hzb⟩ := G0.oW b b.2
    obtain ⟨w, hw, hwz⟩ := hG.oU (prO hc z) (G0.iU z hz)
    have hb : b = ⟨prO hc.symm z, G0.iW z hz⟩ := Subtype.ext hzb.symm
    rw [hb, isoOf_mk G0 hG hz hw hwz, Submodule.Quotient.eq, Submodule.mem_comap] at hx'
    have hd : (x' : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hx'
    have hdW := hTW hd
    refine ⟨z, hz, w + ((x' : V) - prO hc.symm w), Λ.add_mem hw (hTL hG hd), hzb, ?_, ?_⟩
    · rw [map_add (f := _), hsW hdW]; abel
    · rw [map_add (f := _), orth_projection_of_mem_compl hdW, add_zero, hwz]
  have hglue : ∀ P, FP P → InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
    intro P hP
    obtain ⟨N₀, hN₀, hloc⟩ := h0.1
    haveI : Finite (DiscMod h (orthK h U) T 𝔭) :=
      Formalism.L2.SG.Pf.ProjectionDiscriminantModule.discMod_finite hc h𝔭 hM hT hN₀ hloc G0.cW G0.iW G0.oW
    exact glue_mem hs h𝔭 hM hT G0 h0 hP (Finite.surjective_of_injective (FP.injective G0 hd₀ hP))
  have hleft : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), glue hc T 𝔭 Λ₀ (isoOf G0 (hgood Λ hΛ)) = Λ := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    ext x
    constructor
    · rintro ⟨b, hb, y, hy, c, hcy, hU, hP⟩
      obtain ⟨w, hw, hwy⟩ := hG.oU (prO hc y) (G0.iU y hy)
      have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hcy
      rw [hc', isoOf_mk G0 hG hy hw hwy, Submodule.Quotient.eq, Submodule.mem_comap] at hP
      have hd : (b : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hP
      rw [hb] at hd
      exact mem_of_proj hG hw (hwy.trans hU) hd
    · intro hx
      obtain ⟨y, hy, hyx⟩ := G0.oU (prO hc x) (hG.iU x hx)
      exact ⟨⟨prO hc.symm x, hG.iW x hx⟩, rfl, y, hy, ⟨prO hc.symm y, G0.iW y hy⟩, rfl, hyx,
        (isoOf_mk G0 hG hy hx hyx.symm).symm⟩
  have hright : ∀ P (hP : FP P), isoOf G0 (hgood _ (hglue P hP)) = P := by
    intro P hP
    have hG := hgood _ (hglue P hP)
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
    obtain ⟨y, hy, hyc⟩ := G0.oW c c.2
    have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hyc.symm
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk c))
    rw [hc'] at hx' ⊢
    have hmem := mem_glue_of (P := P) G0 hy x' hx'
    have hx'W : (x' : V) ∈ orthK h U := memW G0 x'.2
    have hUeq : prO hc (prO hc y + x') = prO hc y := by
      rw [map_add (f := _), prO_of_mem_U (prO_mem hc y), orth_projection_of_mem_compl hx'W, add_zero]
    rw [isoOf_mk G0 hG hy hmem hUeq, ← hx']
    congr 1
    apply Subtype.ext
    have e := prO_add hc (prO hc y)
    rw [prO_of_mem_U (prO_mem hc y)] at e
    have e0 : prO hc.symm (prO hc y) = 0 := by
      have := congrArg (fun v => v - prO hc y) e
      simpa using this
    simp only [map_add (f := _), e0, zero_add, hsW hx'W]
  exact Nat.card_congr
    { toFun := fun Λ => ⟨isoOf G0 (hgood Λ.1 Λ.2), hFP Λ.1 Λ.2⟩
      invFun := fun P => ⟨glue hc T 𝔭 Λ₀ P.1, hglue P.1 P.2⟩
      left_inv := fun Λ => Subtype.ext (hleft Λ.1 Λ.2)
      right_inv := fun P => Subtype.ext (hright P.1 P.2) }

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_integer_iff_vle {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (v := valuation K)).symm

theorem mem_OF_of_loc (D : Formalism.BasicNotions.D7) (s : D.host.F)
    (hs : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E s) ∈ (D.s.atP p).O) :
    s ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F s fun p => ?_
  have h1 := hs p
  rw [(D.s.atP p).compat] at h1
  have hint := ((D.s.atP p).O_def _).1 h1
  have hnt : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hinj : Function.Injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) := by
    haveI := hnt; exact (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
  have h2 : (D.s.atP p).ιF s ∈ 𝒪[(D.s.atP p).Fp] :=
    PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral ((isIntegral_algebraMap_iff ).1 hint)
  rw [mem_integer_iff_vle, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one] at h2
  exact h2

theorem locGlobIntE : LocGlobIntE := by
  intro D x hx
  have hstar : star x = D.conjF x := by
    rw [D.conjF_eq]
    have := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    change D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  have hcjO : ∀ p : PlF D, (D.s.atP p).ιE (star x) ∈ (D.s.atP p).O := fun p => by
    rw [hstar, ← (D.s.atP p).cj_ιE, (D.s.atP p).O_def]
    exact ((D.s.atP p).O_def _).1 (hx p) |>.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  obtain ⟨t, ht⟩ := (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := (D.sp.cm.fixed (x * star x)).1 (by rw [star_mul, star_star, mul_comm])
  obtain ⟨t', ht'⟩ := mem_OF_of_loc D t fun p => by
    rw [ht, map_add (f := _)]; exact (D.s.atP p).O.add_mem (hx p) (hcjO p)
  obtain ⟨n', hn'⟩ := mem_OF_of_loc D n fun p => by
    rw [hn, map_mul]; exact (D.s.atP p).O.mul_mem (hx p) (hcjO p)

  have hT : IsIntegral ℤ (x + star x) := by
    rw [← ht, ← ht']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral t'))
  have hN : IsIntegral ℤ (x * star x) := by
    rw [← hn, ← hn']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral n'))
  set a : 𝓞 D.host.E := ⟨x + star x, hT⟩
  set b : 𝓞 D.host.E := ⟨x * star x, hN⟩
  have hx' : IsIntegral (𝓞 D.host.E) x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    show x ^ 2 - (x + star x) * x + x * star x = 0
    ring
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  exact Submodule.mem_one.2 ⟨y, hy⟩

theorem not_integral_density_of_self_dual (h1 : LocSelfDual) (hF : FrameBasisL) : NotIntDens :=
  notIntDens_of_steps h1 hF locGlobIntE

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
end
end

