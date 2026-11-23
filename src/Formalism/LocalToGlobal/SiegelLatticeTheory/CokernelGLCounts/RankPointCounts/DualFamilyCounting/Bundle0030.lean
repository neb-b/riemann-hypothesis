module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdSd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdTr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniPart

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfBasis
section
namespace Formalism.L2.SG.Pf.Cnt

theorem glueExists_of (hloc : Formalism.L2.SG.Pf.G7.GlueLocal) : GlueExists :=
  Formalism.L2.SG.Pf.G7.glueExists_of_local hloc

theorem glueExists_of_fam (hJ : JordanExists) (hV : Formalism.L2.SG.Pf.GluingBases.GlueVecs)
    (h0 : Formalism.L2.SG.Pf.GluingBases.FamTop) (h1 : Formalism.L2.SG.Pf.GluingBases.FamGram) (h2 : Formalism.L2.SG.Pf.GluingBases.FamDual) :
    GlueExists :=
  glueExists_of (Formalism.L2.SG.Pf.GluingBases.glueLocal_of_fam hJ hV h0 h1 h2 Formalism.L2.SG.Pf.FamilyMeetLattice.family_meet_holds)

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def LastUnit : Prop :=
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
      ∀ j : Fin (finrank K (orthK h U)), (j : ℕ) + 1 = finrank K (orthK h U) →
      ∃ l : K, l ≠ 0 ∧ InP 𝔭 0 (algebraMap F K (c j) * (l * star l)) ∧
        InP 𝔭 0 (algebraMap F K (c j) * (l * star l))⁻¹

theorem lastRescale_of (hL : LastUnit) : LastRescale := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  have hm : 0 < finrank K (orthK h U) := lt_of_le_of_lt (Nat.zero_le _) hc
  set j₀ : Fin (finrank K (orthK h U)) := ⟨finrank K (orthK h U) - 1, by omega⟩ with hj₀
  obtain ⟨l, hl0, hl1, hl2⟩ :=
    hL K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg j₀ (by simp [j₀]; omega)
  obtain ⟨hwW, hwo, hwn, hτ, hu, hcong, hτl, hunit⟩ := hg
  obtain ⟨μ, hμ⟩ := (hF (l * star l)).1 (by rw [star_mul', star_star, mul_comm])
  have hμ0 : μ ≠ 0 := by
    intro e; rw [e, map_zero] at hμ
    exact mul_ne_zero hl0 (star_ne_zero.2 hl0) hμ.symm
  let w' := Function.update w j₀ (l • w j₀)
  let c' := Function.update c j₀ (μ * c j₀)
  have hw'₀ : w' j₀ = l • w j₀ := Function.update_self _ _ _
  have hw'n : ∀ j, j ≠ j₀ → w' j = w j := fun j hj => Function.update_of_ne hj _ _
  have hc'₀ : c' j₀ = μ * c j₀ := Function.update_self _ _ _
  have hc'n : ∀ j, j ≠ j₀ → c' j = c j := fun j hj => Function.update_of_ne hj _ _
  have hτ₀ : ∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j₀ := by
    intro i hi e
    have := hτl i hi
    rw [e] at this
    simp [j₀] at this
    omega
  refine ⟨w', c', ⟨?_, ?_, ?_, hτ, hu, ?_, ?_⟩⟩
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀]; exact Submodule.smul_mem _ _ (hwW j₀)
    · rw [hw'n j hj]; exact hwW j
  · intro j k hjk
    by_cases hj : j = j₀
    · have hk : k ≠ j₀ := fun e => hjk (hj.trans e.symm)
      rw [hj, hw'₀, hw'n k hk, form_smul_left, hwo _ _ (hj ▸ hjk), mul_zero]
    · by_cases hk : k = j₀
      · rw [hk, hw'₀, hw'n j hj, form_smul_right, hwo _ _ (hk ▸ hjk), mul_zero]
      · rw [hw'n j hj, hw'n k hk]; exact hwo j k hjk
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀, hc'₀, form_smul_smul, (hwn j₀).1, map_mul, hμ]
      refine ⟨by ring, mul_ne_zero hμ0 (hwn j₀).2⟩
    · rw [hw'n j hj, hc'n j hj]; exact hwn j
  · intro i hi
    rw [hc'n _ (hτ₀ i hi)]; exact hcong i hi
  · intro j hnp
    by_cases hj : j = j₀
    · rw [hj, hc'₀]
      refine ⟨?_, ?_⟩
      · rw [map_mul, hμ, mul_comm]; exact hl1
      · rw [map_inv₀, map_mul, hμ, mul_comm]; exact hl2
    · rw [hc'n j hj]
      refine hunit j ?_ hnp
      have h1 := j.isLt
      have h2 : (j : ℕ) ≠ finrank K (orthK h U) - 1 := fun e => hj (Fin.ext e)
      omega

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_subset_span {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) V) :
    (locF 𝔭 L : Set V) ⊆ Submodule.span K (L : Set V) := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp L x).1 hx
  have ht0 : algebraMap F K (t : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero (ne_zero_of_notMem ht)
  have h1 : algebraMap F K (t : F) • x ∈ Submodule.span K (L : Set V) := by
    rw [← jι_eq', algebraMap_smul]; exact Submodule.subset_span htx
  exact (Submodule.smul_mem_iff _ ht0).1 h1

theorem le_span_of_locF {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {U : Submodule K V}
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {n : ℕ} {b : Fin n → V}
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 M) :
    U ≤ Submodule.span K (Set.range b) := by
  rw [← hM.2, Submodule.span_le]
  intro x hx
  have h1 : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]; exact LocF.le_locF 𝔭 M hx
  have h2 := locF_subset_span hp _ h1
  rwa [Submodule.span_span_of_tower] at h2

theorem linearIndependent_orth {m : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (w : Fin m → V)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) (hwn : ∀ j, h (w j) (w j) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := congrArg (h (w k)) hg
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hwo k j (Ne.symm hj), mul_zero])
    (by simp)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hwn k)

theorem family_top_holds : FamTop := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hw : ∀ j, w j ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hb : ∀ i, b i ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := by
    intro i
    have hg' : glueFam K 𝔭 b a π w τ (Sum.inl i) ∈
        Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := Submodule.subset_span ⟨Sum.inl i, rfl⟩
    simp only [glueFam, Sum.elim_inl] at hg'
    by_cases hi : vF 𝔭 (a i) = 0
    · rwa [if_pos hi] at hg'
    · rw [if_neg hi] at hg'
      have h0 : (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) ≠ 0 := by
        apply pow_ne_zero; apply inv_ne_zero; rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
      have h1 := (Submodule.smul_mem_iff _ h0).1 hg'
      have h2 := Submodule.sub_mem _ h1 (hw (τ i))
      rwa [add_sub_cancel_right] at h2
  have hU : U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (le_span_of_locF hp hM hbL) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i))
  have hli : LinearIndependent K w := linearIndependent_orth h w hwo fun j => by
    rw [(hwn j).1]; exact (map_ne_zero _).2 (hwn j).2
  have hle : Submodule.span K (Set.range w) ≤ orthK h U :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hwW j)
  have hfr : finrank K (Submodule.span K (Set.range w)) = finrank K (orthK h U) := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hW : orthK h U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (Submodule.eq_of_le_of_finrank_eq hle hfr).ge
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hw j))
  rw [eq_top_iff, ← hUc.sup_eq_top]
  exact sup_le hU hW

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MmIntOfEZ
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmInt_of_EZ {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word}
    (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    {F0 : FlagG (VS D) D.R.rS (Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hR : IsRowReps D F0 what₂)
    {Z : MatZ D} {F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')} (hz : F'.zt = F'.fl.z) (hZ : ZhatL (lf D F0) F' = Z)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z)) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : IsRowLat D F0 Λ) (hE : F' ∈ EZ (Tn u') F0 Λ Z) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') := by
  have hG := (((mmChar_of local_unimodular_holds) D u u' hT F0 what₂ hR Z F' hz hZ hP).2 Λ).mp ⟨hΛ, hE⟩
  by_contra hI
  rw [Formalism.L2.SG.Pf.Asm.glueSet_eq_empty (U := UPair D F0 F') hI] at hG
  exact hG

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWitt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittAlg
open scoped TensorProduct

section Main

theorem sigR_inclR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem hform_inclR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (sigR R σ) (JR R J) (fun i => inclR R (x i)) (fun i => inclR R (y i)) =
      inclR R (Formalism.UG.hform (σ : E →+* E) J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, JR, Matrix.map_apply, sigR_inclR']
  rfl

theorem intWittAE_of (hA : AlgWitt) (hD : HermDiag) (hL : LamAE) : LocSBPf.IntWittAE := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hT hLat d b
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLL, rfl⟩ := hLat
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  have hJh : Formalism.UG.IsHerm (σ : E →+* E) J := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    exact hJ.1 i j
  obtain ⟨P, Q, hQP, hPo, hPd⟩ := hD E (σ : E →+* E) hσ two_ne_zero n J hJh a X0 hT
  set Z0 : Fin a → Fin n → E := fun i => ∑ l, P i l • X0 l with hZ0
  have hZ0e : ∀ i, Z0 i = ∑ l, P i l • X0 l := fun i => rfl
  have hX0e : ∀ c, X0 c = ∑ l, Q c l • Z0 l := fun c => by
    funext k
    simp only [hZ0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, Q c l * (P l m * X0 m k) = (if c = m then 1 else 0) * X0 m k := by
      intro m
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
    simp_rw [hm]
    simp
  let δ : Fin a → E := fun i => Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 i)
  have hδσ : ∀ i, σ (δ i) = δ i := fun i => hform_conj (σ : E →+* E) J hσ hJh _ _
  have hJi : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)
  filter_upwards [ev_latLoc_std L hLL,
    eventually_all.2 fun k => ev_oev (F := F) (b k),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (J⁻¹ i j),
    eventually_all.2 fun i => ev_oev (F := F) (δ i),
    eventually_all.2 fun i => ev_oev (F := F) (δ i)⁻¹,
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (P i j),
    eventually_all.2 fun i => eventually_all.2 fun j => ev_oev (F := F) (Z0 i j),
    eventually_all.2 fun i => hL F E σ hCM (δ i) (hδσ i) (hPd i)]
    with v hstd hbv hJv hJiv hδv hδiv hPv hZv hlam
  intro X hX hgram
  let O := oevRing (E := E) v
  have hXO : ∀ c k, X c k ∈ O := by
    intro c k
    show X c k ∈ OEv (E := E) v
    rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr (X c k)]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact oev_smul' v (hX c k l) (hbv l)
  let s := sigR (Fv F v) σ
  have hs : ∀ z, s (s z) = z := PI.VolStabS.sigR_invol (Fv F v) σ hσ
  have hsO : ∀ z ∈ O, s z ∈ O := by
    intro z hz
    exact oev_sigR v σ hz
  let Jv := JR (F := F) (Fv F v) J
  let Jv' := JR (F := F) (Fv F v) J⁻¹
  have hJJ : Jv' * Jv = 1 := by
    show J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1
    rw [← Matrix.map_mul, hJi, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJvh : Formalism.UG.IsHerm s Jv := by
    unfold Formalism.UG.IsHerm Formalism.UG.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Jv, JR, s, sigR_inclR']
    rw [hJ.1 i j]
  let y : Fin a → Fin n → Fv F v ⊗[F] E := fun i k => inclR (F := F) (Fv F v) (Z0 i k)
  let x : Fin a → Fin n → Fv F v ⊗[F] E := fun i => ∑ l, inclR (F := F) (Fv F v) (P i l) • X l
  have hxO : ∀ i k, x i k ∈ O := by
    intro i k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact O.sum_mem fun l _ => O.mul_mem (hPv i l) (hXO l k)
  have hyy : ∀ i j, Formalism.UG.hform s Jv (y i) (y j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    rw [show Formalism.UG.hform s Jv (y i) (y j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) from
      hform_inclR _ σ J _ _]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  have hXX : ∀ l m, Formalism.UG.hform s Jv (X l) (X m) =
      inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
    intro l m
    exact congrFun (congrFun hgram l) m
  have hxx : ∀ i j, Formalism.UG.hform s Jv (x i) (x j) = if i = j then inclR (F := F) (Fv F v) (δ i) else 0 := by
    intro i j
    have e1 : Formalism.UG.hform s Jv (x i) (x j) = inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (Z0 i) (Z0 j)) := by
      calc Formalism.UG.hform s Jv (x i) (x j)
          = ∑ l, inclR (F := F) (Fv F v) (σ (P i l)) * ∑ m, inclR (F := F) (Fv F v) (P j m) *
              inclR (F := F) (Fv F v) (Formalism.UG.hform (σ : E →+* E) J (X0 l) (X0 m)) := by
            simp only [x]
            rw [hform_sum_left]
            simp_rw [hform_sum_right, hXX, s, sigR_inclR']
        _ = _ := by
            rw [hZ0e i, hZ0e j, hform_sum_left]
            simp_rw [hform_sum_right]
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sum, map_mul]
            rfl
    rw [e1]
    split_ifs with h
    · subst h; rfl
    · rw [hPo i j h, map_zero]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := hA (Fv F v ⊗[F] E) s O hs hsO n Jv Jv' hJvh hJJ hJv hJiv a
    (fun i => inclR (F := F) (Fv F v) (δ i)) (fun i => inclR (F := F) (Fv F v) (δ i)⁻¹) hδv hδiv
    (fun i => by rw [← map_mul, mul_inv_cancel₀ (hPd i), map_one])
    hlam x y hxO hZv hxx hyy
  refine ⟨(⟨g, hg⟩ : HR (Fv F v) σ J), ?_, ?_⟩
  · show ∀ w, w ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
      (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w ∈ latLoc (E := E) v (L : Set (Fin n → E))
    rw [hstd]
    intro w
    constructor
    · intro hw
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgO w (fun k => mem_oev_of_std v w hw k) i
    · intro hw
      have e : w = ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ w) := by
        rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
      rw [e]
      exact mem_std_of_oev v _ fun i => mulVec_mem O _ hgiO _ (fun k => mem_oev_of_std v _ hw k) i
  · funext c
    show (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ ratTup (F := F) (Fv F v) X0 c = X c
    have e1 : ratTup (F := F) (Fv F v) X0 c = ∑ l, inclR (F := F) (Fv F v) (Q c l) • y l := by
      funext k
      simp only [ratTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, y]
      rw [hX0e c]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum, map_mul]
    rw [e1, mulVec_sum]
    simp_rw [mulVec_smul, hgy]
    funext k
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hm : ∀ m, ∑ l, inclR (F := F) (Fv F v) (Q c l) * (inclR (F := F) (Fv F v) (P l m) * X m k) =
        (if c = m then 1 else 0) * X m k := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hQP, Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [hm]
    simp

end Main

theorem integral_witt_almost_everywhere : Formalism.L2.SG.Pf.NcS.LocSBPf.IntWittAE :=
  intWittAE_of IntWittAlg.algWitt IntWittAlg.hermDiag lamAE

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sdNormDV_of {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (hA : AnnX X ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : SdNormDV X ψ := by
  have c1 : SdFromAnn := SdW.sdFromAnn_holds
  intro v hv ι _
  refine c1 ψ v (dV v) hψ ?_ ?_ (hA hψ hs v) ι
  · exact X.B.I.cm.deg2
  · exact VolOrdW.dV_ne_zero (v := v)

theorem volOrdV_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hC : CondAll) : VolOrdV X u u' ψ := by
  intro hψ hs
  exact volOrd_body X u u' ψ (sdNormDV_of X ψ (annX_of X ψ hC) hψ hs) SdW.boxScaleL_holds

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RebasingHolds
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem rebasing_holds : G3.Rebase := by
  intro K V _ _ _ _ _ S π h hS hπ hs hd
  exact rebaseAt_of hS hπ
    (fun J _ _ b e i₀ ho hu x hx hX => G3.uni_part hS hπ hs hd ho hu x hx hX)
    (fun J _ _ e i₀ x hx T hT hlt b ho hu => G3.absorb hS hπ hs x hx T hT hlt b ho hu)

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

