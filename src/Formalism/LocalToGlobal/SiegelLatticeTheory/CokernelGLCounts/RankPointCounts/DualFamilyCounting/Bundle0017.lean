module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDet
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittOEv
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Matrix Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

section OEvRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_inclR (o : 𝓞 E) : inclR (F := F) (Fv F v) (o : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨o, trivial, rfl⟩

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have h := oev_inclR (F := F) (E := E) v 1
  simpa using h

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at hx hy ⊢
  rw [SetLike.mem_coe] at hx hy ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      exact Submodule.subset_span ⟨a * b, trivial, by simp [map_mul]⟩
    | zero => simp
    | add y z _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      show _ * ((c : Fv F v) • y) ∈ _
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c h
  | zero => simp
  | add x z _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show ((c : Fv F v) • x) * y ∈ _
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c h

theorem sigR_smul' (σ : E →ₐ[F] E) (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add (f := _), h1, h2, map_add (f := _), smul_add]

theorem oev_sigR (σ : E →ₐ[F] E) {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    sigR (Fv F v) σ x ∈ OEv (E := E) v := by
  unfold OEv at hx ⊢
  rw [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    refine Submodule.subset_span
      ⟨⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)⟩, trivial, ?_⟩
    simp [sigR, inclR]
    rfl
  | zero => simp
  | add x y _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    show sigR (Fv F v) σ ((c : Fv F v) • x) ∈ _
    rw [sigR_smul']
    exact Submodule.smul_mem _ c h

def oevRing : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oev_mul v
  one_mem' := oev_one v
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  neg_mem' := fun hx => Submodule.neg_mem _ hx

theorem mem_std_of_oev {n : ℕ} (y : Fin n → Fv F v ⊗[F] E) (hy : ∀ i, y i ∈ OEv (E := E) v) :
    y ∈ latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  have hsingle : ∀ (i : Fin n) (z : Fv F v ⊗[F] E), z ∈ OEv (E := E) v → Pi.single i z ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
    intro i z hz
    change z ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨o, -, rfl⟩ := hw
      refine Submodule.subset_span ⟨Pi.single i (o : E), ?_, ?_⟩
      · rw [SetLike.mem_coe, MassDataMassesW.KCptW.stdSub, Submodule.mem_pi]
        intro k _
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · funext k
        by_cases hk : k = i
        · subst hk; simp [ratV]
        · simp [ratV, hk]
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add w w' _ _ h1 h2 => rw [Pi.single_add]; exact Submodule.add_mem _ h1 h2
    | smul c w _ h =>
      have : (Pi.single i (c • w) : Fin n → Fv F v ⊗[F] E) = c • (Pi.single i w : Fin n → Fv F v ⊗[F] E) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      rw [this]
      exact Submodule.smul_mem _ c h
  rw [← Finset.univ_sum_single y]
  exact Submodule.sum_mem _ fun i _ => hsingle i (y i) (hy i)

theorem ev_oev (x : E) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, inclR (F := F) (Fv F v) x ∈ OEv (E := E) v := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsIntegral.isIntegral x).isAlgebraic
  obtain ⟨N, hN0, hNx⟩ := halg.exists_integral_multiple
  let o : 𝓞 E := ⟨N • x, hNx⟩
  filter_upwards [ev_int (F := F) ((N : F)⁻¹)] with v hv
  have e : inclR (F := F) (Fv F v) x =
      (⟨algebraMap F (Fv F v) ((N : F)⁻¹), hv⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (o : E) := by
    show _ = algebraMap F (Fv F v) ((N : F)⁻¹) • inclR (F := F) (Fv F v) (N • x)
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, map_zsmul, zsmul_eq_mul, ← mul_assoc, ← map_intCast (algebraMap F (Fv F v ⊗[F] E)), ← map_mul,
      inv_mul_cancel₀ (Int.cast_ne_zero.2 hN0), map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ (oev_inclR v o)

theorem oev_smul' {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {z : Fv F v ⊗[F] E}
    (hz : z ∈ OEv (E := E) v) : r • z ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨r, hr⟩ : v.adicCompletionIntegers F) hz

end OEvRing

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegOnOfCompl
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans

def IsGlueData {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) {n m : ℕ} (a : Fin n → 𝓞 F)
    (π : 𝓞 F) (w : Fin m → V) (c : Fin m → F) (τ : Fin n → Fin m) : Prop :=
  (∀ j, w j ∈ orthK h U) ∧ (∀ j k, j ≠ k → h (w j) (w k) = 0) ∧
  (∀ j, h (w j) (w j) = algebraMap F K (c j) ∧ c j ≠ 0) ∧
  (∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) ∧
  (∃ s₀ : 𝓞 F, IsUnif0 𝔭 π s₀) ∧
  (∀ i, vF 𝔭 (a i) ≠ 0 →
    InP 𝔭 (2 * vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i)))) ∧
  (∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) →
    InP 𝔭 0 (algebraMap F K (c j)) ∧ InP 𝔭 0 (algebraMap F K (c j)⁻¹))

def GlueVecs : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
      ∃ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
        (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ

def GlueAssemble : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueData h U 𝔭 a π w c τ →
      ∃ T : Submodule (𝓞 K) V, (∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧ locF 𝔭 A = T) ∧
        dualF h 𝔭 T = T ∧ T ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem nondegOn_of_compl {h : V →ₗ⋆[K] V →ₗ[K] K} (hnd : Nondeg h) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) : NondegOn h U := by
  intro x hx hxU
  apply hnd
  intro y
  have hy : y ∈ U ⊔ orthK h U := by rw [hUc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
  have hz' : h x z = 0 := by
    have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hz x) hx
    exact LinearMap.mem_ker.1 this
  rw [map_add (f := _), hxU u hu, hz', add_zero]

theorem glueLocal_of_of (hJ : JordanExists) (hV : GlueVecs) (hA : GlueAssemble) :
    Formalism.L2.SG.Pf.G7.GlueLocal := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 hc
  have hne : {c | ∃ b a, IsJordanIn h U M 𝔭 b a ∧ c = cJof 𝔭 a}.Nonempty := by
    obtain ⟨b, a, hba⟩ := (hJ K F V hK hF h hs).1 U M (nondegOn_of_compl hnd hUc) hM hMi 𝔭 h𝔭
    exact ⟨_, b, a, hba, rfl⟩
  obtain ⟨b, a, hba, hca⟩ := Nat.sInf_mem hne
  have hc' : cJof 𝔭 a < finrank K (orthK h U) := by
    rw [← hca]; exact hc
  obtain ⟨π, w, c, τ, hg⟩ := hV K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc'
  exact hA K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PairSpanDimension

variable {D : Formalism.BasicNotions.D7}

theorem totPos_ne_zero {x : D.host.E} (hx : TotPos x) : x ≠ 0 := by
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; have := D.R.two_le_m; have := D.R.m_le_f
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; omega)
  obtain ⟨τ⟩ := this
  intro h
  have := hx τ
  rw [h, map_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

def fam {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V :=
  Sum.elim F0.fvec F'.fl.fvec

variable {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

theorem upair_eq : UPair D F0 F' = Submodule.span D.host.E (Set.range (fam F0 F')) := by
  unfold UPair fam
  rw [Set.Sum.elim_range]

theorem hT_fam (a b : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) :
    (VS D).hT (fam F0 F' a) (fam F0 F' b) = Ga T T' (ZhatL (lf D F0) F') a b := by
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := by
    intro x y
    rw [← starRingEnd_apply]
    first
      | exact (VS D).herm.eq x y
      | exact (VS D).herm x y
  have hze : ∀ j, (VS D).hT F0.z (F0.e j) = 0 := fun j => by rw [← hs, F0.z_orth, star_zero]
  have hze' : ∀ j, (VS D).hT F'.fl.z (F'.fl.e j) = 0 := fun j => by rw [← hs, F'.fl.z_orth, star_zero]
  rcases a with a | a <;> rcases b with b | b
  · simp only [fam, Sum.elim_inl, Ga, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F0.e_iso, F0.z_orth, F0.z_norm, hze]
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [fam, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply]
    show _ = star ((VS D).hT (F0.fvec b) (F'.fl.fvec a))
    rw [hs]
  · simp only [fam, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [FlagG.fvec, F'.fl.e_iso, F'.fl.z_orth, F'.fl.z_norm, hze']

theorem eq_zero_of_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0)
    (c : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → D.host.E)
    (h : ∀ a, (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i) = 0) : c = 0 := by
  have hdet : (Ga T T' (ZhatL (lf D F0) F')).det ≠ 0 := by
    rw [PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_Ga]
    refine mul_ne_zero ?_ hG
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h1 | h1 <;>
      rw [h1] <;> simp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext a
  have ha := h a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul, hT_fam] at ha
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← ha]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem fam_li (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) : LinearIndependent D.host.E (fam F0 F') := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 := eq_zero_of_orth F0 F' hG c (fun a => by rw [hc, map_zero])
  intro i
  exact congrFun h0 i

theorem mem_orthK {U : Submodule D.host.E (VS D).V} {x : (VS D).V} :
    x ∈ orthK (VS D).hT U ↔ ∀ u ∈ U, (VS D).hT u x = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem inf_orth (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxU, hxO⟩ := hx
  rw [upair_eq, Submodule.mem_span_range_iff_exists_fun] at hxU
  obtain ⟨c, rfl⟩ := hxU
  have hc := eq_zero_of_orth F0 F' hG c (fun a => (mem_orthK.mp hxO) _
    (by rw [upair_eq]; exact Submodule.subset_span ⟨a, rfl⟩))
  rw [Submodule.mem_bot, hc]
  simp

theorem isCompl (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    IsCompl (UPair D F0 F') (orthK (VS D).hT (UPair D F0 F')) := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    exact inf_orth F0 F' hG
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let Φ : ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) →ₗ[D.host.E]
        ((Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) → D.host.E) :=
      { toFun := fun c a => (VS D).hT (fam F0 F' a) (∑ i, c i • fam F0 F' i)
        map_add' := by
          intro c d
          ext a
          simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro s c
          ext a
          simp [mul_smul, ← Finset.smul_sum, mul_add] }
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      exact eq_zero_of_orth F0 F' hG c (fun a => congrFun hc a)
    obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) (fun a => (VS D).hT (fam F0 F' a) v)
    have hu : ∑ i, c i • fam F0 F' i ∈ UPair D F0 F' := by
      rw [upair_eq]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hw : v - ∑ i, c i • fam F0 F' i ∈ orthK (VS D).hT (UPair D F0 F') := by
      rw [mem_orthK]
      intro u hu'
      rw [upair_eq] at hu'
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        have h1 := congrFun hc a
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at h1
        rw [map_sub, h1, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | smul s x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
    have hv : v = ∑ i, c i • fam F0 F' i + (v - ∑ i, c i • fam F0 F' i) := by abel
    rw [hv]
    exact Submodule.add_mem_sup hu hw

theorem finrank_upair (hG : GZ T T' (ZhatL (lf D F0) F') ≠ 0) :
    finrank D.host.E (UPair D F0 F') = D.R.m := by
  rw [upair_eq, finrank_span_eq_card (fam_li F0 F' hG)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  have := D.R.rS_two
  omega

theorem finrank_V : finrank D.host.E (VS D).V = D.R.r := by
  rw [(VS D).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Formalism.BasicNotions.Ranks.rankY]

theorem X_le_upair : F0.X ≤ UPair D F0 F' := by
  unfold FlagG.X UPair
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  left
  exact ⟨i.castSucc, by simp [FlagG.fvec]⟩

theorem z_mem_upair : F0.z ∈ UPair D F0 F' := by
  unfold UPair
  exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)

theorem Xplus_le_upair : F0.Xplus ≤ UPair D F0 F' := by
  unfold FlagG.Xplus
  exact sup_le (X_le_upair F0 F') ((Submodule.span_singleton_le_iff_mem _ _).mpr (z_mem_upair F0 F'))

end PairSpanDimension


open PairSpanDimension in
theorem perpendicular_definition_holds : PerpDef := by
  intro D u u' _ F0 what₂ _ Z F' _ hZ hP
  have hG : GZ (Tn u) (Tn u') (ZhatL (lf D F0) F') ≠ 0 := by rw [hZ]; exact totPos_ne_zero hP
  have hC := PairSpanDimension.isCompl F0 F' hG
  have hU := PairSpanDimension.finrank_upair F0 F' hG
  have hW : finrank D.host.E (orthK (VS D).hT (UPair D F0 F')) = D.R.k - 1 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    have h2 := D.R.r_eq
    rw [PairSpanDimension.finrank_V, hU] at h1
    omega
  refine ⟨hC, ?_, hU, hW⟩
  intro x hx hx0 φ
  have hpos := Formalism.MainNotions.LatticeGluingRadicals.p_posX D (D.mem u).A.T (D.mem u).A.T_prime.pos (lf D F0)
  have hxO : x ∈ orth (VS D) (Xplus (lf D F0)) := by
    rw [Formalism.MainNotions.LatticeGluingRadicals.p_mem_orth]
    intro w hw
    exact (PairSpanDimension.mem_orthK.1 hx) w (PairSpanDimension.Xplus_le_upair F0 F' hw)
  have hxX : x ∉ Xsp (lf D F0) := by
    intro hxX
    have : x ∈ UPair D F0 F' ⊓ orthK (VS D).hT (UPair D F0 F') := ⟨PairSpanDimension.X_le_upair F0 F' hxX, hx⟩
    rw [PairSpanDimension.inf_orth F0 F' hG] at this
    exact hx0 ((Submodule.mem_bot _).1 this)
  exact hpos φ x hxO hxX

end Formalism.L2.SG.Pf.Cnt
end
end

