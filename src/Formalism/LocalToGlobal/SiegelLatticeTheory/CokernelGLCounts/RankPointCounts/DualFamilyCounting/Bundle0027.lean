module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CoeffOfSpan
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsAdmissibleIntegralBasisChangeOne
section
noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem frameAct_one (f : Fin (r + 1) → S.V) (b : Fin (r + 1)) : frameAct f 1 b = f b := by
  unfold frameAct
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Matrix.one_apply_ne hab]
  · simp

end General

variable {D : Formalism.BasicNotions.D7} {T T' : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'}
  {Λ : Submodule (𝓞 D.host.E) (VS D).V}

theorem f_mem_UUS (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F0.fvec (Fin.last _) = F0.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · have e : F0.fvec (Fin.castSucc a) = F0.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem f'_mem_UUS (i : Fin (D.R.rS + 1)) : F'.fl.fvec i ∈ UUS D F0 F' := by
  unfold UUS
  refine Fin.lastCases ?_ (fun a => ?_) i
  · have e : F'.fl.fvec (Fin.last _) = F'.fl.z := by simp [FlagG.fvec]
    rw [e]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · have e : F'.fl.fvec (Fin.castSucc a) = F'.fl.e a := by simp [FlagG.fvec]
    rw [e]
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact Submodule.subset_span ⟨a, 1, one_mem_ddS D a, (one_smul _ _).symm⟩

theorem spanE_UUS : spanE (VS D) (UUS D F0 F') = UPair D F0 F' := by
  apply le_antisymm
  · unfold spanE
    rw [Submodule.span_le]
    intro y hy
    have hle : UUS D F0 F' ≤ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
      unfold UUS
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inl ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inl ⟨Fin.last _, by simp [FlagG.fvec]⟩)
      · unfold XS
        rw [Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        exact (UPair D F0 F').smul_mem x (Submodule.subset_span (Or.inr ⟨Fin.castSucc a, by simp [FlagG.fvec]⟩))
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span (Or.inr ⟨Fin.last _, by simp [FlagG.fvec]⟩)
    exact hle hy
  · unfold UPair
    rw [Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Submodule.subset_span (f_mem_UUS i)
    · exact Submodule.subset_span (f'_mem_UUS i)

theorem UU_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    UU Λ (lf D F0) F' = UUS D F0 F' := by
  unfold UU
  rw [hX0, hX1, hz]
  rfl

theorem blat_eq (hX0 : XLam Λ (lf D F0) = XS D F0) (hX1 : XLam Λ F' = XS D F'.fl) (hz : F'.zt = F'.fl.z) :
    BLat Λ (lf D F0) F' = Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
  unfold BLat UUE
  rw [UU_eq hX0 hX1 hz, spanE_UUS]

theorem mplus1_loc (hX0 : XLam Λ (lf D F0) = XS D F0) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (Mplus Λ (gS D) (lf D F0) F' 1) = Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') := by
  rw [loc_BB_g D F0 F' P hg]
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (Submodule.span_le.2 ?_))
    (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
  · rintro v ((hv | hv) | ⟨b, rfl⟩)
    · have hv' : v ∈ XS D F0 := by rw [← hX0]; exact hv
      refine ((XS_le_locP_e D F0 P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))) hv'
      rintro _ ⟨a, rfl⟩; exact e_mem_MMg D F0 F' a
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Formalism.L2.SG.Pf.le_locP' _ _ (z_mem_MMg D F0 F')
    · refine Formalism.L2.SG.Pf.le_locP' _ _ ?_
      simp only [frame, frameAct_one]
      exact m_mem_MMg D F0 F' b
  · rintro v (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · induction i using Fin.lastCases with
      | last => rw [fvec_last]; exact Submodule.subset_span (Or.inl (Or.inr rfl))
      | cast a =>
        rw [fvec_cast]
        refine Submodule.subset_span (Or.inl (Or.inl ?_))
        rw [hX0]; exact e_mem_XS D F0 a
    · refine Submodule.subset_span (Or.inr ⟨b, ?_⟩)
      simp only [frame, frameAct_one]

theorem isAdmissibleIntegralBasisChange_one (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    AdmWit Λ (gS D) (lf D F0) F' 1 := by
  refine ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a, fun b P _ => ?_⟩
  have := P.isPrime
  have hm : (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b) ∈ Λ := by
    have := MMg_le_BB D F0 F' (m_mem_MMg D F0 F' b)
    rw [← hB] at this
    exact this.1
  refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
  rw [one_smul]
  have e : frame F' b - frameAct (frame (lf D F0)) 1 b =
      ((gS D : ℕ) : 𝓞 D.host.E) • ((((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
    rw [frameAct_one, smulO, map_natCast, smul_smul, mul_inv_cancel₀ (g_ne D), one_smul]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm

theorem forward {Z : MatZ D} (hz : F'.zt = F'.fl.z) (hR : IsRowLat D F0 Λ) (hE : F' ∈ EZ T' F0 Λ Z) :
    Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F' := by
  obtain ⟨-, ⟨-, -, hL, hF⟩, hX0⟩ := hR
  obtain ⟨⟨hL', -, -⟩, h1, ⟨ξ, hξ, hgen⟩, ⟨hF', hX1⟩, -⟩ := hE
  rw [← blat_eq hX0 hX1 hz]
  apply Formalism.L2.SG.Pf.eq_of_locP
  intro P
  have := P.isPrime
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · rw [(hgen P).1 hg, Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg ξ hξ,
      ← Formalism.L2.SG.Pf.Mplus_eq_MplusInt hL hF hL' hF' P hg 1 h1, mplus1_loc hX0 P.asIdeal hg]
  · rw [(hgen P).2 hg, UU_eq hX0 hX1 hz, ← loc_BB_ng D F0 F' P.asIdeal hg]

theorem backward (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) {Z : MatZ D} (hz : F'.zt = F'.fl.z)
    (hZ : ZhatL (lf D F0) F' = Z) (hG : GZ T T' (Zhat F0 F'.fl) ≠ 0)
    (hlat : Submodule.IsLattice D.host.E Λ) (huni : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (hB : Λ ⊓ (UPair D F0 F').restrictScalars (𝓞 D.host.E) = BB D F0 F') :
    IsRowLat D F0 Λ ∧ F' ∈ EZ T' F0 Λ Z := by
  have hw := indep D F0 F'.fl hG
  have hX0 := xlam0 hw hB
  have hX1 := xlam1 hw hB
  have hzΛ : F0.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z_mem_MMg D F0 F'))
  have hz'Λ : F'.fl.z ∈ Λ := BB_le_Lam hw hB (MMg_le_BB D F0 F' (z'_mem_MMg D F0 F'))
  have hFC0 : IsFixedConv Λ (gS D) (lf D F0) := by
    refine ⟨fun P => ?_, prim0 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F0 P
    exact ⟨c, hc0, hc1, by rw [hX0]; exact hc2⟩
  have hFC1 : IsFixedConv Λ (gS D) F' := by
    refine ⟨fun P => ?_, prim1 hw hB⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := xs_locGen D F'.fl P
    exact ⟨c, hc0, hc1, by rw [hX1]; exact hc2⟩
  have h1 := isAdmissibleIntegralBasisChange_one hB
  refine ⟨⟨Formalism.MainNotions.BridgeRowsGenus.unimodular_mem_genus hU D.sp.cm (VS D) Λ hlat huni,
    ⟨hlat, huni, ⟨hzΛ, rfl⟩, hFC0⟩, hX0⟩, ⟨⟨hz'Λ, hz⟩, ⟨1, h1⟩, hG⟩, h1, ⟨1, h1, fun P => ?_⟩,
    ⟨hFC1, hX1⟩, hZ⟩
  have := P.isPrime
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [blat_eq hX0 hX1 hz, hB, mplus1_loc hX0 P.asIdeal hg]
  · rw [blat_eq hX0 hX1 hz, hB, UU_eq hX0 hX1 hz, loc_BB_ng D F0 F' P.asIdeal hg]

end Formalism.L2.SG.Pf.Cnt.R3

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mmChar_of (hU : Formalism.MainNotions.BridgeRowsGenus.LocUnimod) : MMChar := by
  intro D u u' _ F0 what₂ _ Z F' hz hZ hP
  have hG : GZ (Tn u) (Tn u') (Zhat F0 F'.fl) ≠ 0 := by
    subst hZ
    exact totPos_ne D hP
  rw [MMof_eq]
  refine ⟨BB_latIn D F0 F', fun Λ => ⟨fun ⟨hR, hE⟩ => ?_, fun ⟨hlat, huni, hB⟩ => ?_⟩⟩
  · exact ⟨hR.2.1.1, hR.2.1.2.1, forward hz hR hE⟩
  · exact backward hU hz hZ hG hlat huni hB

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LamAE
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Formalism.L2.SG.Pf.NcS.KfOrbPf
open scoped TensorProduct

theorem lamAE : LamAE := by
  intro F E _ _ _ _ _ σ hCM δ hδ hδ0
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabS.sigma_invol σ hCM.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra H
    push Not at H
    let w : InfinitePlace E := Classical.arbitrary _
    have hreal : ComplexEmbedding.IsReal w.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext z
      rw [ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)
  set θ : E := x - σ x with hθdef
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσ]; ring
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' := congrArg σ h
    rw [map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h'
    have hq : (2 : E) * (algebraMap F E q * θ) = 0 := by linear_combination h - h'
    have hq0 : q = 0 := by
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1
      · exact (algebraMap F E).injective (by rw [h1, map_zero])
      · exact absurd h1 hθ0
    subst hq0
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩
  let v2 : Fin 2 → E := ![1, θ]
  have hli : LinearIndependent F v2 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0 := by
      rw [← hg]; simp [v2, Algebra.smul_def]
    obtain ⟨h0, h1⟩ := hind _ _ e
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let b2 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])
  have hb2 : ∀ i, b2 i = v2 i := fun i => by
    simp only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ := by
    intro e
    conv_lhs => rw [← b2.sum_repr e]
    rw [Fin.sum_univ_two, hb2, hb2]
    simp [v2, Algebra.smul_def]

  have hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0) := by
    intro e he
    have h1 := hdec e
    have h2 := congrArg σ h1
    rw [he, map_add (f := _), map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
    have h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0 := by
      rw [map_zero, map_mul, map_ofNat]; linear_combination h2 - h1
    have hq := (hind _ _ h3).2
    have hq' : b2.repr e 1 = 0 := (mul_eq_zero.1 hq).resolve_left two_ne_zero
    rw [hq', map_zero (algebraMap F E), zero_mul, add_zero] at h1
    exact h1
  have hθ2σ : σ (θ ^ 2) = θ ^ 2 := by rw [map_pow, hσθ, neg_sq]
  set d := b2.repr (θ ^ 2) 0 with hd_def
  have hd : θ ^ 2 = algebraMap F E d := hfixF _ hθ2σ
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    have h1 : (θ - 1) * (θ + 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.1 h1 with h | h
    · have e : θ = 1 := sub_eq_zero.1 h
      rw [e, map_one] at hσθ
      exact two_ne_zero (by linear_combination hσθ : (2 : E) = 0)
    · have e : θ = -1 := eq_neg_of_add_eq_zero_left h
      rw [e, map_neg, map_one] at hσθ
      exact two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)
  set β0 := b2.repr δ 0 with hβ0_def
  have hδF : δ = algebraMap F E β0 := hfixF δ hδ
  have hβ0 : β0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hδF
    exact hδ0 hδF
  have h1d : (1 - d) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
  set Pc : F := (1 + d) / (1 - d) with hPc
  set Qc : F := 2 / (1 - d) with hQc_def
  have hQc : Qc ≠ 0 := div_ne_zero two_ne_zero h1d
  have hpq : Pc ^ 2 - d * Qc ^ 2 = 1 := by
    rw [hPc, hQc_def]
    field_simp
    ring
  filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc,
    ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2]
    with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd
  intro t ht
  let ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
    (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
  have hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F),
      ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y := by
    intro y hy
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hιO : ∀ r, ι r ∈ oevRing (E := E) v := by
    intro r
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v
    rw [Algebra.algebraMap_eq_smul_one]
    exact oev_smul' v r.2 (oev_one v)
  have hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r := by
    intro r
    show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hincl : ∀ y : F, inclR (F := F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y :=
    fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y
  have hΘ : (inclR (F := F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by
    rw [hιF, ← map_pow, hd, hincl]
  have hsΘ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by
    simp [sigR, inclR, hσθ, TensorProduct.tmul_neg]
  have hcrd' := hcrd t ht
  have htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F := F) (Fv F v) θ := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]
    rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]
    show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 0) +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabS.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ
    simp only [PI.VolStabS.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [inclR]
  have hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1 := by
    apply Subtype.ext
    show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]
  have hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hβ0, map_one]
  have hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]
  have h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1 := by
    apply Subtype.ext
    show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1
    have e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4 := by
      rw [map_ofNat]; rfl
    rw [e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO
    (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩
    hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4
  refine ⟨lam, hlamO, hlam, c', hc'O, ?_⟩
  have hδι : inclR (F := F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]
  rw [hδι]
  conv_lhs => rw [htd]
  exact hc'

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthProjectionOfMemCompl
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

structure Good {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} (hc : IsCompl U (orthK h U))
    (M T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) : Prop where
  iU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M)
  iW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T)
  oU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v
  oW : ∀ v ∈ locF 𝔭 (dualIn h (orthK h U) T), ∃ x ∈ Λ, prO hc.symm x = v
  cU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M
  cW : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem mk_eq_iff {X : Submodule K V} {L : Submodule (𝓞 K) V} (a b : ↥(locF 𝔭 (dualIn h X L))) :
    (Submodule.Quotient.mk a : DiscMod h X L 𝔭) = Submodule.Quotient.mk b ↔
      (a : V) - (b : V) ∈ locF 𝔭 L := by
  rw [Submodule.Quotient.eq]
  simp [Submodule.mem_comap]

private theorem prO_mem' {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) : prO hc x ∈ X := by
  exact (Submodule.projectionOnto X Y hc x).2

private theorem prO_eq_zero_of_mem_compl {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ Y) :
    prO hc x = 0 := by
  have h1 : prO hc x ∈ X := prO_mem' hc x
  have h2 : prO hc x ∈ Y := by
    have e : prO hc x = x - prO hc.symm x := eq_sub_of_add_eq (prO_add hc x)
    rw [e]
    exact Y.sub_mem hx (prO_mem' hc.symm x)
  have h3 : prO hc x ∈ X ⊓ Y := Submodule.mem_inf.2 ⟨h1, h2⟩
  rw [hc.inf_eq_bot] at h3
  exact (Submodule.mem_bot K).1 h3

private theorem prO_eq_self_of_mem {X Y : Submodule K V} (hc : IsCompl X Y) {x : V} (hx : x ∈ X) :
    prO hc x = x := by
  have h0 : prO hc.symm x = 0 := prO_eq_zero_of_mem_compl hc.symm hx
  have e := prO_add hc x
  rw [h0, add_zero] at e
  exact e

theorem prO_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc' x ∈ U := prO_mem' hc' x

theorem prO_symm_mem (hc' : IsCompl U (orthK h U)) (x : V) : prO hc'.symm x ∈ orthK h U := prO_mem' hc'.symm x

theorem orth_projection_of_mem_compl {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) : prO hc' x = 0 := by
  exact prO_eq_zero_of_mem_compl hc' hx

theorem orth_projection_symm_of_mem {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ orthK h U) :
    prO hc'.symm x = x := by
  exact prO_eq_self_of_mem hc'.symm hx

theorem prO_symm_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc'.symm x = 0 := by
  exact prO_eq_zero_of_mem_compl hc'.symm hx

theorem mem_of_proj (hG : Good hc M T 𝔭 Λ) {x x' : V} (hx' : x' ∈ Λ) (hU : prO hc x' = prO hc x)
    (hW : prO hc.symm x - prO hc.symm x' ∈ locF 𝔭 T) : x ∈ Λ := by
  have hle : locF 𝔭 T ≤ Λ := by
    rw [← hG.cW]
    exact inf_le_left
  have ht : prO hc.symm x - prO hc.symm x' ∈ Λ := hle hW
  have e1 := prO_add hc x
  have e2 := prO_add hc x'
  rw [hU] at e2
  have hx : x = x' + (prO hc.symm x - prO hc.symm x') := by
    calc x = prO hc x + prO hc.symm x := e1.symm
      _ = (prO hc x + prO hc.symm x') + (prO hc.symm x - prO hc.symm x') := by abel
      _ = x' + (prO hc.symm x - prO hc.symm x') := by rw [e2]
  rw [hx]
  exact Λ.add_mem hx' ht

def gam (hG : Good hc M T 𝔭 Λ) : DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭 :=
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hG.iU) =
      LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hG.iW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hG.cU, prO_mem_iff hc.symm hG.cW]
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
  ((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hG.iU hG.oU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hG.iW hG.oW))

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

