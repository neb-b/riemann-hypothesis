module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0025

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualLeGlue
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)}

theorem memW (hG : Good hc M T 𝔭 Λ) {b : V} (hb : b ∈ locF 𝔭 (dualIn h (orthK h U) T)) :
    b ∈ orthK h U := by
  obtain ⟨x, -, rfl⟩ := hG.oW b hb
  first
  | exact Submodule.projection_apply_mem _ _ _ _
  | exact Submodule.projection_apply_mem _ _ _
  | exact Submodule.projection_apply_mem _ _
  | exact (orthK h U).projection_apply_mem _ _ _
  | (unfold prO; simp)

theorem mem_glue_of (hG₀ : Good hc M T 𝔭 Λ₀) {y : V} (hy : y ∈ Λ₀)
    (x' : ↥(locF 𝔭 (dualIn h (orthK h U) T)))
    (hx' : Submodule.Quotient.mk x' = P (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩)) :
    prO hc y + x' ∈ glue hc T 𝔭 Λ₀ P := by
  have hx'W : (x' : V) ∈ orthK h U := memW hG₀ x'.2
  have hyU : prO hc y ∈ U := by
    first
    | exact Submodule.projection_apply_mem _ _ _ _
    | exact Submodule.projection_apply_mem _ _ _
    | exact Submodule.projection_apply_mem _ _
    | (unfold prO; simp)
  have h0 : prO hc.symm (prO hc y) = 0 := by
    first
    | exact prO_symm_of_mem_U hyU
    | (rw [prO_apply]; simp [hyU])
    | (unfold prO; simp [hyU])
  refine ⟨x', ?_, y, hy, ⟨prO hc.symm y, hG₀.iW y hy⟩, rfl, ?_, hx'⟩
  · rw [map_add (f := _), orth_projection_symm_of_mem (hc' := hc) hx'W, h0, zero_add]
  · rw [map_add (f := _), prO_of_mem_U (hc' := hc) hyU, orth_projection_of_mem_compl (hc' := hc) hx'W, add_zero]

theorem glue_inf_U (hG₀ : Good hc M T 𝔭 Λ₀) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) :
    glue hc T 𝔭 Λ₀ P ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨b, hb, y, hy, c, hcy, hU, hPb⟩, hxU⟩
    have hb0 : b = 0 :=
      Subtype.ext (hb.trans ((prO_symm_of_mem_U (hc' := hc) hxU).trans Submodule.coe_zero.symm))
    rw [hb0, Submodule.Quotient.mk_zero] at hPb
    have hxy : prO hc y = x := by rw [hU, prO_of_mem_U (hc' := hc) hxU]
    have hcW : (c : V) ∈ orthK h U := by
      rw [hcy]
      first
      | exact Submodule.projection_apply_mem _ _ _ _
      | exact Submodule.projection_apply_mem _ _ _
      | exact Submodule.projection_apply_mem _ _
      | (unfold prO; simp)
    have hcO : ∀ u ∈ U, h u (c : V) = 0 := by
      intro u hu
      simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hcW
      exact hcW u hu
    have hcΛ : (c : V) ∈ Λ₀ := by
      rw [← hd₀]
      intro z hz
      have hzW := hG₀.iW z hz
      obtain ⟨d, hd⟩ := Submodule.Quotient.mk_surjective _
        (P (Submodule.Quotient.mk (⟨prO hc.symm z, hzW⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T)))))
      have h2 := hP ⟨prO hc.symm z, hzW⟩ c d 0 hd (by rw [Submodule.Quotient.mk_zero]; exact hPb)
      have e : h z (c : V) =
          -(h (d : V) (((0 : ↥(locF 𝔭 (dualIn h (orthK h U) T))) : V)) - h (prO hc.symm z) (c : V)) := by
        have e1 : h z (c : V) = h (prO hc z) (c : V) + h (prO hc.symm z) (c : V) := by
          conv_lhs => rw [← prO_add hc z]
          rw [map_add (f := _), LinearMap.add_apply]
        rw [e1, hcO (prO hc z) ?_]
        · simp
        · first
      | exact Submodule.projection_apply_mem _ _ _ _
      | exact Submodule.projection_apply_mem _ _ _
      | exact Submodule.projection_apply_mem _ _
      | (unfold prO; simp)
      rw [e]
      exact Submodule.neg_mem _ h2
    have hxΛ : x ∈ Λ₀ := by
      have e := prO_add hc y
      rw [hxy, ← hcy] at e
      have ex : x = y - (c : V) := eq_sub_of_add_eq e
      rw [ex]
      exact Λ₀.sub_mem hy hcΛ
    rw [← hG₀.cU]
    exact Submodule.mem_inf.2 ⟨hxΛ, hxU⟩
  · intro hx
    have hxΛU : x ∈ Λ₀ ⊓ U.restrictScalars (𝓞 K) := by
      rw [hG₀.cU]
      exact hx
    obtain ⟨hxΛ, hxU⟩ := Submodule.mem_inf.1 hxΛU
    have hxU' : x ∈ U := hxU
    have hps : prO hc.symm x = 0 := prO_symm_of_mem_U (hc' := hc) hxU'
    have hmem : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := hG₀.iW x hxΛ
    refine ⟨⟨0, Submodule.coe_zero.trans hps.symm, x, hxΛ, ⟨prO hc.symm x, hmem⟩, rfl, rfl, ?_⟩, hxU'⟩
    have hz : (⟨prO hc.symm x, hmem⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T))) = 0 := Subtype.ext hps
    rw [hz, Submodule.Quotient.mk_zero, map_zero]

theorem glue_inf_orthK_eq_locF (hG₀ : Good hc M T 𝔭 Λ₀) :
    glue hc T 𝔭 Λ₀ P ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨b, hb, y, hy, c, hcy, hU, hP⟩, hxW⟩
    have hx0 : prO hc x = 0 := orth_projection_of_mem_compl (hc' := hc) hxW
    have hxb : (b : V) = x := by rw [hb, orth_projection_symm_of_mem (hc' := hc) hxW]
    have hyc : (c : V) = y := by
      rw [hcy]
      have e := prO_add hc y
      rw [hU, hx0, zero_add] at e
      exact e
    have hyW : y ∈ orthK h U := by
      rw [← hyc, hcy]
      first
      | exact Submodule.projection_apply_mem _ _ _ _
      | exact Submodule.projection_apply_mem _ _ _
      | exact Submodule.projection_apply_mem _ _
      | (unfold prO; simp)
    have hyT : y ∈ locF 𝔭 T := by
      rw [← hG₀.cW]
      exact Submodule.mem_inf.2 ⟨hy, hyW⟩
    have hc0 : (Submodule.Quotient.mk c : DiscMod h (orthK h U) T 𝔭) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_comap.2 (by rw [Submodule.subtype_apply, hyc]; exact hyT))
    rw [hc0, map_zero] at hP
    have hb' := Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 hP)
    rw [Submodule.subtype_apply, hxb] at hb'
    exact hb'
  · intro hx
    have hxΛW : x ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by
      rw [hG₀.cW]
      exact hx
    obtain ⟨hxΛ, hxW⟩ := Submodule.mem_inf.1 hxΛW
    have hxW' : x ∈ orthK h U := hxW
    have hps : prO hc.symm x = x := orth_projection_symm_of_mem (hc' := hc) hxW'
    have hmem : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := hG₀.iW x hxΛ
    refine ⟨⟨⟨prO hc.symm x, hmem⟩, rfl, x, hxΛ, ⟨prO hc.symm x, hmem⟩, rfl, rfl, ?_⟩, hxW'⟩
    have hc0 : (Submodule.Quotient.mk (⟨prO hc.symm x, hmem⟩ : ↥(locF 𝔭 (dualIn h (orthK h U) T))) :
        DiscMod h (orthK h U) T 𝔭) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.mem_comap.2 (by rw [hps] at hmem ⊢; exact hx : prO hc.symm x ∈ locF 𝔭 T))
    rw [hc0, map_zero]

theorem glue_int (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) {a b : V}
    (ha : a ∈ glue hc T 𝔭 Λ₀ P) (hb : b ∈ glue hc T 𝔭 Λ₀ P) :
    h a b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨ba, hba, ya, hya, ca, hca, hUa, hPa⟩ := ha
  obtain ⟨bb, hbb, yb, hyb, cb, hcb, hUb, hPb⟩ := hb
  rw [split hs hc a b, ← hUa, ← hUb, ← hba, ← hbb]
  have hy : h (prO hc ya) (prO hc yb) = h ya yb - h ca cb := by
    rw [split hs hc ya yb, ← hca, ← hcb]
    ring
  rw [hy]
  have h1 : h ya yb ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    have hmemd : yb ∈ dualF h 𝔭 Λ₀ := by
      rw [hd₀]
      exact hyb
    exact hmemd ya hya
  have h2 := hP ca cb ba bb hPa hPb
  have e : h ya yb - h ca cb + h ba bb = h ya yb + (h ba bb - h ca cb) := by ring
  rw [e]
  exact Submodule.add_mem _ h1 h2

theorem glue_le_dual (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hP : FP P) :
    glue hc T 𝔭 Λ₀ P ≤ dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) := by
  intro x hx y hy
  exact glue_int hs hd₀ hP hy hx

theorem dual_le_glue (hs : h.IsSymm) (hG₀ : Good hc M T 𝔭 Λ₀) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀)
    (hM : IsLatIn U M) (hT : IsLatIn (orthK h U) T) (hP : FP P) (hsurj : Function.Surjective P) :
    dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) ≤ glue hc T 𝔭 Λ₀ P := by
  intro x hx
  have hx' : ∀ z ∈ glue hc T 𝔭 Λ₀ P, h z x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  have hLM : locF 𝔭 M ≤ glue hc T 𝔭 Λ₀ P := by
    intro m hm
    rw [← glue_inf_U hG₀ hd₀ hP] at hm
    exact hm.1
  have hLT : locF 𝔭 T ≤ glue hc T 𝔭 Λ₀ P := by
    intro m hm
    rw [← glue_inf_orthK_eq_locF (P := P) hG₀] at hm
    exact hm.1
  have hxU : prO hc x ∈ locF 𝔭 (dualIn h U M) := by
    apply mem_locF_dualIn hM.1 𝔭 (prO_mem hc x)
    intro m hm
    have hmU := le_of_isLatIn hM m hm
    have e : h m x = h m (prO hc x) + h m (prO hc.symm x) := by rw [← map_add (f := _), prO_add]
    rw [h_UW hmU (prO_symm_mem hc x), add_zero] at e
    rw [← e]
    exact hx' m (hLM (LocF.le_locF 𝔭 M hm))
  have hxW : prO hc.symm x ∈ locF 𝔭 (dualIn h (orthK h U) T) := by
    apply mem_locF_dualIn hT.1 𝔭 (prO_symm_mem hc x)
    intro m hm
    have hmW := le_of_isLatIn hT m hm
    have e : h m x = h m (prO hc x) + h m (prO hc.symm x) := by rw [← map_add (f := _), prO_add]
    rw [h_WU hs hmW (prO_mem hc x), zero_add] at e
    rw [← e]
    exact hx' m (hLT (LocF.le_locF 𝔭 T hm))
  obtain ⟨y, hy, hyU⟩ := hG₀.oU _ hxU
  obtain ⟨x'', hx''⟩ := Submodule.Quotient.mk_surjective _
    (P (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩))
  have hz := mem_glue_of hG₀ hy x'' hx''
  have hx''W := memW hG₀ x''.2
  have hdW : prO hc.symm x - (x'' : V) ∈ orthK h U := (orthK h U).sub_mem (prO_symm_mem hc x) hx''W
  have hdx : prO hc.symm x - (x'' : V) = x - (prO hc y + x'') := by
    calc prO hc.symm x - (x'' : V) = (prO hc x + prO hc.symm x) - (prO hc x + x'') := by abel
      _ = _ := by rw [prO_add, hyU]
  have hdT : prO hc.symm x - (x'' : V) ∈ locF 𝔭 T := by
    apply mem_T_of hG₀ hd₀ hdW
    intro b' hb'
    obtain ⟨e, he⟩ := hsurj (Submodule.Quotient.mk ⟨b', hb'⟩)
    induction e using Submodule.Quotient.induction_on with
    | H e₀ =>
      obtain ⟨y₁, hy₁, he₀⟩ := hG₀.oW e₀ e₀.2
      have hz₁ : prO hc y₁ + b' ∈ glue hc T 𝔭 Λ₀ P := by
        refine mem_glue_of hG₀ hy₁ ⟨b', hb'⟩ ?_
        rw [← he]
        congr 2
        exact Subtype.ext he₀.symm
      have h1 := hx' _ hz₁
      have h2 := glue_int hs hd₀ hP hz₁ hz
      have := sub_mem h1 h2
      rw [← map_sub, ← hdx, map_add (f := _), LinearMap.add_apply, h_UW (prO_mem hc y₁) hdW, zero_add] at this
      exact this
  refine ⟨⟨prO hc.symm x, hxW⟩, rfl, y, hy, ⟨prO hc.symm y, hG₀.iW y hy⟩, rfl, hyU, ?_⟩
  rw [← hx'']
  exact (mk_eq_iff _ _).2 hdT

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyDualHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem form_sum_orth {ι' : Type} [Fintype ι'] [DecidableEq ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι' → V)
    (hvo : ∀ i k, i ≠ k → h (v i) (v k) = 0) (i : ι') (x : ι' → K) :
    h (v i) (∑ k, x k • v k) = x i * h (v i) (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hvo i k (Ne.symm hk), mul_zero]) (by simp)

theorem form_sum_zero {ι' : Type} [Fintype ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (v : ι' → V)
    (h0 : ∀ k, h u (v k) = 0) (x : ι' → K) : h u (∑ k, x k • v k) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul, h0, mul_zero, Finset.sum_const_zero]

theorem family_dual_holds : FamDual := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  have htop := family_top_holds K F V hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j => GluedFormOrthogonality.form_U_orth (hbU i) (hwW j)
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => GluedFormOrthogonality.form_orth_U hs (hbU i) (hwW j)
  have hϖ0 : algebraMap F K (π : F) ≠ 0 := by rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  set L := Submodule.span (𝓞 K) (Set.range (glueFam K 𝔭 b a π w τ)) with hL
  have hGi : ∀ s, glueFam K 𝔭 b a π w τ s ∈ L := fun s => Submodule.subset_span ⟨s, rfl⟩
  have hGw : ∀ j, w j ∈ L := fun j => hGi (Sum.inr j)
  have hg1 : ∀ i, vF 𝔭 (a i) ≠ 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) =
      (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) • (b i + w (τ i)) := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_neg hi]
  have hg0 : ∀ i, vF 𝔭 (a i) = 0 → glueFam K 𝔭 b a π w τ (Sum.inl i) = b i := fun i hi => by
    simp only [glueFam, Sum.elim_inl, if_pos hi]
  have hGb : ∀ i, b i ∈ L := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [← hg0 i hi]; exact hGi _
    · have e : b i = (algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i)) • glueFam K 𝔭 b a π w τ (Sum.inl i)
          - w (τ i) := by
        rw [hg1 i hi, ← algebraMap_smul K, smul_smul, map_pow, jι_eq', ← mul_pow,
          mul_inv_cancel₀ hϖ0, one_pow, one_smul, add_sub_cancel_right]
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hGi _)) (hGw _)
  intro x hx
  have hX : ∀ z ∈ L, h z x ∈ SP K 𝔭 := fun z hz => by
    rw [mem_SP_iff_locF]; exact hx z (LocF.le_locF 𝔭 _ hz)
  have hbw_top : Submodule.span K (Set.range (Sum.elim b w)) = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rcases s with i | j
    · by_cases hi : vF 𝔭 (a i) = 0
      · rw [hg0 i hi]; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · rw [hg1 i hi]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.subset_span ⟨Sum.inr (τ i), rfl⟩))
    · exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hxmem : x ∈ Submodule.span K (Set.range (Sum.elim b w)) := by
    rw [hbw_top]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxmem
  rw [Fintype.sum_sum_type] at hf
  simp only [Sum.elim_inl, Sum.elim_inr] at hf
  have hbx : ∀ i, h (b i) x = f (Sum.inl i) * algebraMap F K (a i : F) := by
    intro i
    rw [← hf, map_add (f := _), form_sum_orth h b hbo i, form_sum_zero h (b i) w (hbw i), hbn, add_zero]
  have hwx : ∀ j, h (w j) x = f (Sum.inr j) * algebraMap F K (c j) := by
    intro j
    rw [← hf, map_add (f := _), form_sum_orth h w hwo j, form_sum_zero h (w j) b (fun i => hwb i j),
      (hwn j).1, zero_add]
  have hα : ∀ i, f (Sum.inl i) * algebraMap F K (a i : F) ∈ SP K 𝔭 := fun i => by
    rw [← hbx]; exact hX _ (hGb i)
  have hγ : ∀ j, f (Sum.inr j) * algebraMap F K (c j) ∈ SP K 𝔭 := fun j => by
    rw [← hwx]; exact hX _ (hGw j)
  have hσ : ∀ i, vF 𝔭 (a i) ≠ 0 → (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
      (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i))) ∈
        SP K 𝔭 := by
    intro i hi
    have h1 := hX _ (hGi (Sum.inl i))
    rwa [hg1 i hi, form_smul_left, star_inv_pow hF, map_add, LinearMap.add_apply, hbx, hwx] at h1
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [← jι_eq']; exact jι_ne_zero (ha0 i)

  have cf0 : ∀ i, vF 𝔭 (a i) = 0 → f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    rw [hi, pow_zero, mul_one] at hu'
    have e : f (Sum.inl i) = (f (Sum.inl i) * algebraMap F K (a i : F)) *
        (algebraMap F K (a i : F))⁻¹ := by field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf1 : ∀ i, vF 𝔭 (a i) ≠ 0 →
      f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) ∈ SP K 𝔭 := by
    intro i hi
    have hu' := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have e : f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i) =
        (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      field_simp [hA0 i]
    rw [e]; exact (SP K 𝔭).mul_mem (hα i) hu'
  have cf2 : ∀ i, vF 𝔭 (a i) ≠ 0 → f (Sum.inr (τ i)) - f (Sum.inl i) ∈ SP K 𝔭 := by
    intro i hi
    obtain ⟨hC0, huc⟩ := UnitPairSolutions.unit_part_c hK hF h𝔭 hu (ha0 i) hi (hcong i hi)
    have hua := UnitPairSolutions.unit_part hK hF h𝔭 hu (ha0 i)
    have hr := mem_SP_of_inP hu (hcong i hi)
    have hq0 : algebraMap F K (π : F) ^ vF 𝔭 (a i) ≠ 0 := pow_ne_zero _ hϖ0
    have e : f (Sum.inr (τ i)) - f (Sum.inl i) =
        ((algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) *
          (f (Sum.inl i) * algebraMap F K (a i : F) + f (Sum.inr (τ i)) * algebraMap F K (c (τ i)))) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) -
        ((algebraMap F K (π : F))⁻¹ ^ (2 * vF 𝔭 (a i)) * algebraMap F K ((a i : F) + c (τ i))) *
          (f (Sum.inl i) * algebraMap F K (a i : F)) *
          ((algebraMap F K (a i : F))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) *
          ((algebraMap F K (c (τ i)))⁻¹ * algebraMap F K (π : F) ^ vF 𝔭 (a i)) := by
      rw [map_add (f := _), inv_pow, inv_pow, pow_mul]
      field_simp [hA0 i, hC0, hϖ0]
      ring
    rw [e]
    exact (SP K 𝔭).sub_mem ((SP K 𝔭).mul_mem (hσ i hi) huc)
      ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem ((SP K 𝔭).mul_mem hr (hα i)) hua) huc)
  classical
  set P := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  let z : Fin (finrank K (orthK h U)) → K := fun j =>
    f (Sum.inr j) - ∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)
  have hz : ∀ j, z j ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      have e : ∑ i' ∈ P.filter (fun i' => τ i' = τ i), f (Sum.inl i') = f (Sum.inl i) := by
        apply Finset.sum_eq_single_of_mem
        · simp [hP, hi]
        · intro i' hi' hne
          simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
          exact absurd (hτ i' i hi'.1 hi hi'.2) hne
      show f (Sum.inr (τ i)) - _ ∈ _
      rw [e]; exact cf2 i hi
    · have e : ∑ i' ∈ P.filter (fun i' => τ i' = j), f (Sum.inl i') = 0 := by
        apply Finset.sum_eq_zero
        intro i' hi'
        simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hi'
        exact absurd ⟨i', hi'.1, hi'.2⟩ hj
      show f (Sum.inr j) - _ ∈ _
      rw [e, sub_zero]
      have h1 := (hunit j (fun i hi e' => hj ⟨i, hi, e'⟩)).2
      rw [map_inv₀] at h1
      have e2 : f (Sum.inr j) = (f (Sum.inr j) * algebraMap F K (c j)) * (algebraMap F K (c j))⁻¹ := by
        field_simp [(map_ne_zero _).2 (hwn j).2]
      rw [e2]; exact (SP K 𝔭).mul_mem (hγ j) h1
  let coef : Fin (finrank K U) → K := fun i => if vF 𝔭 (a i) = 0 then f (Sum.inl i) else
    f (Sum.inl i) * algebraMap F K (π : F) ^ vF 𝔭 (a i)
  have hcoef : ∀ i, coef i ∈ SP K 𝔭 := fun i => by
    simp only [coef]; split_ifs with hi
    · exact cf0 i hi
    · exact cf1 i hi
  have hterm : ∀ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) =
      f (Sum.inl i) • b i + (if vF 𝔭 (a i) ≠ 0 then f (Sum.inl i) • w (τ i) else 0) := by
    intro i
    by_cases hi : vF 𝔭 (a i) = 0
    · simp only [coef, if_pos hi]
      rw [hg0 i hi, if_neg (fun h' => h' hi), add_zero]
    · simp only [coef, if_neg hi]
      rw [hg1 i hi, if_pos hi, smul_smul, mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow,
        mul_one, smul_add]
  have hfib : ∑ j, (∑ i ∈ P.filter (fun i => τ i = j), f (Sum.inl i)) • w j =
      ∑ i ∈ P, f (Sum.inl i) • w (τ i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.univ) (g := τ)
      (fun i _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hdec : x = ∑ i, coef i • glueFam K 𝔭 b a π w τ (Sum.inl i) + ∑ j, z j • w j := by
    simp only [hterm, Finset.sum_add_distrib, z, sub_smul, Finset.sum_sub_distrib, hfib]
    rw [← Finset.sum_filter]
    conv_lhs => rw [← hf]
    abel
  rw [hdec]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => UnitPairSolutions.smul_mem_locF_of_SP (hcoef i) (hGi _))
    (Submodule.sum_mem _ fun j _ => UnitPairSolutions.smul_mem_locF_of_SP (hz j) (hGw j))

end Formalism.L2.SG.Pf.GluingBases
end
end

