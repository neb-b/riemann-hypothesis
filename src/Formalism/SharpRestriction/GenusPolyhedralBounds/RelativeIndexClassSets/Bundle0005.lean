module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0004
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.BaseDegreeAtLiftIndex

@[expose] public section

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

namespace NetData

variable (Nt : NetData B j ka)

theorem inner_euclideanEmbedding_eq_average (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) =
      (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ y, conj (Nt.ev σ y F) * Nt.ev σ y G := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
  · have hc : (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) = ((Nt.cf σ : ℝ) : ℂ) * ((Nt.cf σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Nt.cf_sq]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Nt.goodRowsProjector_apply_eq_sum, if_true, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring
  · intro τ _ h
    simp [Nt.goodRowsProjector_apply_eq_sum, h]
  · simp

def herm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => Nt.netN σ) (Fintype.card (Σ τ : B.KO →+* ℂ, Nt.NN τ)) where
  e σ := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin (Σ τ : B.KO →+* ℂ, Nt.NN τ))).toLinearEquiv.toLinearMap.comp
    (Nt.e0 σ)
  norm_e σ F := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map, Nt.norm_euclideanEmbedding_eq_netNorm]

theorem herm_inner (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.herm.e σ F) (Nt.herm.e σ G) = inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) := by
  simp only [herm, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_map]

theorem herm_conj : Nt.herm.Conj := by
  intro σ f g
  rw [Nt.herm_inner, Nt.herm_inner, Nt.inner_euclideanEmbedding_eq_average, Nt.inner_euclideanEmbedding_eq_average]
  rw [← Fintype.card_congr (Nt.cj σ), ← (Nt.cj σ).sum_comp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Nt.ev_conj, Complex.conj_conj, star_mul', Complex.star_def, Complex.conj_ofReal, map_sum, map_mul]

end NetData

theorem sup_L2_bound_of_net : SupL2BoundFromNet (D := D) (B := B) (j := j) (ka := ka) := by
  intro Nt hM hL large₂ CG AG hP F σ
  rw [Nt.Bp_L2N_run hM hL]
  change B.supN j ka σ F ^ 2 ≤ _ * Nt.netN σ F ^ 2
  obtain ⟨y, hy⟩ := hM σ F
  have hS := B.supN_nonneg j ka σ F
  have hn : (1 : ℝ) ≤ (Fintype.card (Nt.NN σ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨y⟩).ne'
  have hsum0 : (0 : ℝ) ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Nt.netN σ F ^ 2 = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (by linarith)) hsum0)
  have h1 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : (B.supN j ka σ F / 4) ^ 2 ≤ ‖Nt.ev σ y F‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  have h3 : B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := by
    rw [hsq]
    have : 16 * (Fintype.card (Nt.NN σ) : ℝ) * ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2) =
        16 * ∑ y, ‖Nt.ev σ y F‖ ^ 2 := by
      field_simp
    rw [this]
    have h4 : (B.supN j ka σ F / 4) ^ 2 = B.supN j ka σ F ^ 2 / 16 := by ring
    linarith
  have h4 : 16 * (Fintype.card (Nt.NN σ) : ℝ) ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 16 * (Fintype.card (Nt.NN σ) : ℝ))]
    exact Real.exp_le_exp.mpr (hP σ)
  calc B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := h3
    _ ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * Nt.netN σ F ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

theorem deepHermNet : DeepHermNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X
  exact ⟨_, { e := Nt.herm.e, norm_e := fun σ F => (Nt.herm.norm_e σ F).trans (by rw [Nt.Bp_L2N_run hM hL]) },
    Nt.herm_conj⟩

theorem deepLogDNet : DeepLogDNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X σ Pd hI hP
  change Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd
  have hd : finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hb := hI _ _ (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have := hb.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hlog0 : 0 ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := Real.log_natCast_nonneg _
  rcases Nat.eq_zero_or_pos (finrank B.KO (B.Cusp j ka)) with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · calc Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hd)
      _ ≤ Pd := hP

end Formalism.MainNotions.Gaps.NetNorms
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem comap_span_of_subset {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set M) (hs : s ⊆ p) :
    (Submodule.span R s).comap (p.subtype.restrictScalars R) = Submodule.span R ((↑) ⁻¹' s : Set ↥p) := by
  apply Submodule.map_injective_of_injective (f := p.subtype.restrictScalars R) Subtype.val_injective
  rw [Submodule.map_comap_eq, Submodule.map_span]
  have h : (p.subtype.restrictScalars R) '' ((↑) ⁻¹' s : Set ↥p) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  rw [h, inf_eq_right, Submodule.span_le]
  intro x hx
  exact ⟨⟨x, hs hx⟩, rfl⟩

theorem mem_span_subtype_iff {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set ↥p) (x : ↥p) :
    x ∈ Submodule.span R s ↔ (x : M) ∈ Submodule.span R ((↑) '' s : Set M) := by
  have h : Submodule.span R ((↑) '' s : Set M) = (Submodule.span R s).map (p.subtype.restrictScalars R) := by
    rw [Submodule.map_span]; rfl
  rw [h]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem isBaseChange_span {K K' V : Type*} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (p : Submodule K' (K' ⊗[K] V))
    (hp : p = Submodule.span K' ((fun v => (1 : K') ⊗ₜ[K] v) '' (W : Set V)))
    (f : ↥W →ₗ[K] ↥p) (hf : ∀ w, (f w : K' ⊗[K] V) = (1 : K') ⊗ₜ[K] (w : V)) : IsBaseChange K' f := by
  have hg : ∀ x : K' ⊗[K] ↥W, ((f.liftBaseChange K' x : ↥p) : K' ⊗[K] V) = W.subtype.baseChange K' x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, Submodule.coe_smul, hf, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Submodule.coe_add, hx, hy]
  have hbij : Function.Bijective (f.liftBaseChange K') := by
    constructor
    · intro x y hxy
      have h1 : W.subtype.baseChange K' x = W.subtype.baseChange K' y := by rw [← hg, ← hg, hxy]
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K') W.subtype Subtype.val_injective h1
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨y, hy⟩ -
      have hy' := hy
      rw [hp] at hy'
      induction hy' using Submodule.span_induction with
      | mem y h =>
        obtain ⟨w, hw, rfl⟩ := h
        refine ⟨(1 : K') ⊗ₜ[K] (⟨w, hw⟩ : ↥W), Subtype.ext ?_⟩
        rw [LinearMap.liftBaseChange_tmul, one_smul, hf]
      | zero => exact (LinearMap.range (f.liftBaseChange K')).zero_mem
      | add a b ha hb iha ihb =>
        exact (LinearMap.range (f.liftBaseChange K')).add_mem (iha (hp ▸ ha)) (ihb (hp ▸ hb))
      | smul r a ha ih => exact (LinearMap.range (f.liftBaseChange K')).smul_mem r (ih (hp ▸ ha))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange K') hbij) (fun x => by simp)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

def embV (F : B.Cusp j ka) : ↥(Vw X la N ka) := ⟨emb X la N (X.inc ka F), emb_mem_Vw X la N ka F⟩

theorem inW_loc_eq_span (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    T0.inW X ka la (X.loc la M) =
      Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} := by
  unfold T0.inW PJ.loc
  rw [comap_span_of_subset (R := X.Ol la) (T0.WL X ka la) (X.bc la '' (M : Set X.Forms))]
  · congr 1
    ext x
    constructor
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, hM hF, rfl⟩

theorem span_jW_inW (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    Submodule.span (Op X la N) (jW X la N ka '' (T0.inW X ka la (X.loc la M) : Set ↥(T0.WL X ka la))) =
      Submodule.span (Op X la N) {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} := by
  rw [inW_loc_eq_span X la ka M hM]
  have h1 : jW X la N ka '' (Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} :
      Set ↥(T0.WL X ka la)) =
      ((Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F}).map
        ((jW X la N ka).restrictScalars (X.Ol la)) : Set ↥(Vw X la N ka)) := rfl
  rw [h1, Submodule.map_span, Submodule.span_span_of_tower]
  congr 1
  ext f
  constructor
  · rintro ⟨x, ⟨F, hF, hx⟩, rfl⟩
    refine ⟨F, hF, ?_⟩
    show bcV X la N (x : X.Vl la) = _
    rw [hx, emb_eq_bcV]
  · rintro ⟨F, hF, hf⟩
    refine ⟨⟨X.bc la F, Submodule.subset_span ⟨F, hM hF, rfl⟩⟩, ⟨F, hF, rfl⟩, Subtype.ext ?_⟩
    rw [hf, emb_eq_bcV]
    rfl

theorem integralForms_eq_span : M1 X la N ka = Submodule.span (Op X la N) (Set.range fun F : B.Mlat j ka => embV X la N ka F) := by
  unfold M1 T0.MW
  rw [span_jW_inW X la N ka _ le_rfl]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, hf⟩
    exact ⟨⟨F, hF⟩, Subtype.ext hf.symm⟩
  · rintro ⟨F, rfl⟩
    exact ⟨_, ⟨F, F.2, rfl⟩, rfl⟩

theorem Th1_eq (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) (h : X.Theta S ka wL wF T ≤ X.Msup ka) :
    Th1 X la N ka S wL wF T = Submodule.span (Op X la N)
      {f : ↥(Vw X la N ka) | ∃ F ∈ X.Theta S ka wL wF T, (f : Rp X la N) = emb X la N F} :=
  span_jW_inW X la N ka _ h

theorem jW_isBaseChange (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    IsBaseChange (Kp X la N) (jW X la N ka) := by
  have hp : Vw X la N ka = Submodule.span (Kp X la N) ((fun v => bcV X la N v) '' (T0.WL X ka la : Set (X.Vl la))) := by
    refine le_antisymm ?_ ?_
    · rw [Vw_eq_span_image X la N ka hM]
      refine Submodule.span_mono ?_
      rintro _ ⟨F, hF, rfl⟩
      exact ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, hF, rfl⟩, rfl⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact bcV_mem_Vw X la N ka hx
  exact isBaseChange_span (K := X.Kl la) (K' := Kp X la N) (V := X.Vl la) (T0.WL X ka la) (Vw X la N ka) hp
    (jW X la N ka) (fun w => rfl)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NonvanishingSectionCondition
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem dm_eq (T : ParamsT D L P) : WeightFamilies.dimY D D.R.m = T.Dp := by
  rw [T.Dp_eq]
  unfold WeightFamilies.dimY Ranks.sigW Ranks.r
  simp [Nat.choose_two_right]

theorem order_le_modulus (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : T.TO ≤ q0N T := by
  unfold q0N
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hZ' : (1 : ℝ) ≤ zBase L := by
    have h : (1 : ℝ) ≤ 10 ^ 60 := by norm_num
    linarith
  have hPP : 1 ≤ T.PP := by
    rw [T.PP_eq]
    exact one_le_mul_of_one_le_of_one_le T.one_le_CP (Real.one_le_rpow hZ' (by linarith [T.eP_ge]))
  have hbpos : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have h1 : (T.TO : ℝ) ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_right hTpos.le hPP) T.TO_PP'
  have h2 := mul_self_le_mul_self hTpos.le h1
  rw [← Real.rpow_add hbpos] at h2
  norm_num at h2
  have hq : (T.TO : ℝ) ≤ L.sc.b / (T.TO : ℝ) := by
    rw [le_div_iff₀ hTpos]
    linarith
  exact_mod_cast le_trans hq (Nat.le_ceil _)

abbrev runOf (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : RunN D where
  T := T.TO
  nW := T.nWn
  nP := T.nP
  Q0 := q0N T
  T_pos := by have := T.TO_40; omega
  nW_even := T.nW_even
  even_nP₂ := T.even_nP₂
  split := T.split
  nP_le_nW := T.nW_lo.2.2
  hQ0 := by
    rw [dm_eq T]
    have := T.TO_nW; have := order_le_modulus T S hZ
    omega

def Kc0 : KAdm := ⟨1, 1, 1, 1, 1, 1, 1, 1, 2⟩

def NonvanishingSectionCondition (T : ParamsT D L P) : KHyp := ⟨10, 20, 1000, 12, T.CP, T.eP, 2⟩

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

theorem eTq : ((runOf T S hZ).Tq : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) := by
  unfold RunN.Tq Tp
  dsimp only [runOf]
  rw [dm_eq T]
  push_cast
  ring

theorem eQ : ((runOf T S hZ).Q : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r := by
  unfold RunN.Q
  push_cast
  linarith [eTq T S hZ]

theorem ekl : ((runOf T S hZ).kl : ℝ) =
    ((T.Dp : ℝ) + 2) * T.nWn + 2 * D.R.r + ((T.TO : ℝ) + ((T.Dp : ℝ) + 2)) * (q0N T : ℝ) := by
  unfold RunN.kl
  push_cast
  rw [eTq T S hZ]
  have hd : (Dm D : ℝ) = (T.Dp : ℝ) := by
    first
    | (unfold Dm; exact_mod_cast dm_eq T)
    | (simp only [Dm]; exact_mod_cast dm_eq T)
    | exact_mod_cast dm_eq T
  rw [hd]

theorem enV : (D.R.nV : ℝ) = (T.nP : ℝ) + (T.TO : ℝ) * T.nWn := by
  have h := T.split
  unfold Ranks.nV
  exact_mod_cast h

theorem ka_le : (runOf T S hZ).ka.size ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sK ?_
  have h := (runOf T S hZ).ka_size_le
  rw [ekl, eTq, eQ, enV T] at h
  exact h

theorem b_le_kl : L.sc.b ≤ ((runOf T S hZ).kl : ℝ) := by
  rw [ekl T S hZ]
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hq : L.sc.b / (T.TO : ℝ) ≤ (q0N T : ℝ) := by unfold q0N; exact Nat.le_ceil _
  have hq' : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ) := by
    rw [div_le_iff₀ hTpos] at hq
    linarith
  have h0 : (0 : ℝ) ≤ (T.Dp : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (T.nWn : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (q0N T : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) := by positivity
  nlinarith [mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h1,
    mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h2]

theorem b_le_ka : L.sc.b ≤ (runOf T S hZ).ka.size := (b_le_kl T S hZ).trans (runOf T S hZ).ka_size_ge

theorem dF_le : (DF (runOf T S hZ).wL : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).dL ?_
  have h := (runOf T S hZ).DF_wL_le
  rw [eQ] at h
  exact h

theorem g_ge (P : ParameterChoice' D L) (i : Fin 2) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
  exact h1.trans (h2 i).1

theorem qq_ge (P : ParameterChoice' D L) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (qq D : ℝ) := by
  unfold qq
  first
  | (rw [Nat.cast_min]; exact le_min (g_ge P 0) (g_ge P 1))
  | (push_cast; exact le_min (g_ge P 0) (g_ge P 1))

theorem eRR : WeightFamilies.RRv D 2 = D.host.rdE ^ 2 := by
  unfold WeightFamilies.RRv
  first
  | rfl
  | simp

theorem eg0 : (g0 D : ℝ) = 1250 * D.R.r := by
  unfold g0
  push_cast
  ring

theorem third_hypothesis_of_params : H3 L (NonvanishingSectionCondition T) T.CP T.eP 2 0 (runOf T S hZ).wL T.TO := by
  have hR := rn_of T S hZ
  have hd0 : (0 : ℝ) ≤ (DF (runOf T S hZ).wL : ℝ) := Nat.cast_nonneg _
  have hd := dF_le T S hZ
  have hq := qq_ge P
  have hq0 : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq
  have hb := hR.h3b hd0 hd hq
  have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T]
    exact hR.h3a hd0 hd hq
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T, eg0]
    exact hb
  · rw [Real.rpow_zero, one_mul, WeightFamilies.PPv_rec T, dm_eq T]
    refine le_trans ?_ T.TO_ge
    have hden : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    apply div_le_div_of_nonneg_right _ hden.le
    have hP := hR.PP_pos
    exact le_mul_of_one_le_right (by positivity) hx1
  · show (T.TO : ℝ) * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1
    rw [eRR, WeightFamilies.PPv_rec T, eg0]
    have e : (T.TO : ℝ) * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * (1250 * D.R.r) =
        ((T.TO : ℝ) * (1250 * D.R.r) * D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    rw [e, div_le_one hq0]
    exact hb
  · show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 2 ^ 2 *
      (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2
    rw [eRR, WeightFamilies.PPv_rec T]
    have hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 := by
      have : (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ hm0.le hmk 3
      calc (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 3 :=
            mul_le_mul hfk this (by positivity) (by positivity)
        _ = (D.R.k : ℝ) ^ 4 := by ring
    have he := hR.h3e hd0 hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm
    have e : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) =
        ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2)) / (qq D : ℝ) := by ring
    rw [e, div_le_iff₀ hq0]
    linarith
  · rw [dm_eq T]
    have := hR.h3f hd0 hd hq
    have e : (T.Dp : ℝ) + 2 + 2 = (T.Dp : ℝ) + 4 := by ring
    rw [e] at this
    exact this

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end

