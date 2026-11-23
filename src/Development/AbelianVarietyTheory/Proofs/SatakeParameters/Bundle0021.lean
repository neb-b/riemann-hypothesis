module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvalues
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem absSpace_eq_bot_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {r : ℝ} (hr : r ≠ 1) :
    absSpace f r = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun α hα => ?_)
  by_contra hne
  have hev : f.HasEigenvalue α := Module.End.hasEigenvalue_iff.mpr fun h => hne (h ▸ le_refl _)
  have hroot : (minpoly ℂ f).IsRoot α := Module.End.hasEigenvalue_iff_isRoot.mp hev
  have hc : α ∈ f.charpoly.roots := by
    rw [mem_roots (LinearMap.charpoly_monic f).ne_zero, ← Polynomial.dvd_iff_isRoot]
    exact (Polynomial.dvd_iff_isRoot.mpr hroot).trans (LinearMap.minpoly_dvd_charpoly f)
  exact hr (hα ▸ hf α hc)

theorem absSpace_one_eq_top_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) :
    absSpace f 1 = ⊤ := by
  rw [eq_top_iff, ← hs.iSup_eigenspace_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : ‖α‖ = 1
  · exact le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = 1) => f.eigenspace β) α hα le_rfl
  · have := absSpace_eq_bot_of_norm_charpoly_roots hf hα
    rw [eq_bot_iff] at this
    refine le_trans ?_ (bot_le : (⊥ : Submodule ℂ V) ≤ absSpace f 1)
    exact le_trans (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = ‖α‖) => f.eigenspace β) α rfl le_rfl) this

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  intro E Ω _ _ _ _ _ A w h a _ heig
  induction a using WD.ind with
  | hP n a =>
  rw [WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := by
    intro α hα; exact heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hne : ∀ s : ℝ, s ≠ 0 → ((normV w : ℕ) : ℝ) ^ s ≠ 1 := by
    intro s hs h1
    rw [← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at h1
    exact hs h1
  refine ⟨eq_top_iff.mpr ?_, fun i => ?_⟩
  · rw [← absSpace_one_eq_top_of_norm_charpoly_roots (a.semisimple φ) hroots]
    refine le_iSup_of_le (0 : ℤ) ?_
    simp
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, Nat.cast_zero, neg_zero]
      exact Set.bijOn_id _
    · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
      rw [absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith)),
        absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith))]
      simp only [Submodule.bot_coe]
      exact ⟨fun v hv => by rw [Set.mem_singleton_iff.mp hv, map_zero]; rfl,
        fun v hv v' hv' _ => by rw [Set.mem_singleton_iff.mp hv, Set.mem_singleton_iff.mp hv'],
        fun v hv => ⟨0, rfl, by rw [Set.mem_singleton_iff.mp hv, map_zero]⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open scoped Pointwise

namespace GlobalTheory.SmoothRiesz

theorem exists_mem_eq_on_of_finiteDimensional {V : Type} [AddCommGroup V] [Module ℂ V]
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (L : V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W] :
    ∃ u ∈ W, ∀ w ∈ W, L w = Bf u w := by
  first
  | exact @_root_.GlobalTheory.ExistsRepresentation.exists_represent
  | exact _root_.GlobalTheory.ExistsRepresentation.exists_represent
  | (apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsRepresentation.exists_represent <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsRepresentation.exists_represent <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsRepresentation.exists_represent ..)

theorem finite_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (hsm : IsSmooth σ)
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (y : V) :
    ((fun k : G => σ k y) '' (K : Set G)).Finite := by
  let S : Set G := {g | σ g y = y}
  have hSo : IsOpen S := hsm y
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun g : K => (g : G) • S) (fun g => hSo.smul _)
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, Set.mem_smul_set.2 ⟨1, by simp [S], by simp⟩⟩)
  refine ((t.finite_toSet.image (fun i : K => σ (i : G) y))).subset ?_
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.1 hki
  refine ⟨i, hi, ?_⟩
  have hs' : σ s y = y := hs
  simp only [smul_eq_mul, map_mul, Module.End.mul_apply, hs']

theorem exists_eq_of_invariant {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hadm : IsAdmissible σ) (hpos : ∀ v, v ≠ 0 → 0 < (Bf v v).re)
    (hinv : ∀ g v w, Bf (σ g v) (σ g w) = Bf v w) (L : V →ₗ⋆[ℂ] ℂ)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hL : ∀ s ∈ K, ∀ w, L (σ s w) = L w) : ∃ u : V, ∀ w, L w = Bf u w := by
  haveI : FiniteDimensional ℂ (fixed σ K) := hadm.2 K hKo hKc
  obtain ⟨u, huK, hu⟩ := exists_mem_eq_on_of_finiteDimensional Bf hpos L (fixed σ K)
  have hfix : ∀ k ∈ K, σ k u = u := fun k hk => by
    simpa using huK ⟨k, hk⟩
  refine ⟨u, fun w => ?_⟩
  have hcomp : ∀ (a b : G) (x : V), σ a (σ b x) = σ (a * b) x := fun a b x => by
    rw [map_mul, Module.End.mul_apply]
  let O : Finset V := (finite_orbit σ hadm.1 K hKc w).toFinset
  have hO : ∀ x, x ∈ O ↔ ∃ k ∈ K, σ k w = x := fun x => by simp [O]
  have hwO : w ∈ O := (hO w).2 ⟨1, K.one_mem, by simp⟩
  have hcard : ((O.card : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨w, hwO⟩)
  have heK : (∑ x ∈ O, x) ∈ fixed σ K := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sum]
    refine Finset.sum_nbij' (fun x => σ k x) (fun x => σ (k : G)⁻¹ x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨k * c, K.mul_mem k.2 hc, (hcomp _ _ _).symm⟩
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
      exact (hO _).2 ⟨(k : G)⁻¹ * c, K.mul_mem (K.inv_mem k.2) hc, (hcomp _ _ _).symm⟩
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rw [hcomp]; simp
    · intro x _
      rfl
  have hLO : ∀ x ∈ O, L x = L w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    exact hL c hc w
  have hBO : ∀ x ∈ O, Bf u x = Bf u w := fun x hx => by
    obtain ⟨c, hc, rfl⟩ := (hO x).1 hx
    conv_lhs => rw [← hfix c hc]
    exact hinv c u w
  have key := hu _ heK
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_congr rfl hLO, Finset.sum_congr rfl hBO, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at key
  exact mul_left_cancel₀ hcard key

end GlobalTheory.SmoothRiesz

namespace GlobalTheory

theorem exists_vector_of_smooth_antilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsAdmissible σ → (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) →
    (∀ v, v ≠ 0 → 0 < (Bf v v).re) → (∀ g v w, Bf (σ g v) (σ g w) = Bf v w) →
    ∀ (L : V →ₗ⋆[ℂ] ℂ) (S : Subgroup (GL (Fin r) k)), IsOpen (S : Set (GL (Fin r) k)) →
      (∀ s ∈ S, ∀ w, L (σ s w) = L w) → ∃ u : V, ∀ w, L w = Bf u w := by
  intro k _ _ _ _ r V _ _ σ Bf hadm _ hpos hinv L S hSo hL
  have hKo : IsOpen ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    hSo.inter SplitFlip.isOpen_KO
  have hKc : IsCompact ((S ⊓ KO k (Fin r) : Subgroup _) : Set (GL (Fin r) k)) :=
    SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKo) inf_le_right
  exact SmoothRiesz.exists_eq_of_invariant σ Bf hadm hpos hinv L _ hKo hKc
    fun s hs => hL s hs.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne TensorProduct

namespace GlobalTheory.WeilDeligne.TwistInj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem apply_eq_det_smul (f : Module.End ℂ (Fin 1 → ℂ)) (v : Fin 1 → ℂ) :
    f v = LinearMap.det f • v := by
  have hd : LinearMap.det f = f (Pi.single 0 1) 0 := by
    conv_lhs => rw [← Matrix.toLin'_toMatrix' f]
    rw [LinearMap.det_toLin', Matrix.det_fin_one, LinearMap.toMatrix'_apply]
  have hv : v = v 0 • (Pi.single 0 1 : Fin 1 → ℂ) := by
    funext i; fin_cases i; simp
  funext i; fin_cases i
  rw [hv, map_smul, hd]
  simp [mul_comm]

def chr (c : WDRep h (Fin 1 → ℂ)) : Weil h →* ℂˣ :=
  (Units.map (LinearMap.det : Module.End ℂ (Fin 1 → ℂ) →* ℂ)).comp c.ρ.asGroupHom

theorem coe_chr (c : WDRep h (Fin 1 → ℂ)) (σ : Weil h) :
    (chr c σ : ℂ) = LinearMap.det (c.ρ σ) := by
  simp [chr, Representation.asGroupHom_apply]

theorem isSmooth_chr (c : WDRep h (Fin 1 → ℂ)) : IsSmooth (chr c) :=
  c.smooth.of_le fun σ hσ => Units.ext (by rw [coe_chr, hσ, map_one]; rfl)

theorem N_eq_zero (c : WDRep h (Fin 1 → ℂ)) : c.N = 0 := by
  have hz : LinearMap.det (0 : Module.End ℂ (Fin 1 → ℂ)) = 0 := by
    have := congrFun (apply_eq_det_smul 0 (fun _ => 1)) 0
    simpa using this.symm
  obtain ⟨k, hk⟩ := c.nilpotent
  have h0 : LinearMap.det c.N = 0 := by
    have : LinearMap.det c.N ^ k = 0 := by rw [← map_pow, hk, hz]
    exact pow_eq_zero_iff'.mp this |>.1
  refine LinearMap.ext fun v => ?_
  rw [apply_eq_det_smul, h0, zero_smul]
  rfl

theorem tensor_iso_twist {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (c : WDRep h (Fin 1 → ℂ)) :
    (a.tensor c).Iso (a.twist (chr c) (isSmooth_chr c)) := by
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [WDRep.tensor_ρ, TensorProduct.map_tmul, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.funUnique_apply,
        TensorProduct.rid_tmul, WDRep.twist_ρ, LinearMap.smul_apply, map_smul, coe_chr]
      rw [apply_eq_det_smul (c.ρ σ) y, smul_smul]
      simp [Function.eval, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [N_eq_zero c, Function.eval, WDRep.twist]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem iso_of_twist {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {a : WDRep h V} {b : WDRep h V'} (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ)
    (hab : (a.twist χ hχ).Iso (b.twist χ hχ)) : a.Iso b := by
  obtain ⟨e, h1, h2⟩ := hab
  refine ⟨e, fun σ v => ?_, h2⟩
  have := h1 σ v
  simp only [WDRep.twist_ρ, LinearMap.smul_apply, map_smul] at this
  exact smul_right_injective V' (Units.ne_zero (χ σ)) this

end GlobalTheory.WeilDeligne.TwistInj


open GlobalTheory.WeilDeligne.TwistInj in
theorem GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a b c : WD h), c.lpDim = 1 → a.lpChar c = b.lpChar c → a = b := by
  intro E Ω _ _ _ _ _ A w h a b c hc hab
  induction a using WD.ind with
  | hP n a =>
  induction b using WD.ind with
  | hP m b =>
  induction c using WD.ind with
  | hP k c =>
  rw [WD.lpDim_mk, Module.finrank_fin_fun] at hc
  subst hc
  rw [WD.lpChar_mk, WD.lpChar_mk, WD.mk_eq_mk] at hab
  exact WD.sound (TwistInj.iso_of_twist (TwistInj.chr c) (TwistInj.isSmooth_chr c)
    (((TwistInj.tensor_iso_twist a c).symm.trans hab).trans (TwistInj.tensor_iso_twist b c)))
end
end

