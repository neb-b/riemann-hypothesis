module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulTopIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0045
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0026
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0034
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFSpanConsBasis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtHomInjective
section
open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def extHom (S : VecSplit h h') : (V' ≃ₗ[K] V') →* (V ≃ₗ[K] V) where
  toFun := SplitBAux.extOf S
  map_one' := by
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply]
    rfl
  map_mul' := by
    intro a b
    ext v
    obtain ⟨c, x, rfl⟩ := S.cover v
    rw [SplitBAux.extOf_apply, mul_apply_eq_comp, mul_apply_eq_comp, SplitBAux.extOf_apply,
      SplitBAux.extOf_apply]

theorem extHom_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : extHom S g' = SplitBAux.extOf S g' := rfl

theorem extHom_injective (S : VecSplit h h') : Function.Injective (extHom S) := by
  intro a b e
  ext x
  apply S.inj
  rw [← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι S b, ← extHom_apply, e, extHom_apply]

def autExt (S : VecSplit h h') (M : Submodule (𝓞 K) V) : Subgroup (V' ≃ₗ[K] V') :=
  (autSub h M).comap (extHom S)

def oM (S : VecSplit h h') (M : Submodule (𝓞 K) V) : ℕ :=
  (autExt S M).relIndex (autSub h' (S.cut M))

def nu {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h₀ : W →ₗ⋆[K] W →ₗ[K] K) (A : Submodule (𝓞 K) W) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  alphaL h₀ A 𝔭 / (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K W * vd h₀ A 𝔭)

def kap (S : VecSplit h h') (M : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) (J k : ℕ) : ℝ :=
  (cnt h M 𝔭 k n (tube (autSub h M) M 𝔭 J S.x₀) : ℝ) /
    ((Ideal.absNorm 𝔭 : ℝ) ^ vd h M 𝔭 * nu h M 𝔭) * (nu h' (S.cut M) 𝔭 / (oM S M : ℝ))

theorem nu_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : 0 < nu h (locF 𝔭 A₀) 𝔭 := by
  have e : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    congr 1
    ext k
    rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  unfold nu
  rw [e]
  exact div_pos (alphaL_pos hK hF hs hd hA₀ hA₀i h𝔭) (pow_pos hq _)

theorem nu_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀)
    (hB₀ : Submodule.IsFullLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    nu h (locF 𝔭 A₀) 𝔭 * ((autSub h (locF 𝔭 A₀)).relIndex (autSub h (locF 𝔭 B₀)) : ℝ) =
      nu h (locF 𝔭 B₀) 𝔭 * ((autSub h (locF 𝔭 B₀)).relIndex (autSub h (locF 𝔭 A₀)) : ℝ) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have h1 := local_density_ratio_holds K F hK hF V h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  rw [orbCount_eq_relIndex, orbCount_eq_relIndex] at h1
  unfold nu
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (pow_pos hq _).ne' (pow_pos hq _).ne']
  linear_combination h1

theorem autExt_le (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autExt S M ≤ autSub h' (S.cut M) := by
  intro g' hg
  obtain ⟨h1, h2⟩ : SplitBAux.extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h ∧
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') M = M := hg
  refine ⟨fun a b => ?_, ?_⟩
  · rw [← S.isom, ← S.isom, ← SplitBAux.extOf_ι, ← SplitBAux.extOf_ι, h1]
  · rw [← StabilizerLattices.cut_gmap_extOf, h2]

theorem inf_fixS_eq_map (S : VecSplit h h') (M : Submodule (𝓞 K) V) :
    autSub h M ⊓ fixS S.x₀ = (autExt S M).map (extHom S) := by
  ext g
  constructor
  · rintro ⟨hg, hx⟩
    have hx' : g S.x₀ = S.x₀ := hx
    have e : extHom S (SplitBAux.res S g hg.1 hx') = g := by
      ext v
      obtain ⟨c, a, rfl⟩ := S.cover v
      rw [extHom_apply, SplitBAux.extOf_apply, SplitBAux.res_spec, map_add (f := _), map_smul, hx']
    refine ⟨SplitBAux.res S g hg.1 hx', ?_, e⟩
    change extHom S _ ∈ autSub h M
    rw [e]
    exact hg
  · rintro ⟨g', hg', rfl⟩
    exact ⟨hg', SplitBAux.extOf_x₀ S g'⟩

theorem relIndex_fix_eq (hs : h.IsSymm) (S : VecSplit h h') (M₁ M₂ : Submodule (𝓞 K) V) :
    (autSub h M₂ ⊓ fixS S.x₀).relIndex (autSub h M₁ ⊓ fixS S.x₀) =
      (autExt S M₂).relIndex (autExt S M₁) := by
  rw [inf_fixS_eq_map, inf_fixS_eq_map, Subgroup.relIndex_map_map_of_injective _ _ (extHom_injective S)]

theorem oM_ne_zero (hs : h.IsSymm) (S : VecSplit h h') {M₁ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsFullLattice K M₁) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : S.x₀ ∈ locF 𝔭 M₁) : oM S (locF 𝔭 M₁) ≠ 0 := by
  have hcut := StabilizerLattices.isFullLattice_cut S hM₁
  have hN : Submodule.IsFullLattice K (S.adjoin (S.cut M₁)) := by
    refine { toIsLattice := (S.isLattice_adjoin_iff' _).mpr hcut.toIsLattice, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, a, rfl⟩ := S.cover v
    refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin _))) ?_
    have ha : a ∈ Submodule.span K (S.cut M₁ : Set V') := by
      rw [hcut.span_eq_top]
      exact Submodule.mem_top
    have hle : (Submodule.span K (S.cut M₁ : Set V')).map S.ι ≤
        Submodule.span K (S.adjoin (S.cut M₁) : Set V) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨b, hb, rfl⟩
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
    exact hle (Submodule.mem_map_of_mem ha)
  have h1 : (autExt S (locF 𝔭 M₁)).relIndex (autExt S (locF 𝔭 (S.adjoin (S.cut M₁)))) ≠ 0 :=
    Subgroup.relIndex_comap_ne_zero (extHom S) (relIndex_autSub_ne_zero h hN hM₁ h𝔭)
  have h2 : autSub h' (S.cut (locF 𝔭 M₁)) ≤ autExt S (locF 𝔭 (S.adjoin (S.cut M₁))) := by
    rintro g' ⟨hg1, hg2⟩
    refine ⟨SplitBAux.extOf_mem_isom hs S hg1, ?_⟩
    change Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') _ = _
    rw [LocalizedFibreSets.cut_locF, LocalizedFibreSets.gmap_locF] at hg2
    rw [LocalizedFibreSets.gmap_locF, SplitBAux.gmap_extOf S g' rfl]
    have mono : ∀ T T' : Submodule (𝓞 K) V', locF 𝔭 T = locF 𝔭 T' →
        locF 𝔭 (S.adjoin T) ≤ locF 𝔭 (S.adjoin T') := by
      intro T T' e
      rw [← LocalizedFibreSets.locF_idem 𝔭 (S.adjoin T')]
      apply LocF.locF_mono
      unfold VecSplit.adjoin
      refine sup_le ((le_sup_left).trans (LocalizedFibreSets.le_locF 𝔭 _)) ?_
      rw [Submodule.map_le_iff_le_comap]
      intro a ha
      have ha' : a ∈ locF 𝔭 T' := e ▸ LocalizedFibreSets.le_locF 𝔭 T ha
      obtain ⟨s, hs, hsa⟩ := ha'
      refine ⟨s, hs, ?_⟩
      apply Submodule.mem_sup_right
      refine Submodule.mem_map.mpr ⟨s • a, hsa, ?_⟩
      exact LinearMap.map_smul_of_tower _ _ _
    exact le_antisymm (mono _ _ hg2) (mono _ _ hg2.symm)
  intro h0
  exact h1 (Subgroup.relIndex_eq_zero_of_le_right h2 h0)

theorem kap_alg {E₁ E₂ Q₁ Q₂ ν₁ ν₂ μ₁ μ₂ a b c d a' b' o₁ o₂ : ℝ} (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (ha' : a' ≠ 0)
    (ho₁ : o₁ ≠ 0) (ho₂ : o₂ ≠ 0) (h1 : E₁ * Q₂ * b * a' = E₂ * Q₁ * a * b')
    (h2 : ν₁ * b = ν₂ * a) (h3 : μ₁ * d = μ₂ * c) (h4 : a' * o₁ * d = c * o₂ * b') :
    E₁ / (Q₁ * ν₁) * (μ₁ / o₁) = E₂ / (Q₂ * ν₂) * (μ₂ / o₂) := by
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hQ₁ hν₁) ho₁) (mul_ne_zero (mul_ne_zero hQ₂ hν₂) ho₂)]
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hb ha') ha) hd)
  linear_combination (μ₁ * d * ν₂ * a * o₂) * h1 + (E₂ * Q₁ * a * b' * ν₂ * a * o₂) * h3 -
    (E₂ * Q₁ * a * b' * μ₂ * c * o₂) * h2 - (E₂ * μ₂ * Q₁ * ν₁ * b * a) * h4

theorem kap_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h')
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsFullLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F)) (hx₁ : S.x₀ ∈ locF 𝔭 M₁)
    (hx₂ : S.x₀ ∈ locF 𝔭 M₂) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      kap S (locF 𝔭 M₁) 𝔭 n J k = kap S (locF 𝔭 M₂) 𝔭 n J k := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    exact_mod_cast reductionMapsOfForms.absNorm_pos h𝔭
  have hT₁ := StabilizerLattices.isFullLattice_cut S hM₁
  have hT₂ := StabilizerLattices.isFullLattice_cut S hM₂
  have hT₁i := UnimodularLocalization.isIntegralLat_cut S hM₁i
  have hT₂i := UnimodularLocalization.isIntegralLat_cut S hM₂i

  set P := autExt S (locF 𝔭 M₁) with hP
  set W := autExt S (locF 𝔭 M₂) with hW
  set Q := autSub h' (S.cut (locF 𝔭 M₁)) with hQ
  set R := autSub h' (S.cut (locF 𝔭 M₂)) with hR
  have hPQ : P ≤ Q := autExt_le S _
  have hWR : W ≤ R := autExt_le S _
  have ho₁ : P.relIndex Q ≠ 0 := oM_ne_zero hs S hM₁ h𝔭 hx₁
  have ho₂ : W.relIndex R ≠ 0 := oM_ne_zero hs S hM₂ h𝔭 hx₂
  have hc : R.relIndex Q ≠ 0 := by
    rw [hR, hQ, LocalizedFibreSets.cut_locF, LocalizedFibreSets.cut_locF]
    exact relIndex_autSub_ne_zero h' hT₁ hT₂ h𝔭
  have hd' : Q.relIndex R ≠ 0 := by
    rw [hR, hQ, LocalizedFibreSets.cut_locF, LocalizedFibreSets.cut_locF]
    exact relIndex_autSub_ne_zero h' hT₂ hT₁ h𝔭
  have hu : W.relIndex Q ≠ 0 := Subgroup.relIndex_ne_zero_trans ho₂ hc
  have ht : Q.relIndex W ≠ 0 := fun h0 => hd' (Subgroup.relIndex_eq_zero_of_le_right hWR h0)
  have ha' : W.relIndex P ≠ 0 := fun h0 => hu (Subgroup.relIndex_eq_zero_of_le_right hPQ h0)
  have c1 := relIndex_cocycle P Q W ha' ho₁ ht
  have c2 := relIndex_cocycle Q R W hu hd' (by rw [Subgroup.relIndex_eq_one.mpr hWR]; exact one_ne_zero)
  rw [Subgroup.relIndex_eq_one.mpr hPQ, one_mul] at c1
  rw [Subgroup.relIndex_eq_one.mpr hWR, mul_one] at c2
  have h4 : W.relIndex P * P.relIndex Q * Q.relIndex R = R.relIndex Q * W.relIndex R * P.relIndex W := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ht)
    calc Q.relIndex W * (W.relIndex P * P.relIndex Q * Q.relIndex R)
        = (P.relIndex Q * Q.relIndex W * W.relIndex P) * Q.relIndex R := by ring
      _ = (Q.relIndex R * W.relIndex Q) * P.relIndex W := by rw [← c1]; ring
      _ = _ := by rw [← c2]; ring
  have h2 := nu_mul_relIndex hK hF hs hd (by first | exact hM₁ | exact hM₁.toIsLattice) hM₁i (by first | exact hM₂ | exact hM₂.toIsLattice) hM₂i h𝔭
  have h3 := nu_mul_relIndex hK hF (S.isSymm hs) (S.isTotPosDef hd) (by first | exact hT₁ | exact hT₁.toIsLattice) hT₁i (by first | exact hT₂ | exact hT₂.toIsLattice) hT₂i h𝔭
  rw [← LocalizedFibreSets.cut_locF, ← LocalizedFibreSets.cut_locF, ← hQ, ← hR] at h3
  filter_upwards [pair hK hF hs hd (by first | exact hM₁ | exact hM₁.toIsLattice) hM₁i (by first | exact hM₂ | exact hM₂.toIsLattice) hM₂i h𝔭 hn hx hx₁ hx₂] with J hJ
  filter_upwards [hJ] with k hk
  rw [relIndex_fix_eq hs, relIndex_fix_eq hs, ← hP, ← hW] at hk
  unfold kap oM
  rw [← hP, ← hW, ← hQ, ← hR]
  refine kap_alg (pow_pos hq _).ne' (pow_pos hq _).ne'
    (nu_pos hK hF hs hd hM₁ hM₁i h𝔭).ne' (nu_pos hK hF hs hd hM₂ hM₂i h𝔭).ne'
    (a := ((autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) : ℝ))
    (b := ((autSub h (locF 𝔭 M₁)).relIndex (autSub h (locF 𝔭 M₂)) : ℝ))
    (c := (R.relIndex Q : ℝ)) (d := (Q.relIndex R : ℝ)) (a' := (W.relIndex P : ℝ))
    (b' := (P.relIndex W : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ h2 h3 ?_
  · exact_mod_cast relIndex_autSub_ne_zero h hM₁ hM₂ h𝔭
  · exact_mod_cast relIndex_autSub_ne_zero h hM₂ hM₁ h𝔭
  · exact_mod_cast hd'
  · exact_mod_cast ha'
  · exact_mod_cast ho₁
  · exact_mod_cast ho₂
  · exact_mod_cast hk
  · exact_mod_cast h4

end Formalism.HermitianLattices.Ext.L3.LIOrb
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsTotPosDefOfSmul
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinD

section One

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [NumberField F] in
theorem star_cK (hF : IsFixF K F) (c : F) : star (algebraMap F K c) = algebraMap F K c :=
  (hF _).2 ⟨c, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K] in
theorem smul_form_apply (c : K) (h : V →ₗ⋆[K] V →ₗ[K] K) (x y : V) : (c • h) x y = c * h x y := by
  rfl

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField K]
  [NumberField F] in
theorem isSymm_of_smul (hF : IsFixF K F) {c : F} (hc : algebraMap F K c ≠ 0)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : (algebraMap F K c • h).IsSymm) : h.IsSymm := by
  refine ⟨fun x y => ?_⟩
  have hxy := hs.eq x y
  rw [smul_form_apply, smul_form_apply, map_mul] at hxy
  have hst : (starRingEnd K) (algebraMap F K c) = algebraMap F K c := star_cK hF c
  rw [hst] at hxy
  exact mul_left_cancel₀ hc hxy

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [NumberField F] in
theorem isTotPosDef_of_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c : F}
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef (algebraMap F K c • h)) {x₀ : V}
    (h1 : h x₀ x₀ = 1) : IsTotPosDef h := by
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    simp at h1
  intro x hx φ
  have hreal : ∀ a : K, star a = a → (φ a).im = 0 := by
    intro a ha
    have := hK.2.1 φ a
    rw [ha] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  have hc0 := hd x₀ hx0 φ
  rw [smul_form_apply, h1, mul_one] at hc0
  have hcx := hd x hx φ
  rw [smul_form_apply, map_mul] at hcx
  have hcr : (φ (algebraMap F K c)).im = 0 := hreal _ (star_cK hF c)
  rw [Complex.mul_re, hcr, zero_mul, sub_zero] at hcx
  exact pos_of_mul_pos_right hcx hc0.le

theorem alphaL_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) :
    alphaL (algebraMap F K (c : F) • h) L 𝔭 =
      (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 1 + vF 𝔭 c ≤ k →
      (akCount (algebraMap F K (c : F) • h) L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (vF 𝔭 c * finrank K V ^ 2) * alphaL h L 𝔭 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.akCount_smul hK hF hs hd hL hLi h𝔭 hc (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := m) (by omega)]
    push_cast
    rw [show (m + vF 𝔭 c) * finrank K V ^ 2 = m * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      show 2 * vF 𝔭 c * finrank K V ^ 2 = vF 𝔭 c * finrank K V ^ 2 + vF 𝔭 c * finrank K V ^ 2 by ring,
      pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

theorem alphaN_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (hs' : (algebraMap F K (c : F) • h).IsSymm)
    (hd' : IsTotPosDef (algebraMap F K (c : F) • h)) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ≠ 0) :
    alphaN (algebraMap F K (c : F) • h) L 𝔭 (c * n) =
      (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have key : ∀ k, 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 + vF 𝔭 c ≤ k →
      (nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) : ℝ) /
          (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) =
        (Ideal.absNorm 𝔭 : ℝ) ^ vF 𝔭 c * alphaN h L 𝔭 n := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + vF 𝔭 c := ⟨k - vF 𝔭 c, by omega⟩
    rw [PinA.nkCount_smul hK hF hs hd hL hLi h𝔭 hc n (k := m + vF 𝔭 c) (by omega), Nat.add_sub_cancel,
      firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭
        (localValuationFiltration.notMem_pow_vF h𝔭 hn) (k := m) (by omega)]
    push_cast
    have h2 : 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V - 1) + vF 𝔭 c := by
      have h3 : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
      calc 2 * vF 𝔭 c * finrank K V = vF 𝔭 c * (2 * finrank K V) := by ring
        _ = vF 𝔭 c * ((2 * finrank K V - 1) + 1) := by rw [← h3]
        _ = _ := by ring
    rw [h2, show (m + vF 𝔭 c) * (2 * finrank K V - 1) =
        m * (2 * finrank K V - 1) + vF 𝔭 c * (2 * finrank K V - 1) by ring, pow_add, pow_add]
    field_simp <;> ring
  exact (tendsto_const_nhds.congr'
    (Filter.eventually_atTop.2 ⟨_, fun k hk => (key k hk).symm⟩)).limUnder_eq

end One

section Two

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isom_smul {c : K} (hc : c ≠ 0) (h : V →ₗ⋆[K] V →ₗ[K] K) :
    Formalism.HermitianLatticesTheory.isom (c • h) = Formalism.HermitianLatticesTheory.isom h := by
  ext g
  show (∀ x y, (c • h) (g x) (g y) = (c • h) x y) ↔ ∀ x y, h (g x) (g y) = h x y
  simp only [smul_form_apply, mul_right_inj' hc]

def unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) : VecSplit h h' where
  x₀ := S.x₀
  ι := S.ι
  inj := S.inj
  hx₀ := fun e => S.hx₀ (by rw [smul_form_apply, e, mul_zero])
  isom := fun a b => by
    have := S.isom a b
    rw [smul_form_apply, smul_form_apply] at this
    exact mul_left_cancel₀ hc this
  orth := fun a => by
    have := S.orth a
    rw [smul_form_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  cover := S.cover

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem fibLoc_unscale {c : K} (hc : c ≠ 0) (S : VecSplit (c • h) (c • h')) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 T = fibLoc (unscale hc S) L 𝔭 T := by
  simp only [fibLoc, isom_smul hc]
  rfl

theorem isLocReps_scale (hF : IsFixF K F) {c : 𝓞 F} (hc : algebraMap F K (c : F) ≠ 0)
    (S : VecSplit (algebraMap F K (c : F) • h) (algebraMap F K (c : F) • h'))
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s : Finset (Submodule (𝓞 K) V')}
    (hr : IsLocReps (unscale hc S) L 𝔭 s) : IsLocReps S L 𝔭 s := by
  have hLi' := PinA.isIntegralLat_smul hLi c
  have hiso : Formalism.HermitianLatticesTheory.isom (algebraMap F K (c : F) • h') = Formalism.HermitianLatticesTheory.isom h' := isom_smul hc h'
  refine ⟨fun T hT => ?_, fun T hTl hTi hTf => ?_⟩
  · obtain ⟨h1, -, h3⟩ := hr.1 T hT
    rw [← fibLoc_unscale] at h3
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero S hL hLi' h3
    refine ⟨h1, ?_, h3⟩
    have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
    rwa [hC, h1] at this
  · rw [fibLoc_unscale hc] at hTf
    obtain ⟨C, -, hCi, hC⟩ := UnimodularLocalization.exists_lattice_of_fibLoc_ne_zero (unscale hc S) hL hLi hTf
    have hTi' : IsIntegralAt 𝔭 h' T := by
      have := GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hCi
      rwa [hC, hTl] at this
    rw [hiso]
    exact hr.2 T hTl hTi' hTf

theorem alphaL_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) :
    alphaL h L 𝔭 = alphaN h L 𝔭 1 * alphaL h' (S.cut L) 𝔭 := by
  have hN : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
  have hdim := S.finrank_add_one
  have hA := alphaL_pos hK hF hs hd hL hLi h𝔭
  have h1𝔭 : (1 : 𝓞 F) ∉ 𝔭 ^ (0 + 1) := by
    rw [zero_add, pow_one]; exact (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top
  have key : ∀ k, 2 * vd h L 𝔭 + 2 ≤ k → alphaN h L 𝔭 1 ≠ 0 ∧
      (akCount h' (S.cut L) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V' ^ 2) =
        alphaL h L 𝔭 / alphaN h L 𝔭 1 := by
    intro k hk
    have eA := firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := k) (by omega)
    have eB := firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 h1𝔭 (k := k) (by omega)
    have eS := PinB.akCount_split hK hF hs hd S h1 hL hLi hx h𝔭 hv (k := k) (by omega)
    rw [eS, Nat.cast_mul] at eA
    have hnk : (nkCount h L 𝔭 k 1 : ℝ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, zero_div] at eA
      linarith
    have hB : alphaN h L 𝔭 1 ≠ 0 := by
      rw [eB]; exact div_ne_zero hnk (pow_ne_zero _ hN)
    refine ⟨hB, ?_⟩
    rw [eA, eB, ← hdim]
    have e1 : k * (finrank K V' + 1) ^ 2 =
        k * (2 * (finrank K V' + 1) - 1) + k * finrank K V' ^ 2 := by
      have : 2 * (finrank K V' + 1) - 1 = 2 * finrank K V' + 1 := by omega
      rw [this]; ring
    rw [e1, pow_add]
    field_simp <;> ring
  obtain ⟨hB, -⟩ := key _ le_rfl
  have hl : alphaL h' (S.cut L) 𝔭 = alphaL h L 𝔭 / alphaN h L 𝔭 1 :=
    (tendsto_const_nhds.congr'
      (Filter.eventually_atTop.2 ⟨_, fun k hk => ((key k hk).2).symm⟩)).limUnder_eq
  rw [hl]
  field_simp

end Two

end Formalism.HermitianLattices.Ext.L3.PinD
end
end

