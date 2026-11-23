module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegenerateOnOrthCompl
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0013

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExtensionIdentityOfMemCompl
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def formOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : ↥X →ₗ⋆[K] ↥X →ₗ[K] K :=
  (h.comp X.subtype).compl₂ X.subtype

@[simp] theorem formOn_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x y : ↥X) :
    formOn h X x y = h x y := rfl

theorem formOn_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : Submodule K V) :
    (formOn h X).IsSymm :=
  ⟨fun x y => hs.eq (x : V) (y : V)⟩

def incl (X : Submodule K V) : ↥X →ₗ[𝓞 K] V := X.subtype.restrictScalars (𝓞 K)

theorem incl_injective (X : Submodule K V) : Function.Injective (incl X) := Subtype.val_injective

def push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : Submodule (𝓞 K) V := L.map (incl X)

def pull (X : Submodule K V) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) ↥X := L.comap (incl X)

theorem mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {v : V} :
    v ∈ push X L ↔ ∃ x ∈ L, (x : V) = v := Submodule.mem_map

theorem coe_mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {x : ↥X} :
    (x : V) ∈ push X L ↔ x ∈ L := by
  rw [mem_push]
  constructor
  · rintro ⟨y, hy, e⟩
    rwa [← Subtype.ext e]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem push_le (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : ∀ v ∈ push X L, v ∈ X := by
  rintro v ⟨x, -, rfl⟩
  exact x.2

theorem push_pull {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : ∀ v ∈ L, v ∈ X) :
    push X (pull X L) = L := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    exact ⟨⟨v, hL v hv⟩, hv, rfl⟩

theorem push_injective (X : Submodule K V) : Function.Injective (push X) :=
  Submodule.map_injective_of_injective (incl_injective X)

theorem algebraMap_ne_zero {𝔭 : Ideal (𝓞 F)} (_hp : 𝔭.IsPrime) {t : 𝓞 F} (ht : t ∉ 𝔭) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
  have ht0 : t ≠ 0 := fun e => ht (e ▸ 𝔭.zero_mem)
  have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  rw [e]
  exact (map_ne_zero (algebraMap F K)).mpr (by exact_mod_cast ht0)

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {t : 𝓞 F}
    (ht : t ∉ 𝔭) {v : V} (hv : algebraMap (𝓞 F) (𝓞 K) t • v ∈ X) : v ∈ X := by
  have hne := algebraMap_ne_zero (K := K) hp ht
  have e : v = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • v) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) v, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact X.smul_mem _ hv

theorem push_locF (X : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    push X (locF 𝔭 L) = locF 𝔭 (push X L) := by
  ext v
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff hp L x).1 hx
    exact ⟨t, ht, ⟨_, hx, (incl X).map_smul _ _⟩⟩
  · rintro ⟨t, ht, hy⟩
    have hv : v ∈ X := mem_of_smul_mem (K := K) hp ht (push_le X L _ hy)
    refine ⟨⟨v, hv⟩, (LocF.mem_locF_iff hp L _).2 ⟨t, ht, ?_⟩, rfl⟩
    rw [← coe_mem_push (X := X)]
    exact hy

theorem push_span (X : Submodule K V) (s : Set ↥X) :
    push X (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K) (((↑) : ↥X → V) '' s) :=
  Submodule.map_span (incl X) s

theorem isLatIn_push_iff_isLattice {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    IsLatIn X (push X L) ↔ Submodule.IsFullLattice K L := by
  have hspan : Submodule.span K ((push X L : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (L : Set ↥X)).map X.subtype := by
    rw [Submodule.map_span]
    congr 1
  constructor
  · rintro ⟨hfg, hsp⟩
    refine
      { toIsLattice := Submodule.IsLattice.of_fg K
          (Submodule.fg_of_fg_map_injective _ (incl_injective X) hfg)
        span_eq_top := ?_ }
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [← hspan, hsp, Submodule.map_subtype_top]
  · intro hL
    refine ⟨hL.toIsLattice.fg.map _, ?_⟩
    rw [hspan, hL.span_eq_top, Submodule.map_subtype_top]

theorem isIntegralLat_push {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (push X L) ↔ Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h X) L := by
  constructor
  · intro H x hx y hy
    exact H _ (coe_mem_push.mpr hx) _ (coe_mem_push.mpr hy)
  · rintro H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact H x hx y hy

theorem isJordanIn_top {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) ↥X}
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (H : IsJordanIn h X (push X L) 𝔭 b a) :
    IsJordanIn (formOn h X) ⊤ L 𝔭 (fun i => ⟨b (Fin.cast (finrank_top K ↥X) i), H.1 _⟩)
      (fun i => a (Fin.cast (finrank_top K ↥X) i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨fun _ => Submodule.mem_top, ?_, fun i j hij => h3 _ _ fun e => hij (Fin.cast_injective _ e),
    fun i => h4 _, fun i => h5 _⟩
  apply push_injective X
  rw [push_locF X hp, push_locF X hp, push_span]
  refine Eq.trans ?_ h2
  congr 2
  ext v
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨Fin.cast (finrank_top K ↥X).symm i, rfl⟩, ?_⟩
    rfl

section Ext

variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def extId (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm.trans
    (((LinearEquiv.refl K ↥U).prodCongr g).trans (Submodule.prodEquivOfIsCompl U (orthK h U) hc))

theorem extId_add (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u w : V}
    (hu : u ∈ U) (hw : w ∈ orthK h U) : extId hc g (u + w) = u + (g ⟨w, hw⟩ : V) := by
  have e1 : (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm (u + w) = (⟨u, hu⟩, ⟨w, hw⟩) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extId, LinearEquiv.trans_apply, e1, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']

theorem exists_add (hc : IsCompl U (orthK h U)) (v : V) :
    ∃ u ∈ U, ∃ w ∈ orthK h U, u + w = v := by
  have hv : v ∈ U ⊔ orthK h U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  exact Submodule.mem_sup.mp hv

theorem extId_of_mem_U (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u : V}
    (hu : u ∈ U) : extId hc g u = u := by
  have := extId_add hc g hu (orthK h U).zero_mem
  rw [add_zero] at this
  rw [this]
  simp

theorem extension_identity_of_mem_compl (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U))
    (w : ↥(orthK h U)) : extId hc g w = g w := by
  have := extId_add hc g U.zero_mem w.2
  rw [zero_add] at this
  rw [this, zero_add]

theorem extId_mem (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) : extId hc g ∈ isomFix h U := by
  refine ⟨fun v v' => ?_, fun u hu => extId_of_mem_U hc g hu⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  obtain ⟨u', hu', w', hw', rfl⟩ := exists_add hc v'
  rw [extId_add hc g hu hw, extId_add hc g hu' hw']
  have hg' : h (g ⟨w, hw⟩ : V) (g ⟨w', hw'⟩ : V) = h w w' := hg _ _
  have o1 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h x y = 0 := fun hx hy => mem_orthK.mp hy _ hx
  have o2 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h y x = 0 := fun {x y} hx hy => by
    rw [← hs.eq x y, o1 hx hy, map_zero]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hg', o1 hu (g ⟨w', hw'⟩).2, o2 hu' (g ⟨w, hw⟩).2, o1 hu hw', o2 hu' hw]

theorem map_orthK {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    (orthK h U).map (g : V →ₗ[K] V) = orthK h U := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact apply_mem_orthK hg hy
  · intro hx
    exact ⟨g.symm x, apply_mem_orthK ((isomFix h U).inv_mem hg) hx, g.apply_symm_apply x⟩

def restr {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U) :=
  g.ofSubmodules (orthK h U) (orthK h U) (map_orthK hg)

theorem restr_apply {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (w : ↥(orthK h U)) :
    (restr hg w : V) = g w :=
  LinearEquiv.ofSubmodules_apply _ _ _

theorem restr_mem {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    restr hg ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)) := fun x y => by
  simp only [formOn_apply, restr_apply]
  exact hg.1 x y

theorem extId_restr (hc : IsCompl U (orthK h U)) {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    extId hc (restr hg) = g := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  rw [extId_add hc _ hu hw, restr_apply, map_add (f := _), hg.2 u hu]

theorem restr_extId (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) :
    restr (extId_mem hs hc hg) = g := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact (restr_apply _ w).trans (extension_identity_of_mem_compl hc g w)

theorem gmap_push {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap g (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap (restr hg) L) := by
  unfold Formalism.HermitianLatticesTheory.gmap push
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

theorem gmap_extId_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)))
    (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap (extId hc g) (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap g L) := by
  rw [gmap_push (extId_mem hs hc hg), restr_extId hs hc hg]

end Ext

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibSEqSingleton
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma locF_inf_restrictScalars (X : Submodule K V) (Λ : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) :
    locF 𝔭 (Λ ⊓ X.restrictScalars (𝓞 K)) = locF 𝔭 Λ ⊓ X.restrictScalars (𝓞 K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine Submodule.mem_inf.mpr ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.1⟩, ?_⟩
    rw [← Formalism.L2.SG.Pf.G7.locF_subspace X hp]
    exact (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.2⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    exact (mem_locF_lemma 𝔭 _ x).mpr
      ⟨s, hs, Submodule.mem_inf.mpr ⟨hsx, (X.restrictScalars (𝓞 K)).smul_mem s hx2⟩⟩

theorem locF_mem_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {M T Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ)
    (hM : Λ ⊓ U.restrictScalars (𝓞 K) = M) (hT : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibS h U 𝔭 M T := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ = Λ := hu
  simp only [fibS, Set.mem_setOf_eq]
  refine ⟨⟨Λ, hΛ, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ.fg h𝔭.isPrime, hu']
  · rw [← hM, locF_inf_restrictScalars U Λ h𝔭.isPrime]
  · rw [← hT, locF_inf_restrictScalars (orthK h U) Λ h𝔭.isPrime]

theorem fibS_eq_singleton (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {M T Λ₀ : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hΛ₀ : Submodule.IsLattice K Λ₀) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (he : locF 𝔭 (M ⊔ T) = locF 𝔭 Λ₀) :
    fibS h U 𝔭 M T = {locF 𝔭 (M ⊔ T)} := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ₀ = Λ₀ := hu
  have hN : dualF h 𝔭 (locF 𝔭 (M ⊔ T)) = locF 𝔭 (M ⊔ T) := by
    rw [he, ← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ₀.fg h𝔭.isPrime, hu']
  have hMU : ∀ x ∈ M, x ∈ U := fun x hx => hM.2 ▸ Submodule.subset_span hx
  have hTW : ∀ x ∈ T, x ∈ orthK h U := fun x hx => hT.2 ▸ Submodule.subset_span hx
  have hcapU : locF 𝔭 (M ⊔ T) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M :=
    locF_sup_inf hUc hMU hTW h𝔭.isPrime
  have hcapW : locF 𝔭 (M ⊔ T) ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
    rw [sup_comm]; exact locF_sup_inf hUc.symm hTW hMU h𝔭.isPrime
  ext Λ
  simp only [fibS, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨Λ₁, hΛ₁, rfl⟩, hd, hcU, hcW⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ₁ := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
      obtain ⟨m, hm, t, ht, hmt⟩ := Submodule.mem_sup.mp hsx
      have hm' : m ∈ locF 𝔭 Λ₁ := by
        have hm1 : m ∈ locF 𝔭 M :=
          (mem_locF_lemma 𝔭 _ m).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcU] at hm1
        exact (Submodule.mem_inf.mp hm1).1
      have ht' : t ∈ locF 𝔭 Λ₁ := by
        have ht1 : t ∈ locF 𝔭 T :=
          (mem_locF_lemma 𝔭 _ t).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcW] at ht1
        exact (Submodule.mem_inf.mp ht1).1
      have hsx' : s • x ∈ locF 𝔭 Λ₁ := by rw [← hmt]; exact add_mem hm' ht'
      obtain ⟨s', hs', h'⟩ := (mem_locF_lemma 𝔭 _ _).mp hsx'
      exact (mem_locF_lemma 𝔭 _ x).mpr
        ⟨s' * s, Submonoid.mul_mem _ hs' hs, by rw [mul_smul]; exact h'⟩
    refine le_antisymm ?_ hle
    calc locF 𝔭 Λ₁ = dualF h 𝔭 (locF 𝔭 Λ₁) := hd.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
      _ = locF 𝔭 (M ⊔ T) := hN
  · rintro rfl
    exact ⟨⟨Λ₀, hΛ₀, he.symm⟩, hN, hcapU, hcapW⟩

theorem card_glue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M)
    (hΛ₀full : Submodule.IsFullLattice K Λ₀) {T : Submodule (𝓞 K) V}
    (hT : IsLatIn (orthK h U) T) :
    Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T := by
  classical
  have hN : Submodule.IsFullLattice K (M ⊔ T) := by
    refine { toIsLattice := isLattice_sup hUc hM hT, span_eq_top := ?_ }
    rw [eq_top_iff, ← hUc.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
      (Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right))
  obtain ⟨s, hs⟩ := exists_locF_eq (F := F) hN hΛ₀full
  have hsing : ∀ 𝔭 ∉ s, fibS h U 𝔭.1 M T = {locF 𝔭.1 (M ⊔ T)} := fun 𝔭 h𝔭 =>
    fibS_eq_singleton hF hUc hM hT hΛ₀.1 hΛ₀.2.1 𝔭.2 (hs 𝔭 h𝔭)
  have hone : ∀ 𝔭 ∉ s, fibP h U 𝔭.1 M T = 1 := by
    intro 𝔭 h𝔭
    rw [fibP_eq, hsing 𝔭 h𝔭]
    simp
  rw [tprod_eq_prod hone, ← Finset.prod_coe_sort s]
  simp only [fibP_eq]
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun Λ 𝔭 => ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibS hF Λ.2.1.1 Λ.2.1.2.1 Λ.2.1.2.2 Λ.2.2 𝔭.1.2⟩) ⟨?_, ?_⟩)
  · rintro ⟨Λ₁, h1⟩ ⟨Λ₂, h2⟩ he
    apply Subtype.ext
    show Λ₁ = Λ₂
    refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
    by_cases hps : (⟨𝔭, h𝔭⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) ∈ s
    · exact congrArg Subtype.val (congrFun he ⟨_, hps⟩)
    · have a1 := locF_mem_fibS hF h1.1.1 h1.1.2.1 h1.1.2.2 h1.2 h𝔭
      have a2 := locF_mem_fibS hF h2.1.1 h2.1.2.1 h2.1.2.2 h2.2 h𝔭
      rw [hsing _ hps, Set.mem_singleton_iff] at a1 a2
      exact a1.trans a2.symm
  · intro τ
    obtain ⟨Λ, ⟨hΛ, hin, hout⟩, -⟩ := exists_unique_patch hK hF hN s
      (fun 𝔭 => if hp : 𝔭 ∈ s then (τ ⟨𝔭, hp⟩).1 else ⊥) (by
        intro 𝔭 hp
        simp only [dif_pos hp]
        obtain ⟨⟨A, hA, e⟩, -, hU, hW⟩ := (τ ⟨𝔭, hp⟩).2
        refine ⟨by rw [← e, LocF.locF_idem], A, { toIsLattice := hA, span_eq_top := ?_ }, e⟩
        have hle : locF 𝔭.1 A ≤ (Submodule.span K (A : Set V)).restrictScalars (𝓞 K) := by
          rw [← G7.locF_subspace (Submodule.span K (A : Set V)) 𝔭.2.isPrime]
          exact LocF.locF_mono 𝔭.1 (fun _ hx => Submodule.subset_span hx)
        have hNle : M ⊔ T ≤ locF 𝔭.1 A := by
          rw [e]
          exact sup_le ((LocF.le_locF 𝔭.1 M).trans (hU ▸ inf_le_left))
            ((LocF.le_locF 𝔭.1 T).trans (hW ▸ inf_le_left))
        rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le]
        exact hNle.trans hle)
    have hfib : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 Λ ∈ fibS h U 𝔭.1 M T := by
      intro 𝔭
      by_cases hp : 𝔭 ∈ s
      · rw [hin 𝔭 hp, dif_pos hp]
        exact (τ ⟨𝔭, hp⟩).2
      · rw [hout 𝔭 hp, hsing 𝔭 hp]
        exact Set.mem_singleton _
    have hmem : Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T := by
      refine ⟨⟨hΛ, ?_, ?_⟩, ?_⟩
      · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
        refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [G7.locF_dual hF h hΛ.fg h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.2
    refine ⟨⟨Λ, hmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 Λ = (τ 𝔭).1
    rw [hin 𝔭.1 𝔭.2, dif_pos 𝔭.2]

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FieldDictionaryHolds
section
namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem field_dictionary_holds : HostDict := by
  intro D
  refine ⟨D.sp.cm.cmUnram, ?_, ?_⟩
  · intro a
    rw [D.sp.cm.fixed a, RingHom.mem_range, Set.mem_range]
  · intro x hx
    exact (D.sp.Y 0).nondeg.1 x hx

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanIffSpanS
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sum_orth {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c : ι → K) (i : ι) : h (b i) (∑ j, c j • b j) = c i * h (b i) (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [ho i j (Ne.symm hji), mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]

end

end Formalism.L2.SG.Pf.G3
end
end

