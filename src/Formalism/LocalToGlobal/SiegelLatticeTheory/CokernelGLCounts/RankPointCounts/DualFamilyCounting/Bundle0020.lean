module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ProjectionIntoHolds
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RieszHermitianHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

def SummandLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    ∀ X : Submodule K V, ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ Λ : Submodule (𝓞 K) V,
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) →
      ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ Λ, π y ∈ Λ

def RieszH : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ f : V →ₗ[K] K, ∃ x : V, ∀ y, h x y = f y

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem coe_algebraMap_OF (t : 𝓞 F) :
    ((algebraMap (𝓞 F) (𝓞 K) t : 𝓞 K) : K) = algebraMap F K (t : F) := by
  change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]

theorem form_mem_locF_of (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}
    {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) {v y : V}
    (hv : v ∈ locF 𝔭 (dualIn h X L)) (hy : y ∈ locF 𝔭 L) : h y v ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have := h𝔭
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
  have H := (mem_dual_iff.1 huv.2) _ hty
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨t * u, fun hm => (h𝔭.mem_or_mem hm).elim ht hu, ?_⟩
  have hst : starRingEnd K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    have e := coe_algebraMap_OF (K := K) t
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = _ at e
    rw [e, starRingEnd_apply]
    exact (hF _).2 ⟨_, rfl⟩
  rw [form_ozmul_right, ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) y, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, hst, algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) (h y v)] at H
  rw [map_mul, mul_smul, smul_comm]
  exact H

theorem riesz_hermitian_holds : RieszH := by
  intro K V _ _ _ _ _ h _ hnd f
  classical
  let b := Module.finBasis K V
  let Φ : (Fin (finrank K V) → K) →ₗ[K] Module.Dual K V :=
    { toFun := fun c => ∑ i, c i • h (b i)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hΦ : ∀ c, h (∑ i, star (c i) • b i) = Φ c := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Φ, map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have hx : (∑ i, star (c i) • b i) = 0 := by
      apply hnd
      intro y
      rw [hΦ, hc]
      rfl
    funext i
    have := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i => star (c i)) hx i
    simpa using this
  have hsurj : Function.Surjective Φ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [Module.finrank_fin_fun, Subspace.dual_finrank_eq]
  obtain ⟨c, hc⟩ := hsurj f
  exact ⟨∑ i, star (c i) • b i, fun y => by rw [hΦ, hc]⟩

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} {u : 𝓞 F} (hu : u ∉ 𝔭) {v : V}
    (hv : algebraMap (𝓞 F) (𝓞 K) u • v ∈ X) : v ∈ X := by
  have hu0 : (u : F) ≠ 0 := by
    intro e
    apply hu
    have : u = 0 := RingOfIntegers.ext (by simpa using e)
    rw [this]
    exact 𝔭.zero_mem
  have hc0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) ≠ 0 := by
    have e := coe_algebraMap_OF (K := K) u
    change algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) = _ at e
    rw [e]
    exact (map_ne_zero _).2 hu0
  have h1 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u) • v ∈ X := by
    rw [algebraMap_smul]
    exact hv
  have := X.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) u))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

theorem projOnto_of (hS : SummandLoc) (hR : RieszH) : ProjOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd X Y hc hXY L hL 𝔭 h𝔭 Λ hΛ0 hΛd hΛX v hv
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨π, hπX, hπid, hπΛ⟩ := hS K F V X 𝔭 h𝔭 Λ hΛ0
  obtain ⟨x, hx⟩ := hR K V h hs hnd ((h v).comp π)
  have key : ∀ y, h y x = h (π y) v := by
    intro y
    rw [← hs.eq x y, hx y, LinearMap.comp_apply, hs.eq v (π y)]
  have hvX : v ∈ X := by
    obtain ⟨u, hu, huv⟩ := (LocalSpans.mem_locF 𝔭 _ v).1 hv
    exact mem_of_smul_mem hu huv.1
  have hxΛ : x ∈ Λ := by
    rw [← hΛd]
    show ∀ y ∈ Λ, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
    intro y hy
    rw [key]
    have : π y ∈ locF 𝔭 L := by
      rw [← hΛX]
      exact ⟨hπΛ y hy, hπX y⟩
    exact form_mem_locF_of hF hp hv this
  refine ⟨x, hxΛ, ?_⟩
  set w := X.projection Y hc x - v with hw
  have hwX : w ∈ X := X.sub_mem (Submodule.projection_apply_mem hc x) hvX
  have hw0 : w = 0 := by
    apply hnd
    intro z
    have ez := Submodule.projection_add_projection_eq_self hc z
    rw [← ez, map_add (f := _)]
    have h1 : h w (Y.projection X hc.symm z) = 0 := hXY w hwX _ (Submodule.projection_apply_mem _ z)
    have hzX : X.projection Y hc z ∈ X := Submodule.projection_apply_mem hc z
    have ex := Submodule.projection_add_projection_eq_self hc x
    have e3 : h (X.projection Y hc z) (X.projection Y hc x) = h (X.projection Y hc z) x := by
      conv_rhs => rw [← ex]
      rw [map_add (f := _), hXY _ hzX _ (Submodule.projection_apply_mem _ x), add_zero]
    have h2 : h (X.projection Y hc z) w = 0 := by
      rw [hw, map_sub, e3, key, hπid _ hzX, sub_self]
    rw [h1, add_zero, ← hs.eq (X.projection Y hc z) w, h2, map_zero]
  exact sub_eq_zero.mp hw0

end Formalism.L2.SG.Pf.G6
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SecondFlagXsLeBigBlock
section
noncomputable section

open NumberField Module IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')

def BB : Submodule (𝓞 D.host.E) (VS D).V := MMg D F0 F' ⊔ XS D F0 ⊔ XS D F'.fl

theorem natsmul_mem (n : ℕ) {N : Submodule (𝓞 D.host.E) (VS D).V} {x : (VS D).V} (hx : x ∈ N) :
    ((n : ℕ) : D.host.E) • x ∈ N := by
  have := N.smul_mem ((n : ℕ) : 𝓞 D.host.E) hx
  rwa [smulO, map_natCast] at this

theorem f'_eq (b : Fin (D.R.rS + 1)) : F'.fl.fvec b = F0.fvec b +
    ((gS D : ℕ) : D.host.E) • ((((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)) := by
  rw [smul_smul, mul_inv_cancel₀ (g_ne D), one_smul, add_sub_cancel]

theorem f_mem_MMg (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ MMg D F0 F' :=
  Submodule.subset_span (Or.inl ⟨i, rfl⟩)

theorem m_mem_MMg (b : Fin (D.R.rS + 1)) :
    (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b) ∈ MMg D F0 F' :=
  Submodule.subset_span (Or.inr ⟨b, rfl⟩)

theorem f'_mem_MMg (b : Fin (D.R.rS + 1)) : F'.fl.fvec b ∈ MMg D F0 F' := by
  rw [f'_eq D F0 F' b]
  exact Submodule.add_mem _ (f_mem_MMg D F0 F' b) (natsmul_mem D _ (m_mem_MMg D F0 F' b))

theorem e_mem_MMg (a : Fin D.R.rS) : F0.e a ∈ MMg D F0 F' := by
  rw [← fvec_cast]; exact f_mem_MMg D F0 F' _

theorem z_mem_MMg : F0.z ∈ MMg D F0 F' := by
  rw [← fvec_last]; exact f_mem_MMg D F0 F' _

theorem e'_mem_MMg (a : Fin D.R.rS) : F'.fl.e a ∈ MMg D F0 F' := by
  rw [← fvec_cast]; exact f'_mem_MMg D F0 F' _

theorem z'_mem_MMg : F'.fl.z ∈ MMg D F0 F' := by
  rw [← fvec_last]; exact f'_mem_MMg D F0 F' _

theorem MMg_le_BB : MMg D F0 F' ≤ BB D F0 F' := le_sup_left.trans le_sup_left

theorem flag_xs_le_big_block : XS D F0 ≤ BB D F0 F' := le_sup_right.trans le_sup_left

theorem second_flag_xs_le_big_block : XS D F'.fl ≤ BB D F0 F' := le_sup_right

theorem UUS_le_BB : UUS D F0 F' ≤ BB D F0 F' := by
  refine sup_le (sup_le (sup_le (flag_xs_le_big_block D F0 F') ?_) (second_flag_xs_le_big_block D F0 F')) ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact MMg_le_BB D F0 F' (z_mem_MMg D F0 F')
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact MMg_le_BB D F0 F' (z'_mem_MMg D F0 F')

theorem f_mem_U (i : Fin (D.R.rS + 1)) : F0.fvec i ∈ UPair D F0 F' :=
  Submodule.subset_span (Or.inl ⟨i, rfl⟩)

theorem f'_mem_U (i : Fin (D.R.rS + 1)) : F'.fl.fvec i ∈ UPair D F0 F' :=
  Submodule.subset_span (Or.inr ⟨i, rfl⟩)

theorem flag_x_le_pair_span : F0.X ≤ UPair D F0 F' := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [← fvec_cast]; exact f_mem_U D F0 F' _

theorem second_flag_x_le_pair_span : F'.fl.X ≤ UPair D F0 F' := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [← fvec_cast]; exact f'_mem_U D F0 F' _

theorem BB_le_U : BB D F0 F' ≤ (UPair D F0 F').restrictScalars (𝓞 D.host.E) := by
  refine sup_le (sup_le ?_ ((XS_le_X D F0).trans ?_)) ((XS_le_X D F'.fl).trans ?_)
  · rw [MMg, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · exact f_mem_U D F0 F' i
    · exact (UPair D F0 F').smul_mem _ ((UPair D F0 F').sub_mem (f'_mem_U D F0 F' b) (f_mem_U D F0 F' b))
  · exact flag_x_le_pair_span D F0 F'
  · exact second_flag_x_le_pair_span D F0 F'

theorem loc_BB_g (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') = Formalism.HermitianLatticesTheory.localization₂ P (MMg D F0 F') := by
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (sup_le (sup_le (Formalism.L2.SG.Pf.le_locP' _ _) ?_) ?_))
    (Formalism.L2.SG.Pf.localization_mono' (MMg_le_BB D F0 F'))
  · refine (XS_le_locP_e D F0 P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
    rintro _ ⟨a, rfl⟩; exact e_mem_MMg D F0 F' a
  · refine (XS_le_locP_e D F'.fl P hg).trans (Formalism.L2.SG.Pf.localization_mono' (Submodule.span_le.2 ?_))
    rintro _ ⟨a, rfl⟩; exact e'_mem_MMg D F0 F' a

theorem loc_BB_ng (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (hg : ((gS D : ℕ) : 𝓞 D.host.E) ∉ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (BB D F0 F') = Formalism.HermitianLatticesTheory.localization₂ P (UUS D F0 F') := by
  have hX0 : XS D F0 ≤ UUS D F0 F' := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hX1 : XS D F'.fl ≤ UUS D F0 F' := le_sup_right.trans le_sup_left
  have hz0 : F0.z ∈ UUS D F0 F' :=
    (show Submodule.span (𝓞 D.host.E) {F0.z} ≤ UUS D F0 F' from
      le_sup_right.trans (le_sup_left.trans le_sup_left)) (Submodule.mem_span_singleton_self _)
  have hz1 : F'.fl.z ∈ UUS D F0 F' :=
    (show Submodule.span (𝓞 D.host.E) {F'.fl.z} ≤ UUS D F0 F' from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  have hf0 : ∀ i, F0.fvec i ∈ UUS D F0 F' := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [fvec_last]; exact hz0
    | cast a => rw [fvec_cast]; exact hX0 (e_mem_XS D F0 a)
  have hf1 : ∀ i, F'.fl.fvec i ∈ UUS D F0 F' := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [fvec_last]; exact hz1
    | cast a => rw [fvec_cast]; exact hX1 (e_mem_XS D F'.fl a)
  refine le_antisymm (Formalism.L2.SG.Pf.locP_le_locP' (sup_le (sup_le ?_ ?_) ?_))
    (Formalism.L2.SG.Pf.localization_mono' (UUS_le_BB D F0 F'))
  · rw [MMg, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨b, rfl⟩)
    · exact Formalism.L2.SG.Pf.le_locP' _ _ (hf0 i)
    · refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hg, ?_⟩
      rw [smulO, map_natCast, smul_smul, mul_inv_cancel₀ (g_ne D), one_smul]
      exact Submodule.sub_mem _ (hf1 b) (hf0 b)
  · exact hX0.trans (Formalism.L2.SG.Pf.le_locP' _ _)
  · exact hX1.trans (Formalism.L2.SG.Pf.le_locP' _ _)

theorem MMof_eq : MMof D F0 F' = BB D F0 F' := by
  have key : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      (haveI := P.isPrime; if ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal then Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MMg D F0 F')
        else Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UUS D F0 F')) =
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BB D F0 F')) := by
    intro P
    have := P.isPrime
    split_ifs with hg
    · exact (loc_BB_g D F0 F' P.asIdeal hg).symm
    · exact (loc_BB_ng D F0 F' P.asIdeal hg).symm
  refine le_antisymm ?_ ?_
  · intro x hx
    apply Formalism.L2.SG.Pf.mem_of_forall_prime
    intro P
    have := P.isPrime
    have h1 := (Submodule.mem_iInf _).1 hx P
    rw [key P] at h1
    exact h1
  · refine le_iInf fun P => ?_
    have := P.isPrime
    rw [key P]
    exact Formalism.L2.SG.Pf.le_locP' _ _

theorem BB_latIn : IsLatIn (UPair D F0 F') (BB D F0 F') := by
  refine ⟨?_, le_antisymm (Submodule.span_le.2 (BB_le_U D F0 F')) ?_⟩
  · refine Submodule.FG.sup (Submodule.FG.sup ?_ (XS_fg D F0)) (XS_fg D F'.fl)
    exact Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))
  · rw [UPair, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Submodule.subset_span (MMg_le_BB D F0 F' (f_mem_MMg D F0 F' i))
    · exact Submodule.subset_span (MMg_le_BB D F0 F' (f'_mem_MMg D F0 F' i))

section Coord

variable {D F0 F'}
variable (hw : LinearIndependent D.host.E (Sum.elim F0.fvec F'.fl.fvec))
include hw

theorem coord_eq {α β α' β' : Fin (D.R.rS + 1) → D.host.E}
    (h : ∑ i, α i • F0.fvec i + ∑ j, β j • F'.fl.fvec j = ∑ i, α' i • F0.fvec i + ∑ j, β' j • F'.fl.fvec j) :
    α = α' ∧ β = β' := by
  have h0 := Fintype.linearIndependent_iff.1 hw (Sum.elim (α - α') (β - β')) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [sub_add_sub_comm, h, sub_self])
  exact ⟨funext fun i => sub_eq_zero.1 (h0 (Sum.inl i)), funext fun j => sub_eq_zero.1 (h0 (Sum.inr j))⟩

theorem indep4 {x1 x2 : (VS D).V} (h1 : x1 ∈ F0.X) (h2 : x2 ∈ F'.fl.X) {a a' : D.host.E}
    (h : x1 + a • F0.z + (x2 + a' • F'.fl.z) = 0) : x1 = 0 ∧ a = 0 ∧ x2 = 0 ∧ a' = 0 := by
  obtain ⟨c1, rfl⟩ := (mem_X_iff F0).1 h1
  obtain ⟨c2, rfl⟩ := (mem_X_iff F'.fl).1 h2
  rw [← sum_fvec, ← sum_fvec] at h
  obtain ⟨hα, hβ⟩ := coord_eq hw (α' := 0) (β' := 0) (by simpa using h)
  have hc1 : ∀ i, c1 i = 0 := fun i => by simpa using congrFun hα (Fin.castSucc i)
  have hc2 : ∀ i, c2 i = 0 := fun i => by simpa using congrFun hβ (Fin.castSucc i)
  refine ⟨by simp [hc1], by simpa using congrFun hα (Fin.last _), by simp [hc2],
    by simpa using congrFun hβ (Fin.last _)⟩

end Coord

theorem mmg_coord {v : (VS D).V} (hv : v ∈ MMg D F0 F') : ∃ o1 o2 : Fin (D.R.rS + 1) → 𝓞 D.host.E,
    v = ∑ i, (algebraMap (𝓞 D.host.E) D.host.E (o1 i) -
        algebraMap (𝓞 D.host.E) D.host.E (o2 i) * (((gS D : ℕ) : D.host.E))⁻¹) • F0.fvec i +
      ∑ j, (algebraMap (𝓞 D.host.E) D.host.E (o2 j) * (((gS D : ℕ) : D.host.E))⁻¹) • F'.fl.fvec j := by
  have hs : MMg D F0 F' = Submodule.span (𝓞 D.host.E) (Set.range (Sum.elim F0.fvec
      (fun b => (((gS D : ℕ) : D.host.E))⁻¹ • (F'.fl.fvec b - F0.fvec b)))) := by
    rw [Set.Sum.elim_range]; rfl
  rw [hs, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  refine ⟨fun i => c (Sum.inl i), fun j => c (Sum.inr j), ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, smulO, smul_sub, sub_smul, smul_smul, Finset.sum_sub_distrib]
  abel

theorem uus_coord {v : (VS D).V} (hv : v ∈ UUS D F0 F') : ∃ x1 ∈ XS D F0, ∃ o : 𝓞 D.host.E,
    ∃ x2 ∈ XS D F'.fl, ∃ o' : 𝓞 D.host.E,
      v = x1 + algebraMap (𝓞 D.host.E) D.host.E o • F0.z + (x2 + algebraMap (𝓞 D.host.E) D.host.E o' • F'.fl.z) := by
  obtain ⟨y, hy, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨y', hy', x2, hx2, rfl⟩ := Submodule.mem_sup.1 hy
  obtain ⟨x1, hx1, w1, hw1, rfl⟩ := Submodule.mem_sup.1 hy'
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw1
  obtain ⟨o', rfl⟩ := Submodule.mem_span_singleton.1 hw2
  refine ⟨x1, hx1, o, x2, hx2, o', ?_⟩
  rw [smulO, smulO]
  abel

end Formalism.L2.SG.Pf.Cnt.R3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SumFilterSmul
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sums {J : Type} [Fintype J] {b : J → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c d : J → K) :
    h (∑ i, c i • b i) (∑ i, d i • b i) = ∑ i, star (c i) * d i * h (b i) (b i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum h, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ₂, G3.form_sum_orth ho d i, starRingEnd_apply, smul_eq_mul, mul_assoc]

theorem sum_filter_smul {J : Type} [Fintype J] (p : J → Prop) [DecidablePred p] (x : J → K)
    (b : J → V) :
    ∑ i ∈ Finset.univ.filter p, x i • b i = ∑ i, (if p i then x i else 0) • b i := by
  simp only [Finset.sum_filter, ite_smul, zero_smul]

private theorem unit_mul_lemma {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) :
    IsUnitIn S (a * b) := by
  obtain ⟨ha0, haS, haI⟩ := ha
  obtain ⟨hb0, hbS, hbI⟩ := hb
  refine (⟨mul_ne_zero ha0 hb0, S.mul_mem haS hbS, ?_⟩ : a * b ≠ 0 ∧ a * b ∈ S ∧ (a * b)⁻¹ ∈ S)
  rw [mul_inv]
  exact S.mul_mem haI hbI

private theorem unit_add_dv_lemma_2 (hπ : IsUnif S π) {u d : K} (hu : IsUnitIn S u) (hd : Dv S π d) :
    IsUnitIn S (u + d) := by
  have hu' : u ≠ 0 ∧ u ∈ S ∧ u⁻¹ ∈ S := hu
  have hd' : d * π⁻¹ ∈ S := hd
  have e : u * (1 + π * (u⁻¹ * (d * π⁻¹))) = u + d := by
    rw [mul_add, mul_one, mul_left_comm u π, mul_inv_cancel_left₀ hu'.1, mul_left_comm π d,
      mul_inv_cancel₀ hπ.3, mul_one]
  rw [← e]
  exact unit_mul_lemma hu (hπ.5 _ (S.mul_mem hu'.2.2 hd'))

theorem rebaseAt_of (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hUP : ∀ (J : Type) [Fintype J] [DecidableEq J] (b : J → V) (e : J → ℕ) (i₀ : J),
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∀ x : J → K, (∀ i, x i ∈ S) →
      IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
        (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧
        (∀ k, e k ≠ e i₀ → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b)
    (hAB : ∀ (J : Type) [Fintype J] [DecidableEq J] (e : J → ℕ) (i₀ : J) (x : J → K),
      (∀ i, x i ∈ S) → ∀ T : Finset J, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : J → V,
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧ (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b) :
    G3.RebaseAt S π h := by
  intro J _ _ b e i₀ ho hu hmin X hX hXu
  obtain ⟨x, hxS, rfl⟩ := hX
  have hπ0 : π ≠ 0 := hπ.3
  have hterm : ∀ i, e i ≠ e i₀ →
      Dv S π (star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹) := by
    intro i hi
    have hlt : e i₀ < e i := lt_of_le_of_ne (hmin i) (Ne.symm hi)
    have hP : π ^ e i ≠ 0 := pow_ne_zero _ hπ0
    have hw : h (b i) (b i) * (π ^ e i)⁻¹ ∈ S := (show _ ∧ _ ∧ _ from hu i).2.1
    have hs : star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) ∈ S :=
      S.mul_mem (S.mul_mem (hS.1 _ (hxS i)) (hxS i)) hw
    have hk : Dv S π (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [← pow_sub₀ π hπ0 (hmin i)]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
      show π ^ (e i - e i₀) * π⁻¹ ∈ S
      rw [hm, show e i₀ + m + 1 - e i₀ = m + 1 by omega, pow_succ, mul_inv_cancel_right₀ hπ0]
      exact S.pow_mem hπ.1 m
    have e1 : star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹ =
        star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) * (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [mul_assoc _ (_ * _⁻¹), mul_assoc (h (b i) (b i)), inv_mul_cancel_left₀ hP, ← mul_assoc]
    rw [e1]
    exact Dv.mul_left hk hs
  have hD : Dv S π (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹ -
      h (∑ i, x i • b i) (∑ i, x i • b i) * (π ^ e i₀)⁻¹) := by
    rw [sum_filter_smul, form_sums ho, form_sums ho, ← sub_mul, ← Finset.sum_sub_distrib,
      Finset.sum_mul]
    refine Finset.sum_induction _ (Dv S π) (fun _ _ ha hb => Dv.add ha hb) ?_ fun i _ => ?_
    · show (0 : K) * π⁻¹ ∈ S
      rw [zero_mul]
      exact S.zero_mem
    · by_cases hi : e i = e i₀
      · rw [if_pos hi, sub_self, zero_mul]
        show (0 : K) * π⁻¹ ∈ S
        rw [zero_mul]
        exact S.zero_mem
      · rw [if_neg hi, star_zero, zero_mul, zero_mul, zero_sub, neg_mul]
        exact Dv.neg (hterm i hi)
  have hYu : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) := by
    have e2 : ∀ p q : K, p + (q - p) = q := fun p q => by ring
    have := unit_add_dv_lemma_2 hπ hXu hD
    rwa [e2] at this
  obtain ⟨c, hco, hcu, hci0, hck, hspan, hspanS⟩ := hUP J b e i₀ ho hu x hxS hYu
  have hi₀T : i₀ ∉ Finset.univ.filter (fun j => ¬ e j = e i₀) := fun hm =>
    (Finset.mem_filter.mp hm).2 rfl
  have hTlt : ∀ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), e i₀ < e j := fun j hj =>
    lt_of_le_of_ne (hmin j) (Ne.symm (Finset.mem_filter.mp hj).2)
  obtain ⟨c', hco', hcu', hc'i0, hc'k, hspan', hspanS'⟩ :=
    hAB J e i₀ x hxS _ hi₀T hTlt c hco hcu
  have hT' : ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • c j =
      ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • b j :=
    Finset.sum_congr rfl fun j hj => by rw [hck j (Finset.mem_filter.mp hj).2]
  refine ⟨c', hco', hcu', ?_, hspan'.trans hspan, fun v => (hspanS' v).trans (hspanS v)⟩
  rw [hc'i0, hci0, hT', Finset.sum_filter_add_sum_filter_not]

end

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

