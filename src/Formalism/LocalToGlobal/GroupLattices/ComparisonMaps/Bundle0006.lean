module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0005
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.YvRatOfValRat
public import Formalism.SharpRestriction.GrowthBounds.JointsLit

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsMain
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}


open Classical in
def gOf (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : Fin nV → GL (Fin (m + 1)) Qq :=
  if h : ∀ v, IsLattice W (Lt v) then Classical.choose (exists_tupOf W Lt h) else 1

theorem gOf_spec (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) (h : ∀ v, IsLattice W (Lt v)) : Lt = tupOf W (gOf Lt) := by
  unfold gOf
  rw [dite_eq_left h]
  exact Classical.choose_spec (exists_tupOf W Lt h)

def clsC (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (i : compL L p)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : ClassSet (HA sp) (KA L) :=
  clsG I hdet i (fun v => toF I hk v (gOf Lt v))

theorem clsC_eq (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (i : compL L p)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    clsC I hdet hk i Lt = Fib.mkC (HA sp) (KA L) (repP L p i * jQ I hdet hk (gOf Lt)) := rfl

theorem prP_repP (I : LocId L p nV W Qq) (hk : m + 1 = R.k) (i : compL L p) : prP I hk (repP L p i) = 1 := by
  funext v
  rw [prP_apply, repP_over L p i (I.plc v) (I.pl v).2, map_one, map_one]
  rfl

theorem act_eq_prP (I : LocId L p nV W Qq) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : Fin nV)
    (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y) :
    (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).act v γ =
      prP I hk (ratA sp γ.1) v := by
  rw [prP_ratA, MulEquiv.eq_symm_apply]
  exact levC_act sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y v γ

theorem orb_iff (I : LocId L p nV W Qq) (hk : m + 1 = R.k) (y : GA sp) (g g' : Fin nV → GL (Fin (m + 1)) Qq) :
    (∃ γ ∈ HA sp, y⁻¹ * γ * y ∈ KA' L p ∧ g'⁻¹ * (prP I hk γ * g) ∈ stabTup (nV := nV) (k := m + 1) (Qq := Qq) W) ↔
      ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _),
        tupOf W g' = fun v => gMap W (prP I hk (ratA sp γ.1) v) (tupOf W g v) := by
  have key : ∀ γ : GA sp, g'⁻¹ * (prP I hk γ * g) ∈ stabTup (nV := nV) (k := m + 1) (Qq := Qq) W ↔
      tupOf W g' = fun v => gMap W (prP I hk γ v) (tupOf W g v) := by
    intro γ
    rw [← tupOf_eq_iff, eq_comm]
    have : tupOf W (prP I hk γ * g) = fun v => gMap W (prP I hk γ v) (tupOf W g v) := by
      funext v
      exact gMap_mul W _ _ _
    rw [this]
  constructor
  · rintro ⟨γ, hγ, h1, h2⟩
    obtain ⟨γ0, rfl⟩ := exists_ratA γ hγ
    exact ⟨⟨γ0, (mem_gamC_iff y γ0).2 h1⟩, (key _).1 h2⟩
  · rintro ⟨γ, h⟩
    exact ⟨ratA sp γ.1, ratA_mem _, (mem_gamC_iff y γ.1).1 γ.2, (key _).2 h⟩

theorem clsC_tupOf (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (hH : HypAtP I) (i : compL L p)
    (g : Fin nV → GL (Fin (m + 1)) Qq) :
    clsC I hdet hk i (tupOf W g) = Fib.mkC (HA sp) (KA L) (repP L p i * jQ I hdet hk g) := by
  rw [clsC_eq]
  refine ((fibP I hdet hk hH).cls_iff (HA sp) (repP L p) (repP_mk L p) (prP_repP I hk) i i _ _ (repP_mk L p) (prP_repP I hk)).2
    ⟨rfl, 1, Subgroup.one_mem _, ?_, ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · show g⁻¹ * (prP I hk 1 * gOf (tupOf W g)) ∈ _
    rw [map_one, one_mul, ← tupOf_eq_iff]
    exact (gOf_spec (tupOf W g) (tupOf_lat W g)).symm

section Main

variable (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)


include hH in
theorem class_eq_iff_translate_level_zero (i i' : compL L p) (Lt Lt' : Fin nV → Submodule W (Fin (m + 1) → Qq))
    (h : ∀ v, IsLattice W (Lt v)) (h' : ∀ v, IsLattice W (Lt' v)) :
    clsC I hdet hk i Lt = clsC I hdet hk i' Lt' ↔
      i = i' ∧ ∃ γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (repP L p i : GL (Fin R.k) _),
        Lt' = fun v => gMap W (prP I hk (ratA sp γ.1) v) (Lt v) := by
  rw [clsC_eq, clsC_eq]
  refine ((fibP I hdet hk hH).cls_iff (HA sp) (repP L p) (repP_mk L p) (prP_repP I hk) i i' (gOf Lt) (gOf Lt') (repP_mk L p) (prP_repP I hk)).trans
    (and_congr_right fun _ => ?_)
  refine (orb_iff I hk (repP L p i) (gOf Lt) (gOf Lt')).trans (exists_congr fun γ => ?_)
  rw [← gOf_spec Lt' h', ← gOf_spec Lt h]

theorem level_action_lattice_eq (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ Lt =
      fun v => gMap W (prP I hk (ratA sp γ.1) v) (Lt v) := by
  funext v
  rw [← act_eq_prP I hS r lam0 dom hk ψ y v γ]
  rfl

end Main

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfWeak
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

section Local

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq] {k : ℕ}

theorem den_one (π : W) (hπ : Irreducible π) (x : Qq) :
    ∃ (n : ℕ) (c : W), algebraMap W Qq π ^ n * x = algebraMap W Qq c := by
  obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors W) x
  have hs0 : (s : W) ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ
  refine ⟨n, ((u⁻¹ : Wˣ) : W) * c, ?_⟩
  simp only at hs
  rw [hu, map_mul, map_pow] at hs
  have hu' : algebraMap W Qq (u : W) * algebraMap W Qq ((u⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul]
  linear_combination algebraMap W Qq ((u⁻¹ : Wˣ) : W) * hs - algebraMap W Qq π ^ n * x * hu'

theorem den_mat (π : W) (hπ : Irreducible π) (h : Matrix (Fin k) (Fin k) Qq) :
    ∃ (N : ℕ) (H : Matrix (Fin k) (Fin k) W), algebraMap W Qq π ^ N • h = H.map (algebraMap W Qq) := by
  choose nn cc hnc using fun i j => den_one π hπ (h i j)
  refine ⟨∑ i, ∑ j, nn i j, Matrix.of fun i j => π ^ (∑ i, ∑ j, nn i j - nn i j) * cc i j, ?_⟩
  ext i j
  have hle : nn i j ≤ ∑ i, ∑ j, nn i j :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (nn i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, nn i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ i))
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, ← hnc i j]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem colSpan_mul_le (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) :
    colSpan W (g * U.map (algebraMap W Qq)) ≤ colSpan W g := by
  unfold colSpan
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have h : (fun i => (g * U.map (algebraMap W Qq)) i c) = ∑ b, U b c • (fun i => g i b) := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun i => (g * U.map (algebraMap W Qq)) i c) ∈ Submodule.span W (Set.range fun c : Fin k => fun i => g i c)
  rw [h]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem colSpan_mul_unit (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) (hU : IsUnit U.det) :
    colSpan W (g * U.map (algebraMap W Qq)) = colSpan W g := by
  apply le_antisymm (colSpan_mul_le g U)
  have h := colSpan_mul_le (g * U.map (algebraMap W Qq)) U⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv U hU, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one] at h

theorem det_one_add_unit (π : W) (hπ : Irreducible π) (D : Matrix (Fin k) (Fin k) W) : IsUnit (1 + π • D).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hπ0 : IsLocalRing.residue W π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have h1 : (IsLocalRing.residue W).mapMatrix (1 + π • D) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hπ0, zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, Matrix.det_one]
  exact one_ne_zero

theorem approx_local (π : W) (hπ : Irreducible π) (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    ∃ N : ℕ, ∀ N', N ≤ N' → ∀ (A : Matrix (Fin k) (Fin k) Qq) (C : Matrix (Fin k) (Fin k) W),
      A = g + algebraMap W Qq π ^ N' • C.map (algebraMap W Qq) → colSpan W A = colSpan W g ∧ IsUnit A.det := by
  obtain ⟨N, H, hH⟩ := den_mat π hπ g⁻¹
  refine ⟨N + 1, fun N' hN A C hA => ?_⟩
  have hU : IsUnit (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := det_one_add_unit π hπ _
  have hAU : A = g * (1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq) := by
    rw [hA, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, map_pow, ← hH,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.one_mul, smul_smul, smul_smul]
    congr 2
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  refine ⟨by rw [hAU]; exact colSpan_mul_unit g _ hU, ?_⟩
  rw [hAU, Matrix.det_mul]
  refine hg.mul ?_
  have h2 : ((1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq)).det =
      algebraMap W Qq (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact hU.map _

end Local

variable {p : ℕ} (G : GAtP p) {E : Type} [Field E] (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)

def WeakApprox : Prop :=
  ∀ (x : ∀ v, G.P.Qq v) (N : ℕ), ∃ a : E, ∀ v, ∃ c : G.P.W v,
    iw v a = x v + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c

theorem ratTup_of_weak (h : WeakApprox G iw) : RatTup G iw := by
  intro L hL
  by_cases hne : Nonempty (Fin G.P.nV)
  swap
  · exact ⟨1, fun v => (hne ⟨v⟩).elim⟩
  choose g hg hLg using hL
  have := fun v => (G.P.setting v).frac_alt
  choose N hN using fun v => approx_local (p : G.P.W v) (G.P.setting v).p_unif (g v) (hg v)
  choose a c hac using fun x y => h (fun v => g v x y) (∑ v, N v)
  have key : ∀ v, colSpan (G.P.W v) ((Matrix.of a).map (iw v)) = colSpan (G.P.W v) (g v) ∧
      IsUnit ((Matrix.of a).map (iw v)).det := fun v =>
    hN v (∑ v, N v) (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
      ((Matrix.of a).map (iw v)) (fun x y => c x y v) (by
        ext x y
        simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_natCast]
        exact hac x y v)
  obtain ⟨v0⟩ := hne
  have hdet : IsUnit (Matrix.of a).det := by
    have h1 := (key v0).2
    have h2 : ((Matrix.of a).map (iw v0)).det = iw v0 (Matrix.of a).det := by
      rw [RingHom.map_det]; rfl
    rw [h2] at h1
    rw [isUnit_iff_ne_zero] at h1 ⊢
    intro h0
    exact h1 (by rw [h0, map_zero])
  exact ⟨Matrix.nonsingInvUnit (Matrix.of a) hdet, fun v => by rw [hLg v]; exact (key v).1.symm⟩

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescOfValRat
section
namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions

variable {D : D7} (c : LatCmp D)

theorem yvRat (h : ValRat c) : Formalism.MainNotions.G.Joints.Lit.YvRat c :=
  fun u w hg v => yvRat_of_valRat c h u w hg v

theorem npDesc_of_valRat {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (hv : c.VramDef Y) (h : ValRat c) : c.NPDesc X Y K :=
  Formalism.MainNotions.G.Joints.Lit.NPDesc_of c hT X Y K hv (yvRat c h)

end Formalism.L2.G.Cmp
end

