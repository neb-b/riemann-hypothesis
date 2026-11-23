module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.StatementLat

@[expose] public section

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.DualOrthSum
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

private theorem mem_dual_iff_hermitian_lattices {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem dualOrthSum : DualOrthSum := by
  intro R K V _ _ _ _ _ _ _ _ h V₁ V₂ hc h12 h21 L₁ L₂ hL₁ hL₂
  apply le_antisymm
  · intro x hx
    rw [mem_dual_iff_hermitian_lattices] at hx
    have htop : x ∈ V₁ ⊔ V₂ := by
      rw [hc.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp htop
    refine Submodule.mem_sup.mpr ⟨x₁, Submodule.mem_inf.mpr ⟨?_, hx₁⟩,
      x₂, Submodule.mem_inf.mpr ⟨?_, hx₂⟩, rfl⟩
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₂ = 0 := h12 y (hL₁ hy) x₂ hx₂
      have hm := hx y (Submodule.mem_sup_left hy)
      rwa [map_add, e, add_zero] at hm
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₁ = 0 := h21 y (hL₂ hy) x₁ hx₁
      have hm := hx y (Submodule.mem_sup_right hy)
      rwa [map_add, e, zero_add] at hm
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add (f := _), LinearMap.add_apply, h21 y₂ (hL₂ hy₂) x hxV, add_zero]
      exact hxd y₁ hy₁
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add (f := _), LinearMap.add_apply, h12 y₁ (hL₁ hy₁) x hxV, zero_add]
      exact hxd y₂ hy₂

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
section
namespace Formalism.HermitianLatticesTheory

theorem finIntermediate : FinIntermediate := by
  intro W _ P Q hPQ hfin

  let f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q) := fun M =>
    (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))
  haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) :=
    Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q))
      (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q)))
      SetLike.coe_injective
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM N hN hMN
  have key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q →
      (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q := by
    intro M hPM _
    simp only [f]
    rw [AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']
    exact sup_eq_left.mpr fun x hx =>
      AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))
  have h1 : M.addSubgroupOf Q = N.addSubgroupOf Q := by
    rw [← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]
  have h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M := by
    intro M hMQ
    rw [AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]
  rw [← h2 M hM.2, ← h2 N hN.2, h1]

end Formalism.HermitianLatticesTheory
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
section
noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusBasic_gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  rw [isomAct_mem_gmap]
  first
  | rfl
  | simp
  | exact Iff.rfl

theorem genusBasic_gmap_mul (g₁ g₂ : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (g₂ * g₁) L = gmap g₂ (gmap g₁ L) := by
  ext x
  simp only [isomAct_mem_gmap]
  rfl

theorem genusBasic_gmap_inv (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g⁻¹ (gmap g L) = L := by
  first
  | exact isomAct_gmap_symm g L
  | (ext x; simp only [isomAct_mem_gmap]; simp)

theorem genusBasic_mem_one_mul (x : K) (hx : x ∈ (1 : Submodule R K)) (r : R) :
    algebraMap R K r * x ∈ (1 : Submodule R K) := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ r hx

theorem genusBasic_hsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h v (r • w) = algebraMap R K r * h v w := by
  rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]

theorem genusBasic_hsmul_left (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h (r • v) w = algebraMap R K (locBasic_sigma hinj hstar r) * h v w := by
  rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    locBasic_sigma_spec, starRingEnd_apply]

theorem genusBasic_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨hx1, hx2⟩ := hx
    refine Submonoid.subset_closure (Set.mem_setOf.2 ⟨hx2 _ (locBasic_sigma_spec hinj hstar x), fun t ht => ?_⟩)
    have e : t = x := hinj (by rw [ht, locBasic_sigma_spec, star_star])
    rw [e]
    exact hx1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem genusBasic_hS (p : Ideal R) (hp : p.IsMaximal) (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by
  haveI := hp.isPrime
  exact locBasic_hcompl_not_mem p s hs

theorem genusBasic_lg {W : Type*} [AddCommGroup W] [Module R W] (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ loc (K := K) p L) : x ∈ L := locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx

theorem genusBasic_common (S : Submonoid R) (s : Finset V) (f : V → K)
    (hf : ∀ v ∈ s, ∃ u ∈ S, algebraMap R K u * f v ∈ (1 : Submodule R K)) :
    ∃ u ∈ S, ∀ v ∈ s, algebraMap R K u * f v ∈ (1 : Submodule R K) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    obtain ⟨w, hw, hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [map_mul, mul_assoc]
      exact genusBasic_mem_one_mul _ hwa u
    · rw [map_mul, mul_comm (algebraMap R K u), mul_assoc]
      exact genusBasic_mem_one_mul _ (hus v hv) w

theorem genusBasic_loc_dual (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by
  obtain ⟨gens, rfl⟩ := hL
  have hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K := K) p,
      algebraMap R K u * h v z ∈ (1 : Submodule R K) := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))
    exact ⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩
  obtain ⟨u, hu, hall⟩ := genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen
  refine locBasic_mem_locS.2 ⟨u, hu, ?_⟩
  rw [dualBasic_mem_dual]
  intro y hy
  rw [genusBasic_hsmul_right]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hall x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), LinearMap.add_apply, mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
    exact genusBasic_mem_one_mul _ hx _

theorem genusBasic_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V)
    (hLM : SameGenus h L M) : SameGenus h M L := by
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩

theorem genusBasic_int (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : IsIntegralLat h L) : IsIntegralLat h M := by
  intro x hx y hy
  apply genusBasic_lg (K := K) (1 : Submodule R K) (h x y)
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hx' : x ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hx
  have hy' : y ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hy
  rw [isomAct_mem_gmap] at hx' hy'
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.1 hx'
  obtain ⟨t, ht, hty⟩ := locBasic_mem_locS.1 hy'
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg (g.symm x) (g.symm y)
    simpa using e.symm
  refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t,
    Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  rw [Algebra.smul_def, map_mul]
  convert h1 using 1
  ring

theorem genusBasic_dual_le (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLfg : L.FG) (hLM : SameGenus h L M)
    (hL : IsUnimodular h L) : dual h M ≤ M := by
  intro z hz
  rw [dualBasic_mem_dual] at hz
  apply genusBasic_lg (K := K) M z
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  rw [← hgL, isomAct_mem_gmap]
  have hmem : g.symm z ∈ loc (K := K) p (dual h L) := by
    apply genusBasic_loc_dual hinj hstar h p L hLfg
    intro v hv
    have hgv : g v ∈ loc (K := K) p M := by
      rw [← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
      exact locBasic_le_locS _ _ hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 hgv
    have h1 := hz _ hsv
    rw [genusBasic_hsmul_left hinj hstar] at h1
    have hiso : h (g v) z = h v (g.symm z) := by
      have e := hg v (g.symm z)
      simpa using e
    refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s,
      genusBasic_sigma_mem hinj hstar p s hs, ?_⟩
    rw [Algebra.smul_def, ← hiso]
    exact h1
  rwa [show dual h L = L from hL] at hmem

end SlopeTestRemainingChoices

theorem genusBasic : GenusBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L := by
    intro L hL x hx y hy
    have hy' : y ∈ dual h L := by
      rw [show dual h L = L from hL]
      exact hy
    exact (dualBasic_mem_dual h L y).1 hy' x hx
  have hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L := by
    intro L hL y hy
    exact (dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy
  refine ⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩,
    fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
    obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
    exact ⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩
  · intro L g hg p hp
    refine ⟨g, hg, ?_⟩
    ext x
    simp only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]
  · intro L M hL hM hLM
    have hML := genusBasic_symm h L M hLM
    refine ⟨⟨fun hU => ?_, fun hU => ?_⟩,
      ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩
    · exact le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU)
        (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))
    · exact le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU)
        (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem isomOfTrace : IsomOfTrace := by
  intro K V _ _ _ _ _ h g hg
  show ∀ x y, h (g x) (g y) = h x y
  intro x y
  by_contra hne
  have hd : h (g x) (g y) - h x y ≠ 0 := sub_ne_zero.mpr hne
  have key := hg x ((h (g x) (g y) - h x y)⁻¹ • y)
  simp only [map_smul, smul_eq_mul] at key
  have h0 : Algebra.trace ℚ K ((h (g x) (g y) - h x y)⁻¹ * (h (g x) (g y) - h x y)) = 0 := by
    rw [mul_sub, map_sub, key, sub_self]
  rw [inv_mul_cancel₀ hd] at h0
  have h1 : Algebra.trace ℚ K (1 : K) = (Module.finrank ℚ K : ℚ) := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h1] at h0
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact absurd h0 (by exact_mod_cast hpos.ne')

end Formalism.HermitianLatticesTheory
end
end

-- bundled from Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct
section
noncomputable section

open nonZeroDivisors

namespace Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_mem_inv {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by
  unfold invIdeal
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]
  rfl

theorem neighbourConstruct_mem_span {P : Ideal R} {x z : V} :
    z ∈ Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ↔
      ∃ a ∈ invIdeal (K := K) P, z = a • x := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩
    | smul r y _ h1 =>
      obtain ⟨a, ha, rfl⟩ := h1
      refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
      rw [smul_assoc]
  · intro hz
    exact Submodule.subset_span hz

end Gen

section DedekindLFunctions

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_one_mem (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by
  have e := FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0
  have e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1 := by
    rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  have h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [e2]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hne : (P : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP0
  refine (mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1
  · rw [FractionalIdeal.coe_coeIdeal]; exact le_rfl
  · intro a ha
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have := (FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).mp this

theorem neighbourConstruct_key (P : Ideal R) (hP0 : P ≠ ⊥) (L : Submodule R V) (x : V)
    (H : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L) : x ∈ P • L := by
  have h1 := neighbourConstruct_one_mem (K := K) P hP0
  have : ((1 : K) • x) ∈ P • L := by
    refine Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_
    · intro m hm n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm
      rw [Algebra.linearMap_apply, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hp (H n hn)
    · intro a b ha hb
      rw [add_smul]; exact Submodule.add_mem _ ha hb
  simpa using this

end DedekindLFunctions

section Avoid

variable {R : Type*} [CommRing R]

end Avoid

section Main

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

end Main

end Formalism.HermitianLatticesTheory
end
end

