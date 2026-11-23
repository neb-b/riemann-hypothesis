module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClrHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumW
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2
open scoped Classical

namespace UpperTheory.Gal.W2.RootSumScaling

open UpperTheory.Gal.Schur

variable {F : Type} [Field F] [NumberField F]

end UpperTheory.Gal.W2.RootSumScaling

private theorem sch_comp_perm {n : ℕ} (lam : Fin n → ℕ) (g : Fin n → ℂ) (e : Equiv.Perm (Fin n)) :
    UpperTheory.Gal.Schur.sch lam (g ∘ e) = UpperTheory.Gal.Schur.sch lam g := by
  unfold UpperTheory.Gal.Schur.sch GroundTheory.Heights₂.Heights.RestTerms.schur
  rw [← MvPolynomial.aeval_rename, AlgHom.map_det]
  congr 2
  ext i j
  simp [GroundTheory.Heights₂.Heights.RestTerms.Schur.rename_completeSymmetric]

private theorem exists_perm_eq_comp_of_injective_of_surj {n : ℕ} (a b : Fin n → ℂ) (ha : Function.Injective a)
    (hsub : ∀ j, ∃ k, b k = a j) : ∃ e : Equiv.Perm (Fin n), a = b ∘ e := by
  choose f hf using hsub
  have hinj : Function.Injective f := by
    intro j j' h
    apply ha
    rw [← hf j, ← hf j', h]
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext j
  simp [hf]

private theorem detOne_eq_mul_prod_erase {n : ℕ} (x : ℂ) (v : Fin n → ℂ) (i : Fin n) :
    UpperTheory.Gal.Schur.detOne x v = (1 - x * v i) * ∏ k ∈ Finset.univ.erase i, (1 - x * v k) := by
  unfold UpperTheory.Gal.Schur.detOne
  exact (Finset.mul_prod_erase _ (fun k => 1 - x * v k) (Finset.mem_univ i)).symm

private theorem prod_map_erase_eq_prod_univ_erase {n : ℕ} (a : Fin n → ℂ) (ha : Function.Injective a) (i : Fin n)
    (f : ℂ → ℂ) :
    (Multiset.map f ((Multiset.map a Finset.univ.val).erase (a i))).prod =
      ∏ k ∈ Finset.univ.erase i, f (a k) := by
  rw [← Multiset.map_erase a ha, Multiset.map_map, ← Finset.erase_val]
  rfl

open UpperTheory.Gal.W2.RootSumScaling in
theorem UpperTheory.Gal.W2.rootSumW_of :
    UpperTheory.Gal.W2.RootSumW := by
  intro F _ _ n t₀ ε lam m hconj hlam
  obtain ⟨k₀, hk₀⟩ := UpperTheory.Gal.Schur.FibreSum_holds F ℂ n lam
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk₀ k hk 2 two_ne_zero ∅
  refine ⟨c, fun α hα s => ⟨(hc α hα s).1, (hc α hα s).2.1⟩, ?_⟩
  intro χ r hsep hr y
  set t₁ := ComplexEmbedding.conjugate t₀ with ht₁
  have hinj : ∀ τ, Function.Injective (r τ) := by
    intro τ a b hab
    have hnd : (Multiset.map (r τ) Finset.univ.val).Nodup := by
      rw [← hr τ]
      exact Polynomial.nodup_roots hsep.map
    exact Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  have hmap1 : χ.map t₁ = (χ.map t₀).map (starRingEnd ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  have hroot : ∀ j, ∃ k, r t₁ k = starRingEnd ℂ (r t₀ j) := by
    intro j
    have hmem : r t₀ j ∈ (χ.map t₀).roots := by
      change r t₀ j ∈ rts χ t₀
      rw [hr t₀]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    have hne : χ.map t₁ ≠ 0 := Polynomial.map_ne_zero hsep.ne_zero
    have hmem' : starRingEnd ℂ (r t₀ j) ∈ rts χ t₁ := by
      change _ ∈ (χ.map t₁).roots
      rw [Polynomial.mem_roots hne, hmap1]
      exact (Polynomial.isRoot_of_mem_roots hmem).map (starRingEnd ℂ)
    rw [hr t₁] at hmem'
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem'
    exact ⟨k, hk⟩
  obtain ⟨e, he⟩ := exists_perm_eq_comp_of_injective_of_surj (fun j => starRingEnd ℂ (r t₀ j)) (r t₁)
    (fun a b h => hinj t₀ ((starRingEnd ℂ).injective h)) hroot
  have h01 : t₀ ≠ t₁ := fun h => hconj h.symm
  set g : (F →+* ℂ) → Fin n → ℂ :=
    fun τ => if τ = t₁ then (fun j => starRingEnd ℂ (r t₀ j)) else r τ with hgdef
  have hg0 : g t₀ = r t₀ := by simp [hgdef, h01]
  have hg1 : g t₁ = fun j => starRingEnd ℂ (r t₀ j) := by simp [hgdef]
  have hgτ : ∀ τ, τ ≠ t₁ → g τ = r τ := fun τ h => by simp [hgdef, h]
  have hunit : ∀ i j : Fin n, j ≠ i → IsUnit (g t₀ j - g t₀ i) := by
    intro i j hji
    rw [hg0]
    exact (sub_ne_zero.mpr (fun h => hji (hinj t₀ h))).isUnit
  have key := (hsum ℂ t₀ t₁ h01 ε m g y).1 hlam hunit
  have hprod : ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ) =
      ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ) := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    by_cases h : τ = t₁
    · rw [h, hg1, he, sch_comp_perm]
    · rw [hgτ τ h]
  rw [← hprod, ← key]
  refine Finsupp.sum_congr fun α _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [hr t₀, Multiset.map_map]
  refine (Finset.sum_congr rfl fun i _ => ?_ :
    ∑ i, locW t₀ ε α y χ (r t₀ i) = _)
  have hB : ∀ f : ℂ → ℂ, (Multiset.map f ((rts χ t₀).erase (r t₀ i))).prod =
      ∏ k ∈ Finset.univ.erase i, f (r t₀ k) := fun f => by
    rw [hr t₀]
    exact prod_map_erase_eq_prod_univ_erase _ (hinj t₀) i f
  unfold locW
  rw [mul_comm, Finset.prod_comm]
  congr 1
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hx0 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)) = t₀ (α s : F) := rfl
    have hx1 : (algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)) = starRingEnd ℂ (t₀ (α s : F)) :=
      ComplexEmbedding.conjugate_coe_eq t₀ _
    have hA : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₀ (α s)))
        (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀) =
        (1 - t₀ (α s : F) * (y * r t₀ i)) * ∏ k ∈ Finset.univ.erase i, (1 - t₀ (α s : F) * r t₀ k) := by
      rw [detOne_eq_mul_prod_erase _ _ i, hx0]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₀ = UpperTheory.Gal.Schur.scaleAt y i (r t₀) := by
        simp [UpperTheory.Gal.Schur.twist, hg0]
      rw [htw]
      congr 1
      · simp [UpperTheory.Gal.Schur.scaleAt]
      · refine Finset.prod_congr rfl fun k hk => ?_
        simp [UpperTheory.Gal.Schur.scaleAt, Finset.ne_of_mem_erase hk]
    have hC : UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO t₁ (α s)))
        (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁) =
        (1 - starRingEnd ℂ (t₀ (α s : F)) * starRingEnd ℂ (r t₀ i)) *
          ∏ k ∈ Finset.univ.erase i, (1 - starRingEnd ℂ (t₀ (α s : F)) * (y * starRingEnd ℂ (r t₀ k))) := by
      rw [detOne_eq_mul_prod_erase _ _ i, hx1]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g t₁ =
          UpperTheory.Gal.Schur.scaleOff y i (fun j => starRingEnd ℂ (r t₀ j)) := by
        simp [UpperTheory.Gal.Schur.twist, hg1, h01.symm]
      rw [htw]
      congr 1
      · simp [UpperTheory.Gal.Schur.scaleOff]
      · refine Finset.prod_congr rfl fun k hk => ?_
        simp [UpperTheory.Gal.Schur.scaleOff, Finset.ne_of_mem_erase hk]
    have hE : ∀ τ ∈ (Finset.univ.erase t₀).erase t₁,
        (Multiset.map (fun z => 1 - τ (α s : F) * (y ^ ε τ * z)) (rts χ τ)).prod =
          UpperTheory.Gal.Schur.detOne ((algebraMap ℂ ℂ) (UpperTheory.Gal.Schur.resO τ (α s)))
            (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ) := by
      intro τ hτ
      have hτ1 := Finset.ne_of_mem_erase hτ
      have hτ0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)
      rw [hr τ, Multiset.map_map]
      have htw : UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ = fun k => y ^ ε τ * r τ k := by
        simp [UpperTheory.Gal.Schur.twist, hτ0, hτ1, hgτ τ hτ1]
      rw [htw]
      rfl
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t₀),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ t₁⟩),
      hA, hC, ← Finset.prod_congr rfl hE]
    unfold fibW
    rw [hB, hB]
    ring
  · unfold ballW
    rw [hB, hg0]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Ring.inverse_eq_inv', div_eq_mul_inv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootSumWOff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2
open scoped Classical

namespace UpperTheory.Gal.W2.RootOff

open UpperTheory.Gal.Schur

private theorem rts_conj {F : Type} [Field F] [NumberField F] (χ : F[X]) (τ : F →+* ℂ) :
    rts χ τ = (rts χ (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ) := by
  have h : rts χ (ComplexEmbedding.conjugate τ) = (rts χ τ).map (starRingEnd ℂ) := by
    unfold rts
    have e : χ.map (ComplexEmbedding.conjugate τ) = (χ.map τ).map (starRingEnd ℂ) := by
      rw [Polynomial.map_map]
      congr 1
    rw [e, (IsAlgClosed.splits (χ.map τ)).roots_map]
  rw [h, Multiset.map_map]
  conv_lhs => rw [← Multiset.map_id (rts χ τ)]
  congr 1
  funext z
  simp

private theorem ball_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ : F →+* ℂ) (χ : F[X])
    (g₀ g₁ : Fin n → ℂ) (y q : ℂ) (hr : rts χ t₀ = Finset.univ.val.map g₀)
    (hi : Function.Injective g₀) (h0 : ∀ k, g₀ k ≠ 0) (h1 : ∀ k, g₁ k ≠ 0)
    (hq : ∀ k, g₀ k * g₁ k = q) (i : Fin n) :
    ballW t₀ y χ (g₀ i) =
      ∏ j ∈ Finset.univ.erase i, ((g₁ i - y * g₁ j) * Ring.inverse (g₁ i - g₁ j)) := by
  have hqne : q ≠ 0 := by
    rw [← hq i]
    exact mul_ne_zero (h0 i) (h1 i)
  have hg : ∀ k, g₀ k = q / g₁ k := by
    intro k
    rw [← hq k]
    field_simp [h1 k]
  unfold ballW
  rw [hr, ← Multiset.map_erase _ hi, ← Finset.erase_val, Multiset.map_map, Finset.prod_map_val]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hne : g₁ i - g₁ j ≠ 0 := by
    intro h
    apply hji
    apply hi
    rw [hg, hg, sub_eq_zero.mp h]
  simp only [Function.comp, Ring.inverse_eq_inv']
  rw [hg j, hg i]
  have hj1 := h1 j
  have hi1 := h1 i
  have hden : q / g₁ j - q / g₁ i ≠ 0 := by
    rw [div_sub_div _ _ hj1 hi1]
    refine div_ne_zero ?_ (mul_ne_zero hj1 hi1)
    rw [mul_comm (g₁ j) q, ← mul_sub]
    exact mul_ne_zero hqne hne
  rw [div_eq_iff hden]
  field_simp

private theorem fib_eq {F : Type} [Field F] [NumberField F] {n : ℕ} (t₀ t₁ : F →+* ℂ)
    (ht₁ : t₁ = ComplexEmbedding.conjugate t₀) (hne : t₀ ≠ t₁) (ε : (F →+* ℂ) → ℕ) (χ : F[X])
    (g : (F →+* ℂ) → Fin n → ℂ) (y : ℂ) (x : F)
    (hr : ∀ τ, rts χ τ = Finset.univ.val.map (g τ))
    (hi : Function.Injective (g t₀)) (hc : ∀ k, g t₁ k = (starRingEnd ℂ) (g t₀ k)) (i : Fin n) :
    fibW t₀ ε x y χ (g t₀ i) = ∏ τ, detOne (τ x) (twist t₀ t₁ ε y i g τ) := by
  subst ht₁
  have herase : ∀ f : ℂ → ℂ, (Multiset.map f ((rts χ t₀).erase (g t₀ i))).prod
      = ∏ j ∈ Finset.univ.erase i, f (g t₀ j) := by
    intro f
    rw [hr, ← Multiset.map_erase _ hi, ← Finset.erase_val, Multiset.map_map, Finset.prod_map_val]
    rfl
  have hA : detOne (t₀ x) (twist t₀ (ComplexEmbedding.conjugate t₀) ε y i g t₀)
      = (1 - t₀ x * (y * g t₀ i)) * ∏ j ∈ Finset.univ.erase i, (1 - t₀ x * g t₀ j) := by
    unfold detOne twist scaleAt
    rw [if_pos rfl, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hB : detOne ((ComplexEmbedding.conjugate t₀) x) (twist t₀ (ComplexEmbedding.conjugate t₀) ε y i g (ComplexEmbedding.conjugate t₀))
      = (1 - (starRingEnd ℂ) (t₀ x) * (starRingEnd ℂ) (g t₀ i)) *
        ∏ j ∈ Finset.univ.erase i, (1 - (starRingEnd ℂ) (t₀ x) * (y * (starRingEnd ℂ) (g t₀ j))) := by
    unfold detOne twist scaleOff
    rw [if_neg (Ne.symm hne), if_pos rfl, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl,
      ComplexEmbedding.conjugate_coe_eq, hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj), hc]
  have hC : ∀ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀),
      detOne (τ x) (twist t₀ (ComplexEmbedding.conjugate t₀) ε y i g τ)
        = (Multiset.map (fun r => 1 - τ x * (y ^ ε τ * r)) (rts χ τ)).prod := by
    intro τ hτ
    have h1 := Finset.ne_of_mem_erase hτ
    have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hτ)
    unfold detOne twist
    rw [if_neg h2, if_neg h1, hr τ, Multiset.map_map, Finset.prod_map_val]
    rfl
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t₀),
    ← Finset.mul_prod_erase (Finset.univ.erase t₀) _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩),
    hA, hB, Finset.prod_congr rfl hC]
  unfold fibW
  rw [herase, herase]
  ring

end UpperTheory.Gal.W2.RootOff

theorem UpperTheory.Gal.W2.rootSumWOff_of :
    UpperTheory.Gal.W2.RootSumWOff := by
  intro F _ _ n t₀ ε lam m hconj hlam
  obtain ⟨k₀, hk₀⟩ := UpperTheory.Gal.Schur.FibreSum_holds F ℂ n lam
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨c, hcs, hc⟩ := hk₀ k hk 2 two_ne_zero ∅
  refine ⟨c, fun α hα s => ⟨(hcs α hα s).1, (hcs α hα s).2.1⟩, ?_⟩
  intro χ r hsep hr hc0 hqe y
  obtain ⟨q, hq⟩ := hqe
  set t₁ := ComplexEmbedding.conjugate t₀ with ht₁
  have hne : t₀ ≠ t₁ := Ne.symm hconj
  let g : (F →+* ℂ) → Fin n → ℂ := fun τ => if τ = t₀ then (fun k => starRingEnd ℂ (r t₁ k)) else r τ
  have hg0 : g t₀ = fun k => starRingEnd ℂ (r t₁ k) := if_pos rfl
  have hg1 : ∀ τ, τ ≠ t₀ → g τ = r τ := fun τ h => if_neg h
  have hrg : ∀ τ, rts χ τ = Multiset.map (g τ) Finset.univ.val := by
    intro τ
    by_cases h : τ = t₀
    · rw [h, hg0, RootOff.rts_conj χ t₀, hr, Multiset.map_map]
      rfl
    · rw [hg1 τ h]
      exact hr τ
  have hinj : ∀ τ, Function.Injective (g τ) := by
    intro τ a b hab
    have hnd : (rts χ τ).Nodup := Polynomial.nodup_roots (hsep.map)
    rw [hrg τ] at hnd
    exact Multiset.inj_on_of_nodup_map hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  have hmem : ∀ τ k, g τ k ∈ rts χ τ := by
    intro τ k
    rw [hrg τ]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ k)
  have hnz : ∀ τ k, g τ k ≠ 0 := by
    intro τ k h0
    have hm := hmem τ k
    unfold rts at hm
    rw [Polynomial.mem_roots', h0] at hm
    obtain ⟨_, hroot⟩ := hm
    apply hc0
    have hz := hroot.eq_zero
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map] at hz
    exact (map_eq_zero τ).mp hz
  have hcc : ∀ k, g t₁ k = starRingEnd ℂ (g t₀ k) := by
    intro k
    rw [hg1 t₁ hconj, hg0]
    simp
  have hq' : ∀ k, g t₀ k * g t₁ k = (q : ℂ) := by
    intro k
    rw [hcc k]
    exact hq _ (hmem t₀ k)
  have hunit : ∀ i j : Fin n, j ≠ i → IsUnit (g t₁ j - g t₁ i) :=
    fun i j h => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun e => h (hinj t₁ e)))
  have key := (hc ℂ t₀ t₁ hne ε m g y).2 hlam hunit
  have hsch : ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (r τ) = ∏ τ, UpperTheory.Gal.Schur.sch (lam τ) (g τ) := by
    apply Finset.prod_congr rfl
    intro τ _
    by_cases h : τ = t₀
    · have hl : lam τ = fun i => (fun _ => 0) i + m := by
        funext i
        simp [h, hlam]
      have e1 : (rts χ t₀).prod = ∏ k, r t₀ k := by
        rw [hr]
        exact Finset.prod_map_val _ _
      have e2 : (rts χ t₀).prod = ∏ k, g t₀ k := by
        rw [hrg]
        exact Finset.prod_map_val _ _
      rw [hl, (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (r τ)).2 _ m, (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (g τ)).2 _ m,
        (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (r τ)).1, (UpperTheory.Gal.Schur.SchurDet_holds ℂ n (g τ)).1, h, ← e1, ← e2]
    · rw [hg1 τ h]
  rw [hsch, ← key]
  apply Finsupp.sum_congr
  intro α _
  rw [smul_eq_mul]
  congr 1
  rw [hrg t₀, Multiset.map_map, Finset.sum_map_val]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp, locW]
  rw [RootOff.ball_eq t₀ χ (g t₀) (g t₁) y q (hrg t₀) (hinj t₀) (hnz t₀) (hnz t₁) hq' i]
  have hf : ∀ s, fibW t₀ ε (↑(α s)) y χ (g t₀ i)
      = ∏ τ, UpperTheory.Gal.Schur.detOne (τ ↑(α s)) (UpperTheory.Gal.Schur.twist t₀ t₁ ε y i g τ) :=
    fun s => RootOff.fib_eq t₀ t₁ rfl hne ε χ g y _ hrg (hinj t₀) hcc i
  rw [Finset.prod_congr rfl (fun s _ => hf s), Finset.prod_comm]
  exact mul_comm _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRootsFull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_mul_Sb {g : ℕ} {H Sb : Matrix (Fin g) (Fin g) ℂ} {ev : Fin g → ℂ}
    (h : H * Sb = Sb * Matrix.diagonal ev) (i : ℕ) :
    H ^ i * Sb = Sb * Matrix.diagonal (fun j => ev j ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [_root_.pow_succ, _root_.mul_assoc, h, ← _root_.mul_assoc, ih, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    simp only [_root_.pow_succ]

private theorem sum_mul_Sb {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {a : 𝓞 F →+* O} {H Sb : Matrix (Fin g) (Fin g) ℂ}
    {ty : Fin g → (F →+* ℂ)} {ev : Fin g → ℂ} (hD : IsDiag a ρ H Sb ty ev) (q : (𝓞 F)[X]) :
    (q.sum fun i b => ρ (a b) * H ^ i) * Sb =
      Sb * Matrix.diagonal (fun j => ((q.map (algebraMap (𝓞 F) F)).map (ty j)).eval (ev j)) := by
  obtain ⟨-, hc, hH⟩ := hD
  have key : ∀ (i : ℕ) (b : 𝓞 F), ρ (a b) * H ^ i * Sb =
      Sb * Matrix.diagonal (fun j => ty j (b : F) * ev j ^ i) := by
    intro i b
    rw [_root_.mul_assoc, pow_mul_Sb hH i, ← _root_.mul_assoc, hc b, _root_.mul_assoc,
      Matrix.diagonal_mul_diagonal]
  simp only [Polynomial.sum_def, Finset.sum_mul, key, ← Finset.mul_sum]
  congr 1
  ext k l
  simp only [Matrix.sum_apply, Matrix.diagonal_apply, Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  split_ifs with hkl
  · subst hkl
    rfl
  · simp

theorem UpperTheory.Gal.W2.rootsFull_of :
    UpperTheory.Gal.W2.TypeCount → UpperTheory.Gal.W2.PowSumRat → UpperTheory.Gal.W2.NewtonPoly → UpperTheory.Gal.W2.KillsMat → UpperTheory.Gal.W2.RootsFull := by
  intro hTC hPS hNP hKM F _ _ O _ bar g ρ a n t₀ ε hS D P₀ hP ga H hga Sb ty ev hD χ hχ hdeg τ
  have hcard : ∀ σ, (evFull ty ev σ).card = n :=
    fun σ => (hTC F O bar g ρ a n t₀ ε hS H Sb ty ev hD σ).2
  obtain ⟨ψ, hψm, hψd, hψ⟩ :=
    hNP F n (evFull ty ev) hcard (hPS F O bar g ρ a D P₀ hP ga H hga Sb ty ev hD)
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (𝓞 F)) ψ
  set q := IsLocalization.integerNormalization (nonZeroDivisors (𝓞 F)) ψ
  have hb' : q.map (algebraMap (𝓞 F) F) = Polynomial.C (algebraMap (𝓞 F) F (b : 𝓞 F)) * ψ := by
    rw [hb, Polynomial.C_mul', algebraMap_smul]
  have h0 : (fun j => ((q.map (algebraMap (𝓞 F) F)).map (ty j)).eval (ev j)) = 0 := by
    funext j
    have hmem : ev j ∈ evFull ty ev (ty j) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨j, by simp, rfl⟩))
    rw [hb', Polynomial.map_mul, Polynomial.eval_mul, hψ (ty j), Polynomial.eval_multiset_prod,
      Pi.zero_apply]
    apply mul_eq_zero_of_right
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.2 ⟨ev j, hmem, by simp⟩
  have h1 := sum_mul_Sb hD q
  rw [h0, show Matrix.diagonal (0 : Fin g → ℂ) = 0 from Matrix.diagonal_zero,
    Matrix.mul_zero] at h1
  have hu : IsUnit Sb.det := isUnit_iff_ne_zero.mpr hD.1
  have hsum : (q.sum fun i c => ρ (a c) * H ^ i) = 0 := by
    rw [← Matrix.mul_one (q.sum fun i c => ρ (a c) * H ^ i), ← Matrix.mul_nonsing_inv Sb hu,
      ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have hk := (hKM F O bar g ρ a D P₀ hP ga H hga q).2 hsum
  have hdvd : χ ∣ ψ := by
    have := (hχ.2 q).1 hk
    rw [hb'] at this
    have hne : algebraMap (𝓞 F) F (b : 𝓞 F) ≠ 0 :=
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbmem)
    exact (Polynomial.dvd_C_mul hne).1 this
  have heq : ψ = χ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hχ.1 hψm hdvd (by rw [hψd, hdeg])
  show (Polynomial.map τ χ).roots = _
  rw [← heq, hψ τ, Polynomial.roots_multiset_prod_X_sub_C]
end

