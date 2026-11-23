module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFiniteInjectiveMvPowerSeriesCompatibleSect
section
open IsLocalRing UpperTheory.V.Alg

private theorem finite_quotient_of_pow_le {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : ∀ s : S, ∃ a : A, s - algebraMap A S a ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (G : Set S), hF.sup (Submodule.fg_span G.finite_toSet), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨a, ha⟩ := h (c y)
      have : c y • y = a • y + y * (c y - algebraMap A S a) := by
        rw [Algebra.smul_def a, smul_eq_mul]; ring
      rw [this]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span hy)) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

private theorem injective_of_ringKrullDim_eq {A S : Type} [CommRing A] [IsDomain A] [CommRing S]
    [Algebra A S] [Module.Finite A S] {n : ℕ} (hA : ringKrullDim A = n) (hS : ringKrullDim S = n) :
    Function.Injective (algebraMap A S) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (A ⧸ Ideal.span {r}) S :=
    (Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A S) (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
      rw [map_mul, hr, zero_mul])).toAlgebra
  haveI : IsScalarTower A (A ⧸ Ideal.span {r}) S := .of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (A ⧸ Ideal.span {r}) S := Module.Finite.of_restrictScalars_finite A _ _
  have h1 : ringKrullDim S ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap (A ⧸ Ideal.span {r}) S))
      fun _ _ hpq => Ideal.IsIntegral.comap_lt_comap (R := A ⧸ Ideal.span {r}) hpq
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_of_ne_zero hr0)
    (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r))
  have h3 : ringKrullDim S + 1 ≤ ringKrullDim A := (add_le_add_left h1 1).trans h2
  rw [hA, hS] at h3
  norm_cast at h3
  omega

open MvPowerSeries GlobalTheory in
theorem UpperTheory.exists_finite_injective_mvPowerSeries_compatible_section :
    ∀ (O S : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsDomain S] [Algebra O S] [IsCO O S] (x : S →ₐ[O] O), ∃ (d : ℕ) (F : MvPowerSeries (Fin d) O →ₐ[O] S), Function.Injective F ∧ F.toRingHom.Finite ∧ ringKrullDim S = (d + 1 : ℕ) ∧ ∀ g, x (F g) = MvPowerSeries.constantCoeff g := by
  intro O S _ _ _ _ _ _ _ hS x
  have hc : IsAdicComplete (maximalIdeal S) S := IsCO.complete (O := O)
  have hl : IsLocalHom (algebraMap O S) := IsCO.isLocalHom
  have hn : IsNoetherianRing S := hS.toIsNoetherian
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hp.maximalIdeal_eq
  have hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S :=
    fun a ha h => ha (IsLocalHom.map_nonunit a h)
  have hpm : p ∈ maximalIdeal O := hm ▸ Ideal.mem_span_singleton_self p
  have hp0 : algebraMap O S p ≠ 0 := fun h => hp.ne_zero (by simpa using congrArg x h)
  have hx : ∀ s ∈ maximalIdeal S, x s ∈ maximalIdeal O := fun s hs => by
    rw [← res_eq_zero_iff O O, res_map, res_eq_zero_iff]
    exact hs
  obtain ⟨n, y, hy, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S _ hp0 (hloc p hpm)
  let z : Fin n → S := fun i => y i - algebraMap O S (x (y i))
  have hz : ∀ i, z i ∈ maximalIdeal S := fun i => sub_mem (hy i) (hloc _ (hx _ (hy i)))
  let A := MvPowerSeries (Fin n) O
  let φ : A →ₐ[O] S := mvEvalAdic O (maximalIdeal S) z hz
  have hφX : ∀ i, φ (X i) = z i := fun i => mvEvalAdic_X _ z hz i
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := NoZeroDivisors.to_isDomain _
  have hA : IsAdicComplete (maximalIdeal A) A := (co_mvps O O (Fin n)).complete
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => hφX j ▸ hz j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    have h7 := add_mem h4 (hloc _ h5)
    rwa [sub_add_cancel] at h7
  have hC : ∀ a : O, algebraMap A S (C a) = algebraMap O S a := fun a => mvEvalAdic_C _ z hz a
  have hCm : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ (maximalIdeal A).map (algebraMap A S) :=
    fun a ha => hC a ▸ Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simpa using ha))
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hCm p hpm
    · have h1 : z i ∈ (maximalIdeal A).map (algebraMap A S) := by
        rw [← hφX i]
        exact Ideal.mem_map_of_mem (algebraMap A S)
          (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
      have h2 := add_mem h1 (hCm _ (hx _ (hy i)))
      simpa [z] using h2
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, h⟩ := IsCO.res_surj (O := O) s
    exact ⟨C a, by rwa [hC]⟩
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  have hd' : ringKrullDim S = (n + 1 : ℕ) := by rw [hd]; norm_cast
  refine ⟨n, φ, injective_of_ringKrullDim_eq (A := A) (n := n + 1) ?_ hd', hfin, hd', fun g => ?_⟩
  · rw [FormalIsogeny.ringKrullDim_mvPowerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one,
      Nat.card_eq_fintype_card, Fintype.card_fin, add_comm]
    norm_cast
  · have h := algHom_sub_constantCoeff_mem (x.comp φ) (K := ⊥) (fun j => by
      simp [hφX, z]) g
    simpa [sub_eq_zero] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothComplA
section
open IsLocalRing

namespace UpperTheory.V.Loc

private theorem sc_seq {T : ℕ → Type} (r : ∀ N, T (N + 1) → T N → Prop) (t0 : T 0)
    (hs : ∀ N (a : T N), ∃ b : T (N + 1), r N b a) : ∃ F : ∀ N, T N, F 0 = t0 ∧ ∀ N, r N (F (N + 1)) (F N) := by
  choose s hs using hs
  exact ⟨fun N => Nat.rec t0 s N, rfl, fun N => hs N _⟩

private theorem sc_lim {O R A : Type} [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
    (m : Ideal A) [IsAdicComplete m A] (F : ∀ N : ℕ, R →ₐ[O] A ⧸ m ^ (N + 2))
    (hs : ∀ N a, Ideal.Quotient.factorPow m (by omega : N + 2 ≤ N + 1 + 2) (F (N + 1) a) = F N a) :
    ∃ φ : R →ₐ[O] A, ∀ N a, Ideal.Quotient.mk (m ^ (N + 2)) (φ a) = F N a := by
  have ha : StrictMono (fun n : ℕ => n + 2) := fun _ _ h => by simpa using h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : R →+* A, ∀ n a, Ideal.Quotient.mk (m ^ (n + 2)) (ψ a) = F n a :=
    ⟨IsAdicComplete.StrictMono.liftRingHom m ha (fun n => (F n).toRingHom) (fun {k} => RingHom.ext (hs k)),
      fun n a => IsAdicComplete.StrictMono.mk_liftRingHom m ha _ _ a⟩
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψ⟩
  refine sub_eq_zero.1 (IsHausdorff.haus (I := m) inferInstance _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (by omega : n ≤ n + 2) (Ideal.Quotient.eq.1 ?_)
  exact (hψ n _).trans ((F n).commutes c)

private theorem sc_chain {O R A : Type} [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
    (J : ℕ → Ideal A) (hJ : ∀ N, J (N + 1) ≤ J N) (hJ0 : ∀ N, J N ≤ J 0)
    (I : Ideal R) (f₀ : R →ₐ[O] A ⧸ J 0) (h₀ : I ≤ RingHom.ker f₀)
    (step : ∀ (N : ℕ) (f' : R →ₐ[O] A ⧸ J N), I ≤ RingHom.ker f' →
      (∀ a, Ideal.Quotient.factor (hJ0 N) (f' a) = f₀ a) →
      ∃ f : R →ₐ[O] A ⧸ J (N + 1), I ≤ RingHom.ker f ∧ ∀ a, Ideal.Quotient.factor (hJ N) (f a) = f' a) :
    ∃ F : ∀ N, R →ₐ[O] A ⧸ J N, F 0 = f₀ ∧ (∀ N, I ≤ RingHom.ker (F N)) ∧
      ∀ N a, Ideal.Quotient.factor (hJ N) (F (N + 1) a) = F N a := by
  obtain ⟨F, hF0, hF⟩ := sc_seq (T := fun N => {f : R →ₐ[O] A ⧸ J N // I ≤ RingHom.ker f ∧
      ∀ a, Ideal.Quotient.factor (hJ0 N) (f a) = f₀ a})
    (fun N f f' => ∀ a, Ideal.Quotient.factor (hJ N) (f.1 a) = f'.1 a)
    ⟨f₀, h₀, fun a => by
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f₀ a)
      rw [← hb, Ideal.Quotient.factor_mk]⟩
    (fun N f' => by
      obtain ⟨f, h1, h2⟩ := step N f'.1 f'.2.1 f'.2.2
      refine ⟨⟨f, h1, fun a => ?_⟩, h2⟩
      rw [← f'.2.2 a, ← h2 a]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (f a)
      rw [← hb, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk])
  exact ⟨fun N => (F N).1, congrArg Subtype.val hF0, fun N => (F N).2.1, hF⟩

theorem sc_tower {O R A : Type} [CommRing O] [CommRing R] [CommRing A] [Algebra O R] [Algebra O A]
    (m : Ideal A) [IsAdicComplete m A] (I : Ideal R) (f₀ : R →ₐ[O] A ⧸ m ^ (0 + 2)) (h₀ : I ≤ RingHom.ker f₀)
    (step : ∀ (N : ℕ) (f' : R →ₐ[O] A ⧸ m ^ (N + 2)), I ≤ RingHom.ker f' →
      (∀ a, Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 2 ≤ N + 2)) (f' a) = f₀ a) →
      ∃ f : R →ₐ[O] A ⧸ m ^ (N + 1 + 2), I ≤ RingHom.ker f ∧
        ∀ a, Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2)) (f a) = f' a) :
    ∃ φ : R →ₐ[O] A, I ≤ RingHom.ker φ ∧ ∀ a, Ideal.Quotient.mk (m ^ (0 + 2)) (φ a) = f₀ a := by
  obtain ⟨F, hF0, hI, hF⟩ := sc_chain (fun N => m ^ (N + 2)) (fun N => Ideal.pow_le_pow_right (by omega))
    (fun N => Ideal.pow_le_pow_right (by omega)) I f₀ h₀ step
  obtain ⟨φ, hφ⟩ := sc_lim m F hF
  refine ⟨φ, fun a haI => ?_, fun a => (hφ 0 a).trans (AlgHom.congr_fun hF0 a)⟩
  refine IsHausdorff.haus (I := m) inferInstance (φ a) fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  refine Ideal.pow_le_pow_right (by omega : n ≤ n + 2) (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
  exact (hφ n a).trans (hI n haI)

theorem sc_max (E : Type) [Field E] (n : ℕ) (g : MvPowerSeries (Fin n) E) :
    g ∈ maximalIdeal (MvPowerSeries (Fin n) E) ↔ MvPowerSeries.constantCoeff g = 0 := by
  rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

theorem sc_span (E : Type) [Field E] (n : ℕ) :
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) E)) = maximalIdeal _ := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun g hg => ?_
  · rintro _ ⟨i, rfl⟩
    exact (sc_max E n _).2 (by simp)
  · have := GlobalTheory.algHom_sub_constantCoeff_mem (AlgHom.id E (MvPowerSeries (Fin n) E))
      (K := Ideal.span (Set.range MvPowerSeries.X)) (fun j => Ideal.subset_span ⟨j, rfl⟩) g
    simpa [(sc_max E n g).1 hg] using this

theorem sc_first {O E R : Type} [CommRing O] [Field E] [Algebra O E] [CommRing R] [Algebra O R]
    (x : R →ₐ[O] O) (n : ℕ) (D : Fin n → (R →ₗ[O] E))
    (hD : ∀ i a b, D i (a * b) = algebraMap O E (x a) * D i b + algebraMap O E (x b) * D i a) :
    ∃ f : R →ₐ[O] MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ (0 + 2),
      ∀ a, f a = Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap O E (x a)) + ∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i) := by
  have h1 : ∀ i, D i 1 = 0 := fun i => by simpa using hD i 1 1
  let L : R →ₗ[O] MvPowerSeries (Fin n) E :=
    { toFun := fun a => MvPowerSeries.C (algebraMap O E (x a)) + ∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i
      map_add' := fun a b => by simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]; ring
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        simp only [smul_eq_mul, map_mul, Algebra.smul_def, mul_add, Finset.mul_sum, mul_assoc,
          MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] }
  have hm : ∀ a, ∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) :=
    fun a => (sc_max E n _).2 (by simp)
  refine ⟨AlgHom.ofLinearMap ((Ideal.Quotient.mkₐ O _).toLinearMap ∘ₗ L) ?_ fun a b => ?_, fun a => rfl⟩
  · simp [L, h1]
  · show Ideal.Quotient.mk _ (L (a * b)) = Ideal.Quotient.mk _ (L a) * Ideal.Quotient.mk _ (L b)
    rw [← map_mul, eq_comm, Ideal.Quotient.eq]
    have : L a * L b - L (a * b) = (∑ i, MvPowerSeries.C (D i a) * MvPowerSeries.X i) * (∑ i, MvPowerSeries.C (D i b) * MvPowerSeries.X i) := by
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hD, map_mul, map_add (f := _), add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [this, zero_add, pow_two]
    exact Ideal.mul_mem_mul (hm a) (hm b)

end UpperTheory.V.Loc
end

