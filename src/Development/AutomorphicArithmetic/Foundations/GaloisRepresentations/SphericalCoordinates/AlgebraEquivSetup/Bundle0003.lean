module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulL
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfMulL :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulL := by
  intro hAdm hAc hIff X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g₀
  set Φ : X → ℂ := fun y => T.tf r (y⁻¹ * g₀) with hΦ
  have hTy : T.IsTy Φ := by
    intro k hk g
    have hki : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [hΦ, mul_inv_rev, mul_assoc]
    rw [((hAdm X M T r hr).2 k⁻¹ hki (g⁻¹ * g₀)).1, smul_eq_mul]
    congr 2
    have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hki⟩ : T.J) = (⟨T.L.pr k, T.fact.2 _ hk⟩ : T.J)⁻¹ :=
      Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
  have key := hAc X M M' T L' Kw hF hAp t 1 ⟨fun g => by group, map_one _⟩ ℂ Φ hTy 1
  have lhs : conv T.K₀ (T.tf (L'.loc t)) (T.tf r) g₀ = Formalism.UG.hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp [conv, Formalism.UG.hAct, hΦ, smul_eq_mul]
  rw [lhs, key]
  have memKrK : ∀ y, y ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K → L'.pr y ∈ Kw := by
    intro y hy
    rw [DoubleCoset.mem_doubleCoset] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    simp only [map_mul, hr', mul_one]
    exact Kw.mul_mem (hF.2 a ha) (hF.2 b hb)
  simp only [hΦ, one_mul, smul_eq_mul]
  rw [finsum_eq_single _ ((L'.pr g₀ : M' ⧸ Kw)) ?_]
  · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr g₀)
    rw [hw]
    have h1 : (L'.pr g₀ * w ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw) ↔
        L'.pr g₀ ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨a, ha, b * (w : M')⁻¹, Kw.mul_mem hb (Kw.inv_mem w.2), ?_⟩
        calc L'.pr g₀ = L'.pr g₀ * w * (w : M')⁻¹ := by group
          _ = a * t * b * (w : M')⁻¹ := by rw [e]
          _ = a * t * (b * (w : M')⁻¹) := by group
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨a, ha, b * w, Kw.mul_mem hb w.2, by rw [e]; group⟩
    have h2 : ((L'.loc (L'.pr g₀ * w))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K) ↔
        (L'.loc (L'.pr g₀))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      have hwK : L'.loc w ∈ T.K := hF.1 w w.2
      have e : (L'.loc (L'.pr g₀ * w))⁻¹ * g₀ = (L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀) := by
        rw [map_mul, mul_inv_rev, mul_assoc]
      rw [e]
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e2⟩
        refine ⟨L'.loc w * a, T.K.mul_mem hwK ha, b, hb, ?_⟩
        calc (L'.loc (L'.pr g₀))⁻¹ * g₀
            = L'.loc w * ((L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀)) := by group
          _ = L'.loc w * (a * r * b) := by rw [e2]
          _ = L'.loc w * a * r * b := by group
      · rintro ⟨a, ha, b, hb, e2⟩
        exact ⟨(L'.loc w)⁻¹ * a, T.K.mul_mem (T.K.inv_mem hwK) ha, b, hb, by rw [e2]; group⟩
    have hprm : ∀ m, T.L.pr ((L'.loc m)⁻¹ * g₀) = T.L.pr g₀ := by
      intro m
      rw [map_mul, map_inv, hAp.1, inv_one, one_mul]
    simp only [TyLev.tf, dosetInd, Set.indicator_apply, Pi.one_apply, hprm, h1, h2,
      hIff X M' L' T.K Kw hF t r hr' g₀]
    split_ifs <;> simp_all
  · intro x hx
    have hy : (L'.loc (Quotient.out x))⁻¹ * g₀ ∉ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      intro hm
      apply hx
      have hh := memKrK _ hm
      rw [map_mul, map_inv, L'.pr_loc] at hh
      rw [← QuotientGroup.out_eq' x]
      exact QuotientGroup.eq.2 hh
    simp [TyLev.tf, dosetInd, Set.indicator_apply, hy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulR
section
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem tyFn_mul_of_mem {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a b : M)
    (ha : a ∈ J) : tyFn J ψ a * tyFn J ψ b = tyFn J ψ (a * b) := by
  unfold tyFn
  by_cases hb : b ∈ J
  · have hab : a * b ∈ J := J.mul_mem ha hb
    rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left hab]
    have e : (⟨a * b, hab⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul, mul_comm]
  · have hab : a * b ∉ J := fun h => hb (by simpa using J.mul_mem (J.inv_mem ha) h)
    rw [dite_eq_right hb, dite_eq_right hab, mul_zero]

private theorem mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw)
    (hC : ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔
      L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧
        (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (t : M') (r g y : X) (hr : L'.pr r = 1) (hy : y ∈ DoubleCoset.doubleCoset r (K : Set X) K)
    (hz : y⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K) :
    g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ∧
      y⁻¹ * ((L'.loc (L'.pr g))⁻¹ * g) ∈ K := by
  obtain ⟨hn, hk⟩ := (hC t 1 (map_one _) (y⁻¹ * g)).1 (by rw [mul_one]; exact hz)
  obtain ⟨ha, hy'⟩ := (hC 1 r hr y).1 (by rw [map_one, one_mul]; exact hy)
  have haK : L'.pr y ∈ Kw := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 ha
    rw [e, mul_one]
    exact Kw.mul_mem hu hv
  have hkK : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) ∈ K := by
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hk
    rw [e, mul_one]
    exact K.mul_mem hu hv
  generalize hkd : (L'.loc (L'.pr (y⁻¹ * g)))⁻¹ * (y⁻¹ * g) = k at hkK
  generalize hyd : (L'.loc (L'.pr y))⁻¹ * y = y' at hy'
  have hm : L'.pr g = L'.pr y * L'.pr (y⁻¹ * g) := by simp
  generalize had : L'.pr y = a at haK hm hyd
  generalize hnd : L'.pr (y⁻¹ * g) = n at hn hm hkd
  have hpy' : L'.pr y' = 1 := by
    rw [← hyd, map_mul, map_inv, L'.pr_loc, had, inv_mul_cancel]
  have hcomm : ∀ x, L'.loc x * y' = y' * L'.loc x := fun x => L'.comm x y' hpy'
  have hy1 : y = L'.loc a * y' := by rw [← hyd]; group
  have hg : g = L'.loc a * y' * (L'.loc n * k) := by
    rw [← hkd, ← hy1]; group
  have hy0 : (L'.loc (L'.pr g))⁻¹ * g = y' * k := by
    rw [hm, map_mul, hg, mul_assoc (L'.loc a), ← mul_assoc y', ← hcomm n]
    group
  refine ⟨(hC t r hr g).2 ⟨?_, ?_⟩, ?_⟩
  · rw [hm]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hn
    exact DoubleCoset.mem_doubleCoset.2 ⟨a * u, Kw.mul_mem haK hu, v, hv, by rw [e]; group⟩
  · rw [hy0]
    obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy'
    exact DoubleCoset.mem_doubleCoset.2 ⟨u, hu, v * k, K.mul_mem hv hkK, by rw [e]; group⟩
  · rw [hy0]
    have e : y⁻¹ * (y' * k) = (L'.loc a)⁻¹ * k := by
      calc y⁻¹ * (y' * k) = y'⁻¹ * ((L'.loc a)⁻¹ * y') * k := by rw [hy1]; group
        _ = y'⁻¹ * (y' * (L'.loc a)⁻¹) * k := by rw [← map_inv, hcomm]
        _ = (L'.loc a)⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (K.inv_mem (hF.1 a haK)) hkK

private theorem mem_doubleCosets_of_dosetInd_mul_ne_zero {X : Type} [Group X] (K : Subgroup X) (a b : ℂ) (r s x g : X)
    (h : a * dosetInd ℂ K r x * (b * dosetInd ℂ K s (x⁻¹ * g)) ≠ 0) :
    x ∈ DoubleCoset.doubleCoset r (K : Set X) K ∧
      x⁻¹ * g ∈ DoubleCoset.doubleCoset s (K : Set X) K := by
  constructor
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]
  · by_contra hn
    apply h
    simp [dosetInd, Set.indicator_apply, hn]

theorem UpperTheory.Gal.W2.Seed.pTfMulR :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulR := by
  intro hA hAdm hC X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g
  have hloc : T.L.pr (L'.loc t) = 1 := hAp.1 t
  have hinv : ∀ k ∈ T.K, ∀ x : X,
      T.tf r (x * k) * T.tf (L'.loc t) ((x * k)⁻¹ * g) = T.tf r x * T.tf (L'.loc t) (x⁻¹ * g) := by
    intro k hk x
    have h1 := ((hAdm X M T r hr).2 k hk x).2
    have h2 := ((hAdm X M T (L'.loc t) hloc).2 k⁻¹ (T.K.inv_mem hk) (x⁻¹ * g)).1
    rw [show (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) by group, h1, h2]
    have p1 : T.L.pr k ∈ T.J := T.fact.2 k hk
    have p2 : T.L.pr k⁻¹ ∈ T.J := T.fact.2 k⁻¹ (T.K.inv_mem hk)
    have e : (⟨T.L.pr k⁻¹, p2⟩ : T.J) = (⟨T.L.pr k, p1⟩ : T.J)⁻¹ := Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr k, p1⟩)
    linear_combination (T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) * hu
  have hsum := hA X ℂ T.K T.K₀ T.le T.idx (fun x => T.tf r x * T.tf (L'.loc t) (x⁻¹ * g)) hinv
  beta_reduce at hsum
  unfold conv
  rw [hsum]
  have hc : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := by exact_mod_cast T.idx
  by_cases hg : g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (T.K : Set X) T.K
  · obtain ⟨hm, hy0⟩ := (hC X M' L' T.K Kw hF t r hr' g).1 hg
    obtain ⟨y₀, hy0d⟩ : ∃ y₀, y₀ = (L'.loc (L'.pr g))⁻¹ * g := ⟨_, rfl⟩
    rw [← hy0d] at hy0
    have hp0 : L'.pr y₀ = 1 := by rw [hy0d, map_mul, map_inv, L'.pr_loc, inv_mul_cancel]
    have hcomm : L'.loc (L'.pr g) * y₀ = y₀ * L'.loc (L'.pr g) := L'.comm _ _ hp0
    have hg0 : g = L'.loc (L'.pr g) * y₀ := by rw [hy0d]; group
    have hz0 : y₀⁻¹ * g = L'.loc (L'.pr g) := by
      calc y₀⁻¹ * g = y₀⁻¹ * (L'.loc (L'.pr g) * y₀) := by rw [← hg0]
        _ = L'.loc (L'.pr g) := by rw [hcomm]; group
    have hzK : y₀⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t) (T.K : Set X) T.K := by
      rw [hz0]
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
      exact DoubleCoset.mem_doubleCoset.2
        ⟨L'.loc u, hF.1 u hu, L'.loc v, hF.1 v hv, by rw [e, map_mul, map_mul]⟩
    have hJ : T.L.pr y₀ ∈ T.J := by
      obtain ⟨u, hu, v, hv, e⟩ := DoubleCoset.mem_doubleCoset.1 hy0
      rw [e, map_mul, map_mul, hr, mul_one]
      exact T.J.mul_mem (T.fact.2 u hu) (T.fact.2 v hv)
    rw [finsum_eq_single _ (QuotientGroup.mk y₀ : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K y₀
      rw [hk, hinv k k.2 y₀]
      have hτ := tyFn_mul_of_mem T.J T.ψ _ (T.L.pr (y₀⁻¹ * g)) hJ
      rw [← map_mul, mul_inv_cancel_left] at hτ
      simp only [TyLev.tf, dosetInd, Set.indicator_of_mem hy0, Set.indicator_of_mem hzK,
        Set.indicator_of_mem hg, Pi.one_apply]
      rw [smul_eq_mul, ← hτ]
      field_simp
    · intro q hq
      by_contra hne
      apply hq
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      have hK := (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).2
      rw [← hy0d] at hK
      have h := (QuotientGroup.eq (s := T.K)).2 hK
      rwa [QuotientGroup.out_eq'] at h
  · rw [finsum_eq_zero_of_forall_eq_zero]
    · simp [TyLev.tf, dosetInd, hg]
    · intro q
      by_contra hne
      apply hg
      simp only [TyLev.tf] at hne
      have hm1 := mem_doubleCosets_of_dosetInd_mul_ne_zero T.K _ _ r (L'.loc t) q.out g hne
      exact (mem_doubleCoset_loc_mul_of_mem_of_pr_eq_one L' T.K Kw hF (hC X M' L' T.K Kw hF) t r g q.out hr' hm1.1 hm1.2).1
end

