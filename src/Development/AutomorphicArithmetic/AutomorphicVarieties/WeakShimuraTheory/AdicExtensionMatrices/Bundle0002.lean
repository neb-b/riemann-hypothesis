module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.GdotSelf
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

private def gdot (u v : ℤ × ℤ) : ℤ := u.1 * v.1 + u.2 * v.2

private theorem gdot_self (i j : Fin 4) (h : i ≠ j) : 0 < gdot (wt i j) (wt i j) := by
  revert i j; decide

private theorem gdot_neg (i j k l : Fin 4) (h : gdot (wt i j) (wt k l) < 0) :
    j = k ∨ l = i ∨ j = l.rev ∨ k.rev = i := by
  revert i j k l; decide

private theorem wt_add' (i j k : Fin 4) : wt i k = wt i j + wt j k := by
  simp [wt]

private theorem sgn_sq (i j : Fin 4) : (sgn i * sgn j) * (sgn i * sgn j) = 1 := by
  revert i j; decide

private theorem gdot_sum {α : Type} (f : α → ℤ × ℤ) (u : ℤ × ℤ) (L : List α) (h : ∀ b ∈ L, 0 ≤ gdot u (f b)) :
    0 ≤ gdot u (L.map f).sum := by
  induction L with
  | nil => simp [gdot]
  | cons b L ih =>
    have hb := h b List.mem_cons_self
    have hL := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have e : gdot u ((b :: L).map f).sum = gdot u (f b) + gdot u (L.map f).sum := by
      simp only [List.map_cons, List.sum_cons, gdot, Prod.fst_add, Prod.snd_add]
      ring
    rw [e]
    exact add_nonneg hb hL

variable {A : Type} [CommRing A] {𝓡 : Subring (M4 A)}

private theorem gflip (ha : ∀ x ∈ 𝓡, adj x ∈ 𝓡) {x : M4 A} (hx : x ∈ 𝓡) (i j : Fin 4) :
    ∃ x' ∈ 𝓡, x' j.rev i.rev = x i j := by
  refine ⟨(sgn j.rev * sgn i.rev) • adj x, zsmul_mem (ha x hx) _, ?_⟩
  rw [Matrix.smul_apply, adj_apply, Fin.rev_rev, Fin.rev_rev, smul_smul, sgn_sq, one_smul]

private theorem gcomp (h1 : ∀ i, Matrix.single i i 1 ∈ 𝓡) {x y : M4 A} (hx : x ∈ 𝓡) (hy : y ∈ 𝓡) (i j k : Fin 4) :
    ∃ z ∈ 𝓡, z i k = x i j * y j k := by
  refine ⟨x * Matrix.single j j 1 * y, mul_mem (mul_mem hx (h1 j)) hy, ?_⟩
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

private theorem gmerge (h1 : ∀ i, Matrix.single i i 1 ∈ 𝓡) (ha : ∀ x ∈ 𝓡, adj x ∈ 𝓡) {x y : M4 A} (hx : x ∈ 𝓡)
    (hy : y ∈ 𝓡) (i j k l : Fin 4) (h : gdot (wt i j) (wt k l) < 0) :
    ∃ z ∈ 𝓡, ∃ p q, wt p q = wt i j + wt k l ∧ z p q = x i j * y k l := by
  obtain hjk | hli | hjl | hki := gdot_neg i j k l h
  · subst hjk
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hx hy i j l
    exact ⟨z, hz, i, l, wt_add' i j l, hz'⟩
  · subst hli
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hy hx k l j
    exact ⟨z, hz, k, j, by rw [wt_add' k l j, add_comm], by rw [hz', mul_comm]⟩
  · subst hjl
    obtain ⟨y', hy', hy''⟩ := gflip ha hy k l
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hx hy' i l.rev k.rev
    exact ⟨z, hz, i, k.rev, by rw [wt_add' i l.rev k.rev, wt_rev], by rw [hz', hy'']⟩
  · subst hki
    obtain ⟨x', hx', hx''⟩ := gflip ha hx k.rev j
    rw [Fin.rev_rev] at hx''
    obtain ⟨z, hz, hz'⟩ := gcomp h1 hx' hy j.rev k l
    exact ⟨z, hz, j.rev, l, by rw [wt_add' j.rev k l, ← wt_rev k.rev j, Fin.rev_rev], by rw [hz', hx'']⟩

end UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxGma :
    ∀ {A : Type} [CommRing A] (E : Subring A) (𝓡 : Subring (M4 A)), (∀ i, Matrix.single i i 1 ∈ 𝓡) → (∀ x ∈ 𝓡, x.trace ∈ E) → (∀ x ∈ 𝓡, adj x ∈ 𝓡) → ∀ L : List (M4 A × Fin 4 × Fin 4), (∀ x ∈ L, x.1 ∈ 𝓡) → (L.map fun x => wt x.2.1 x.2.2).sum = 0 → (L.map fun x => x.1 x.2.1 x.2.2).prod ∈ E := by
  intro A _ E 𝓡 h1 htr ha L hL hsum
  have hdiag : ∀ x ∈ 𝓡, ∀ p, x p p ∈ E := by
    intro x hx p
    have h := htr _ (mul_mem (h1 p) hx)
    have e : (Matrix.single p p 1 * x : M4 A).trace = x p p := by
      simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
    rwa [e] at h
  suffices key : ∀ n (L : List (M4 A × Fin 4 × Fin 4)), L.length = n → (∀ x ∈ L, x.1 ∈ 𝓡) →
      (L.map fun x => wt x.2.1 x.2.2).sum = 0 → (L.map fun x => x.1 x.2.1 x.2.2).prod ∈ E from
    key _ L rfl hL hsum
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hn hL hsum
  cases L with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    exact E.one_mem
  | cons a rest =>
    obtain ⟨x, i, j⟩ := a
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hsum ⊢
    have hx : x ∈ 𝓡 := hL _ List.mem_cons_self
    have hrest : ∀ y ∈ rest, y.1 ∈ 𝓡 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hlen : rest.length < n := by
      simp at hn
      omega
    by_cases hij : i = j
    · subst hij
      have hs : (rest.map fun x => wt x.2.1 x.2.2).sum = 0 := by
        rw [(wt_eq_zero i i).2 rfl, zero_add] at hsum
        exact hsum
      exact mul_mem (hdiag x hx i) (ih _ hlen rest rfl hrest hs)
    · have hpos := UpperTheory.V.Ws.gdot_self i j hij
      have hneg : ∃ b ∈ rest, UpperTheory.V.Ws.gdot (wt i j) (wt b.2.1 b.2.2) < 0 := by
        by_contra hcon
        push_neg at hcon
        have h0 := UpperTheory.V.Ws.gdot_sum (fun b : M4 A × Fin 4 × Fin 4 => wt b.2.1 b.2.2) (wt i j) rest hcon
        have e : UpperTheory.V.Ws.gdot (wt i j) (wt i j + (rest.map fun b => wt b.2.1 b.2.2).sum) =
            UpperTheory.V.Ws.gdot (wt i j) (wt i j) + UpperTheory.V.Ws.gdot (wt i j) (rest.map fun b => wt b.2.1 b.2.2).sum := by
          simp only [UpperTheory.V.Ws.gdot, Prod.fst_add, Prod.snd_add]
          ring
        have e0 : UpperTheory.V.Ws.gdot (wt i j) 0 = 0 := by simp [UpperTheory.V.Ws.gdot]
        rw [hsum, e0] at e
        linarith
      obtain ⟨b, hb, hbneg⟩ := hneg
      obtain ⟨y, k, l⟩ := b
      have hy : y ∈ 𝓡 := hrest _ hb
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hb
      obtain ⟨z, hz, p, q, hw, hzv⟩ := UpperTheory.V.Ws.gmerge h1 ha hx hy i j k l hbneg
      have hlen' : ((z, p, q) :: (s ++ t)).length < n := by
        simp at hn ⊢
        omega
      have hL' : ∀ w ∈ ((z, p, q) :: (s ++ t)), w.1 ∈ 𝓡 := by
        intro w hw'
        simp only [List.mem_cons, List.mem_append] at hw'
        rcases hw' with rfl | hw' | hw'
        · exact hz
        · exact hrest w (by simp [hw'])
        · exact hrest w (by simp [hw'])
      have hsum' : (((z, p, q) :: (s ++ t)).map fun x => wt x.2.1 x.2.2).sum = 0 := by
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append] at hsum ⊢
        rw [hw]
        linear_combination hsum
      have := ih _ hlen' _ rfl hL' hsum'
      simp only [List.map_cons, List.map_append, List.prod_cons, List.prod_append] at this ⊢
      rw [hzv] at this
      convert this using 1
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurPart
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem laurPart_prod {S R' ι : Type} [CommRing S] [CommRing R'] (e : S →+* LaurentSeries R')
    (w : ι → ℤ) (z : ι → S) (h : ∀ s, ∃ y, e (z s) = HahnSeries.single (w s) y) (d : ι → ℕ) (t : Finset ι) :
    ∃ y, e (∏ i ∈ t, z i ^ d i) = HahnSeries.single (∑ i ∈ t, d i • w i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a t ha ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨u, hu⟩ := h a
    refine ⟨u ^ d a * y, ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, map_pow, hy, hu, HahnSeries.single_pow,
      HahnSeries.single_mul_single]

theorem UpperTheory.V.Ws.sxLaurPart :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur (Λ := Λ) c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y) → ∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ S _ _ _ c e hL τ F hF j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (F.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal S := fun s => by
    show F (W.z s) ∈ maximalIdeal S
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hW s
  refine ⟨(e (F (W.π g))).coeff (τ j), ?_⟩
  ext n
  show (e (F (W.π g))).coeff n = _
  by_cases hn : n = τ j
  · subst hn
    rw [HahnSeries.coeff_single_same]
  rw [HahnSeries.coeff_single_of_ne hn]
  obtain ⟨M, hM⟩ := hL.small n
  have h1 := hM _ (GlobalTheory.algHom_sub_aeval_truncTotal_mem (F.comp W.π) hm M g)
  rw [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, hg d hne, ite_self]
  obtain ⟨y, hy⟩ := laurPart_prod e (fun s => τ (W.wt s)) (fun s => F (W.z s)) hF d d.support
  have hs : (∑ i ∈ d.support, d i • τ (W.wt i)) = τ j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hs] at hy
  rw [map_mul, hL.alg]
  erw [hy]
  rw [HahnSeries.single_mul_single, zero_add, HahnSeries.coeff_single_of_ne hn]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearMap
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R} (f : R →ₐ[Λ] R'), Φ.Near a τ D → Φ.Near a τ (D.map (f : R →+* R')) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ R' _ _ _ τ D f hD
  have hr : ∀ g i j, (D.map (f : R →+* R')).r g i j = f (D.r g i j) := by
    intro g i j
    simp [RD.map, mapRep]
  have hψ : ∀ v i s, (D.map (f : R →+* R')).ψ v i s = f (D.ψ v i s) := by
    intro v i s
    simp [RD.map]
  have hm : maximalIdeal R ≤ Ideal.comap (f : R →+* R') (maximalIdeal R') := by
    intro x hx
    rw [Ideal.mem_comap]
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ R', res_map, res_eq_zero_iff]
    exact hx
  have hadj : ∀ X : M4 R, adj ((f : R →+* R').mapMatrix X) = (f : R →+* R').mapMatrix (adj X) := by
    intro X
    ext i j
    simp [adj_apply, map_zsmul]
  have hrm : ∀ g, (D.map (f : R →+* R')).r g = (f : R →+* R').mapMatrix (D.r g) := by
    intro g
    ext i j
    rw [hr]
    simp
  refine ⟨⟨fun g => ?_, fun g hg => ?_, ?_⟩, fun i j => ?_, fun v i => ?_, fun g i => ?_,
    fun g i j hij hτ => ?_, fun v i s => ?_⟩
  · have hX : adj (D.r g) * D.r g = (algebraMap Λ R) (a ↑(Φ.ν g)) • 1 := hD.rep.mult g
    have h := congrArg (f : R →+* R').mapMatrix hX
    rw [map_mul, ← hadj, ← hrm] at h
    show adj ((D.map (f : R →+* R')).r g) * (D.map (f : R →+* R')).r g =
      ((algebraMap Λ R').comp a) ↑(Φ.ν g) • 1
    rw [h]
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  · rw [hrm, hD.rep.kill g hg, map_one]
  · intro i j hij
    rw [hrm]
    simp [hD.rep.nrm hij]
  · simpa [hr] using adicCont_map (f : R →+* R') hm (hD.cont i j)
  · simpa [hψ] using adicCont_map (f : R →+* R') hm (hD.contψ v i)
  · rw [hr, res_map]
    exact hD.diag g i
  · rw [hr]
    exact hm (hD.off g i j hij hτ)
  · rw [hψ, res_map]
    exact hD.redψ v i s
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearOfAdjoin
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem near_of_adjoin {P L : Type} [CommRing P] [CommRing L] [Algebra P L] (G : Set L)
    (hG : ∀ g ∈ G, IsNilpotent g) (x : L) (hx : x ∈ Algebra.adjoin P G) :
    ∃ p : P, IsNilpotent (x - algebraMap P L p) :=
  _root_.UpperTheory.Reformulated.B.Qg2.near_of_adjoin G hG x hx

private theorem unit_of_near {S : Type} [CommRing S] {x u : S} (h : IsNilpotent (x - u)) (hu : IsUnit u) :
    IsUnit x := by
  have := h.isUnit_add_right_of_commute hu (Commute.all _ _)
  simpa using this

private theorem local_of_near {P S : Type} [CommRing P] [IsLocalRing P] [CommRing S] [Nontrivial S] [Algebra P S]
    (h : ∀ x : S, ∃ p : P, IsNilpotent (x - algebraMap P S p)) : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨p, hp⟩ := h x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p with hu | hu
  · exact Or.inl (unit_of_near hp (hu.map _))
  · refine Or.inr (unit_of_near (u := algebraMap P S (1 - p)) ?_ (hu.map _))
    have := hp.neg
    convert this using 1
    rw [map_sub, map_one]; ring

private theorem nil_mem_max {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsNilpotent x) :
    x ∈ maximalIdeal S := fun hu => by
  obtain ⟨n, hn⟩ := h
  exact not_isUnit_zero (hn ▸ hu.pow n)

private theorem bound_fin {R : Type} [CommRing R] (S : Subalgebra (PowerSeries R) (LaurentSeries R))
    [Module.Finite (PowerSeries R) S] :
    ∃ N : ℕ, ∀ y ∈ S, ∃ q : PowerSeries R,
      algebraMap (PowerSeries R) (LaurentSeries R) q = (PowerSeries.X : PowerSeries R) ^ N • y := by
  have hfg : S.toSubmodule.FG := Module.Finite.iff_fg.1 ‹_›
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨⟨b, N, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) t
  refine ⟨N, fun y hy => ?_⟩
  have hy' : y ∈ Submodule.span (PowerSeries R) (t : Set (LaurentSeries R)) := by
    rw [ht]; exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem g hg => exact hb g hg
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by rw [map_add (f := _), hp, hq, smul_add]⟩
  | smul r a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨r * p, by rw [map_mul, hp, ← Algebra.smul_def, smul_comm]⟩

private theorem alg_monomial {R : Type} [CommRing R] (n : ℕ) (x : R) :
    algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.C x * PowerSeries.X ^ n)
      = HahnSeries.single (n : ℤ) x := by
  show HahnSeries.ofPowerSeries ℤ R _ = _
  rw [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

theorem UpperTheory.V.Ws.sxLaur :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], IsNilpotent (maximalIdeal R) → ∀ c : ℕ, ∃ (S : Type) (_ : CommRing S) (_ : Algebra Λ S) (_ : IsCO Λ S) (e : S →+* LaurentSeries R), Laur (Λ := Λ) c e := by
  intro Λ _ _ R _ _ hR hnil c
  haveI hP : IsCO Λ (PowerSeries R) := co_mvps Λ R Unit
  have hnilx : ∀ x ∈ maximalIdeal R, IsNilpotent x := fun x hx => by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    have := Ideal.pow_mem_pow hx k
    rw [hk] at this
    simpa using this
  have hnils : ∀ (n : ℤ), ∀ x ∈ maximalIdeal R, IsNilpotent (HahnSeries.single n x : LaurentSeries R) :=
    fun n x hx => by
      obtain ⟨k, hk⟩ := hnilx x hx
      exact ⟨k, by rw [HahnSeries.single_pow, hk, map_zero]⟩
  obtain ⟨s, hs⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  let G : Set (LaurentSeries R) := (fun x => HahnSeries.single (-(c : ℤ)) x) '' (s : Set R)
  have hGfin : G.Finite := s.finite_toSet.image _
  have hG : ∀ g ∈ G, IsNilpotent g := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnils _ x (hs ▸ Ideal.subset_span hx)
  let S := Algebra.adjoin (PowerSeries R) G
  haveI hfin : Module.Finite (PowerSeries R) S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hGfin fun g hg => by
      obtain ⟨k, hk⟩ := hG g hg
      exact ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
  have hnear : ∀ x : S, ∃ p : PowerSeries R, IsNilpotent (x - algebraMap _ S p) := fun x => by
    obtain ⟨p, k, hk⟩ := near_of_adjoin G hG x.1 x.2
    exact ⟨p, k, Subtype.ext hk⟩
  haveI : IsLocalRing S := local_of_near hnear
  letI : Algebra Λ S := ((algebraMap (PowerSeries R) S).comp (algebraMap Λ (PowerSeries R))).toAlgebra
  haveI : IsScalarTower Λ (PowerSeries R) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomap : (maximalIdeal S).comap (algebraMap (PowerSeries R) S) = maximalIdeal (PowerSeries R) :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal S))
  have hin : ∀ p ∈ maximalIdeal (PowerSeries R), algebraMap _ S p ∈ maximalIdeal S := fun p hp => by
    rw [← hcomap] at hp; exact hp
  haveI hS : IsCO Λ S := co_finite Λ (PowerSeries R) S fun x => by
    obtain ⟨p, hp⟩ := hnear x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) p
    refine ⟨a, ?_⟩
    have := (maximalIdeal S).add_mem (nil_mem_max hp) (hin _ ha)
    convert this using 1
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; ring
  have hXmax : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := fun hu => by
    have := PowerSeries.isUnit_constantCoeff _ hu
    simp at this
  refine ⟨S, inferInstance, inferInstance, hS, S.val.toRingHom, Subtype.val_injective, fun x => ?_, ?_, ?_⟩
  · have := alg_monomial 0 (algebraMap Λ R x)
    rw [pow_zero, mul_one, ← PowerSeries.algebraMap_apply] at this
    exact this
  · rintro n x (hn | ⟨hn, hx⟩)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      refine ⟨algebraMap _ S (PowerSeries.C x * PowerSeries.X ^ k), hin _ ?_, alg_monomial k x⟩
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hXmax k (by exact_mod_cast hn))
    · have h1 : ∀ x ∈ Ideal.span (s : Set R), (HahnSeries.single (-(c : ℤ)) x : LaurentSeries R) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem g hg => exact Algebra.subset_adjoin ⟨g, hg, rfl⟩
        | zero => rw [map_zero]; exact S.zero_mem
        | add a b _ _ ha hb => rw [HahnSeries.single_add]; exact S.add_mem ha hb
        | smul r a _ ha =>
          have := S.mul_mem (S.algebraMap_mem (PowerSeries.C r * PowerSeries.X ^ 0)) ha
          rw [alg_monomial, HahnSeries.single_mul_single] at this
          simpa using this
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (a := n + c) (by omega)
      have h2 := S.mul_mem (S.algebraMap_mem (PowerSeries.C 1 * PowerSeries.X ^ k)) (h1 x (hs ▸ hx))
      rw [alg_monomial, HahnSeries.single_mul_single, one_mul, ← hk, add_neg_cancel_right] at h2
      obtain ⟨j, hj⟩ := hnils n x hx
      exact ⟨⟨_, h2⟩, nil_mem_max ⟨j, Subtype.ext hj⟩, rfl⟩
  · intro n
    obtain ⟨N, hN⟩ := bound_fin S
    have hrad : maximalIdeal S ≤ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := by
      intro y hy
      obtain ⟨p, hp⟩ := hnear y
      have hp0 : PowerSeries.constantCoeff p ∈ maximalIdeal R := fun hu =>
        hy (unit_of_near hp ((PowerSeries.isUnit_iff_constantCoeff.2 hu).map _))
      obtain ⟨q, hq⟩ : (PowerSeries.X : PowerSeries R) ∣ p - PowerSeries.C (PowerSeries.constantCoeff p) :=
        PowerSeries.X_dvd_iff.2 (by simp)
      have e1 : y = (y - algebraMap _ S p) + algebraMap _ S (PowerSeries.C (PowerSeries.constantCoeff p))
          + algebraMap (PowerSeries R) S PowerSeries.X * algebraMap _ S q := by
        rw [← map_mul, ← hq, map_sub]; ring
      have hz : ∀ z : S, IsNilpotent z →
          z ∈ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := fun z ⟨k, hk⟩ =>
        ⟨k, hk ▸ Ideal.zero_mem _⟩
      rw [e1]
      refine Ideal.add_mem _ (Ideal.add_mem _ (hz _ hp) (hz _ (((hnilx _ hp0).map _).map _))) ?_
      exact Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨e * (n.natAbs + 1 + N), fun y hy => ?_⟩
    rw [pow_mul] at hy
    have hy2 := Ideal.pow_right_mono he _ hy
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy2
    obtain ⟨z, rfl⟩ := hy2
    obtain ⟨q, hq⟩ := hN z.1 z.2
    have e2 : S.val.toRingHom (algebraMap (PowerSeries R) S PowerSeries.X ^ (n.natAbs + 1 + N) * z)
        = algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.X ^ (n.natAbs + 1) * q) := by
      rw [map_mul (algebraMap (PowerSeries R) (LaurentSeries R)), hq, Algebra.smul_def, ← mul_assoc, ← map_mul,
        ← pow_add, ← map_pow]
      rfl
    rw [e2]
    show ((PowerSeries.X ^ (n.natAbs + 1) * q : PowerSeries R) : LaurentSeries R).coeff n = 0
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_X_pow_mul']
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adj_map_ringHom {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (M : M4 R) :
    adj (M.map f) = (adj M).map f := by
  ext i j
  simp [adj, Matrix.map_apply]

private theorem sxPdMap_lemma_2 {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (c : R) (M : M4 R)
    (h : IsGSp c M) : IsGSp (f c) (M.map f) := by
  simp only [IsGSp] at h ⊢
  rw [adj_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem UpperTheory.V.Ws.sxPdMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' : Type} [CommRing R] [CommRing R'] (a : O →+* R) (f : R →+* R') (P : PD Φ.ι Γ R), (∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s)) ∧ (Φ.IsPair a P → Φ.IsPair (f.comp a) (P.map f)) ∧ (Φ.Res a P → Φ.Res (f.comp a) (P.map f)) := by
  intro O Γ _ _ Φ R R' _ _ a f P
  have hr : ∀ s, mapRep f P.r s = (P.r s).map f := fun s => by
    ext i j
    rw [mapRep_apply, Matrix.map_apply]
  have hψ : ∀ v i s, (P.map f).ψ v i s = f (P.ψ v i s) := fun v i s => by
    simp only [PD.map, PD.ψ]
    rw [hr, adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
  refine ⟨hψ, fun h => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨fun g => ?_, fun g hg => ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
    · simp only [PD.map, hr]
      exact sxPdMap_lemma_2 f _ _ (h1 g)
    · simp only [PD.map, hr, h2 g hg, Matrix.map_one, map_zero, map_one]
    · simp only [PD.map, hr]
      exact h3.map (map_zero f)
    · have := h4 v
      simp only [IsLow] at this ⊢
      simp only [PD.map]
      have hg := sxPdMap_lemma_2 f _ _ this.1
      rw [map_one] at hg
      refine ⟨hg, fun i => ?_, fun i j hij => ?_⟩
      · rw [Matrix.map_apply, this.2.1 i, map_one]
      · rw [Matrix.map_apply, this.2.2 i j hij, map_zero]
    · have := h5 v s hs
      simp only [IsUp] at this ⊢
      simp only [PD.map, hr]
      intro i j hij
      rw [adj_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, this i j hij, map_zero]
    · rw [hψ, h6 v s hs i, map_one]
  · obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun g i => ?_, fun v s hs i => ?_, ?_⟩
    · show mapRep f P.r g i i = _
      rw [mapRep_apply, h1 g i]
      rfl
    · rw [hψ, h2 v s hs i]
      rfl
    · simp only [Supp, SuppM, PD.map] at h3 ⊢
      rcases h3 with ⟨hA, hB⟩ | hC
      · exact Or.inl ⟨fun g i j h h' => by rw [mapRep_apply, hA g i j h h', map_zero],
          fun v i j h h' => by rw [Matrix.map_apply, hB v i j h h', map_zero]⟩
      · exact Or.inr fun g i j h h' => by rw [mapRep_apply, hC g i j h h', map_zero]
end

