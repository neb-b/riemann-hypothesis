module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DenseGen
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem contMod (l : ℕ) [Fact l.Prime] (k : ℕ) {N : Type} [TopologicalSpace N] (c : ZMod (l ^ k) → N) :
    Continuous fun x : ℤ_[l] => c (PadicInt.toZModPow k x) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have h1 : y - x ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy.le
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]

private theorem clopenEq {X N : Type} [TopologicalSpace X] [TopologicalSpace N] [DiscreteTopology N] {f g : X → N}
    (hf : Continuous f) (hg : Continuous g) : IsClopen {x | f x = g x} := by
  have h : {x | f x = g x} = (fun x => (f x, g x)) ⁻¹' {p : N × N | p.1 = p.2} := rfl
  rw [h]
  exact (isClopen_discrete _).preimage (hf.prodMk hg)

private theorem powGen (l : ℕ) [Fact l.Prime] (n : ℕ) :
    (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n = Multiplicative.ofAdd (n : ℤ_[l]) := by
  rw [← ofAdd_nsmul, nsmul_one]

private theorem denseGen (l : ℕ) [Fact l.Prime] :
    DenseRange fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n := by
  have h : (fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n) =
      fun n : ℕ => Multiplicative.ofAdd (n : ℤ_[l]) := funext (powGen l)
  rw [h]
  exact PadicInt.denseRange_natCast

private theorem tendGen (l : ℕ) [Fact l.Prime] :
    Filter.Tendsto (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) Filter.atTop (nhds 1) := by
  have h : (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) =
      fun a : ℕ => Multiplicative.ofAdd ((l : ℤ_[l]) ^ a) := by
    funext a
    rw [powGen]
    push_cast
    rfl
  rw [h]
  have h2 : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h2

private theorem solveGen (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N) (hσ : ContAction σ)
    (ht : ∀ m : N, ∃ n : ℕ, l ^ n • m = 0) (φ : Multiplicative ℤ_[l] → N) (hφ : Continuous φ) (m₀ : N) :
    ∃ C : Multiplicative ℤ_[l] → N, Continuous C ∧ C 1 = m₀ ∧
      ∀ x, C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x := by
  let γ : Multiplicative ℤ_[l] := Multiplicative.ofAdd 1
  let a : ℕ → N := fun n => Nat.rec (motive := fun _ => N) m₀ (fun k ak => σ γ ak - φ (γ ^ k)) n
  have ha0 : a 0 = m₀ := rfl
  have haS : ∀ n, a (n + 1) = σ γ (a n) - φ (γ ^ n) := fun n => rfl
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  have hper : ∀ m : N, ∀ᶠ k in Filter.atTop, σ (γ ^ (l ^ k)) m = m := by
    intro m
    have hc : Continuous fun g : Multiplicative ℤ_[l] => σ g m :=
      hσ'.comp (continuous_id.prodMk continuous_const)
    have ht2 := (hc.tendsto 1).comp (tendGen l)
    rw [map_one σ, Module.End.one_apply, nhds_discrete, Filter.tendsto_pure] at ht2
    exact ht2
  have hφper : ∀ᶠ k in Filter.atTop, ∀ x, φ (γ ^ (l ^ k) * x) = φ x := by
    have hev : ∀ᶠ y in nhds (1 : Multiplicative ℤ_[l]),
        ∀ x ∈ (Set.univ : Set (Multiplicative ℤ_[l])), φ (y * x) = φ x := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro x _
      have hopen : IsOpen {z : Multiplicative ℤ_[l] × Multiplicative ℤ_[l] | φ (z.1 * z.2) = φ z.2} :=
        (clopenEq (hφ.comp continuous_mul) (hφ.comp continuous_snd)).isOpen
      exact hopen.mem_nhds (by simp)
    filter_upwards [(tendGen l).eventually hev] with k hk x
    exact hk x (Set.mem_univ x)
  have L1 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ n, a (n + q) - a n = σ (γ ^ n) (a q - a 0) := by
    intro q hq n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + q = n + q + 1 by omega, haS, haS, pow_succ', map_mul, Module.End.mul_apply,
        ← ih, map_sub]
      have h1 : φ (γ ^ (n + q)) = φ (γ ^ n) := by
        rw [pow_add, mul_comm (γ ^ n), hq]
      rw [h1]
      abel
  have L2 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ s, a (s * q) - a 0 = ∑ t ∈ Finset.range s, σ (γ ^ (t * q)) (a q - a 0) := by
    intro q hq s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Finset.sum_range_succ, ← ih, ← L1 q hq (s * q), add_one_mul]
      abel
  have Lmul : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) → ∀ s, ∀ x, φ (γ ^ (q * s) * x) = φ x := by
    intro q hq s
    induction s with
    | zero => intro x; simp
    | succ s ih => intro x; rw [Nat.mul_succ, pow_add, mul_assoc, ih, hq]
  obtain ⟨k, hk⟩ := hφper.exists
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (hper (a (l ^ k) - a 0))
  have hK1 : l ^ (max A k) = l ^ k * l ^ (max A k - k) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_right A k)]
  have hφQ : ∀ x, φ (γ ^ (l ^ (max A k)) * x) = φ x := by
    rw [hK1]
    exact Lmul _ hk _
  have hdQ : a (l ^ (max A k)) - a 0 =
      ∑ t ∈ Finset.range (l ^ (max A k - k)), σ (γ ^ (t * l ^ k)) (a (l ^ k) - a 0) := by
    rw [← L2 _ hk, hK1, mul_comm (l ^ k)]
  have hfixQ : σ (γ ^ (l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdQ, map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm (γ ^ (l ^ (max A k))), map_mul,
      Module.End.mul_apply, hA (max A k) (le_max_left A k)]
  obtain ⟨j, hj⟩ := ht (a (l ^ (max A k)) - a 0)
  have hφK : ∀ x, φ (γ ^ (l ^ (max A k + j)) * x) = φ x := by
    rw [pow_add]
    exact Lmul _ hφQ _
  have haK : a (l ^ (max A k + j)) = a 0 := by
    have h2 := L2 _ hφQ (l ^ j)
    have h3 : ∀ t ∈ Finset.range (l ^ j),
        σ (γ ^ (t * l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
      intro t _
      rw [mul_comm t, pow_mul, map_pow, Module.End.pow_apply, Function.iterate_fixed hfixQ]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, hj] at h2
    rw [pow_add, mul_comm]
    exact sub_eq_zero.mp h2
  have hperiod : ∀ n, a (n + l ^ (max A k + j)) = a n := by
    intro n
    have h4 := L1 _ hφK n
    rw [haK, sub_self, map_zero, sub_eq_zero] at h4
    exact h4
  have hperiod' : ∀ s n, a (n + l ^ (max A k + j) * s) = a n := by
    intro s
    induction s with
    | zero => intro n; simp
    | succ s ih => intro n; rw [Nat.mul_succ, ← add_assoc, hperiod, ih]
  have hmod : ∀ n, a (n % l ^ (max A k + j)) = a n := by
    intro n
    conv_rhs => rw [← Nat.mod_add_div n (l ^ (max A k + j))]
    rw [hperiod']
  let C : Multiplicative ℤ_[l] → N :=
    fun x => a (PadicInt.toZModPow (max A k + j) (Multiplicative.toAdd x)).val
  have hCc : Continuous C :=
    (contMod l (max A k + j) (fun i : ZMod (l ^ (max A k + j)) => a i.val)).comp continuous_toAdd
  have hCn : ∀ n : ℕ, C (γ ^ n) = a n := by
    intro n
    simp only [C, γ, powGen, toAdd_ofAdd, map_natCast, ZMod.val_natCast]
    exact hmod n
  refine ⟨C, hCc, ?_, ?_⟩
  · have h5 : C 1 = a 0 := by
      simp only [C, toAdd_one, map_zero, ZMod.val_zero]
    rw [h5, ha0]
  · intro x
    refine (denseGen l).induction_on
      (p := fun x => C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x) x ?_ ?_
    · exact (clopenEq (hCc.comp (continuous_const_mul _))
        ((continuous_of_discreteTopology
          (f := fun pr : N × N => σ (Multiplicative.ofAdd 1) pr.1 - pr.2)).comp
          (hCc.prodMk hφ))).isClosed
    · intro n
      show C (γ * γ ^ n) = σ γ (C (γ ^ n)) - φ (γ ^ n)
      rw [← pow_succ', hCn, hCn, haS]

theorem UpperTheory.V.Base.h2Zl :
    ∀ (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [ContinuousConstSMul R N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N), ContAction σ →
      (∀ m : N, ∃ n : ℕ, l ^ n • m = 0) → Subsingleton (H2 σ) := by
  intro l _ R N _ _ _ _ _ _ _ σ hσ ht
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show f.1 ∈ B2 σ
  rw [separated_dvr_second_cohomology_mem]
  have hf : Continuous f.1 := f.2.1
  have hcoc := f.2.2
  have hφ : Continuous fun y => f.1 (Multiplicative.ofAdd (1 : ℤ_[l]), y) :=
    hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC, hC1, hCeq⟩ := solveGen l R N σ hσ ht _ hφ (f.1 (1, 1))
  refine ⟨C, hC, ?_⟩
  funext pr
  obtain ⟨g, h⟩ := pr
  show σ g (C h) - C (g * h) + C g = f.1 (g, h)
  have hf1 : ∀ k, f.1 (1, k) = f.1 (1, 1) := by
    intro k
    have h0 := hcoc 1 1 k
    simp only [map_one, one_mul, Module.End.one_apply, sub_self, zero_add] at h0
    exact sub_eq_zero.mp h0
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  refine (denseGen l).induction_on (p := fun g => σ g (C h) - C (g * h) + C g = f.1 (g, h)) g ?_ ?_
  · exact (clopenEq
      (((hσ'.comp (continuous_id.prodMk continuous_const)).sub
        (hC.comp (continuous_mul_const h))).add hC)
      (hf.comp (continuous_id.prodMk continuous_const))).isClosed
  · intro n
    induction n with
    | zero =>
      simp only [pow_zero, map_one, Module.End.one_apply, one_mul, sub_self, zero_add]
      rw [hC1, hf1 h]
    | succ n ih =>
      rw [pow_succ', mul_assoc, hCeq, hCeq, map_mul, Module.End.mul_apply]
      have hc := hcoc (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1 ^ n) h
      rw [← ih, map_add (f := _), map_sub] at hc
      rw [← sub_eq_zero]
      convert hc using 1
      abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem aux {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) : ∃ m, ∀ g, H.index • f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.Qi36.aux π H f hf h0

theorem UpperTheory.V.Base.kerResSmul :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (x : H1U ρ U), resU ρ h x = 0 → U'.relIndex U • x = 0 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
  obtain ⟨s, hs⟩ := aux (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)
    (fun u => z.1 u - (ρ u m - m))
    (fun g k => by
      have e : z.1 (g * k) = z.1 g + ρ g (z.1 k) := z.2.2 g k
      show z.1 (g * k) - (ρ ((g : G) * k) m - m) = z.1 g - (ρ g m - m) + ρ g (z.1 k - (ρ k m - m))
      rw [e, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel)
    (fun u hu => sub_eq_zero.2 (hm ⟨u.1, hu⟩))
  have e0 : U'.relIndex U • (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk (U'.relIndex U • z) :=
    (map_nsmul (Submodule.mkQ _) _ z).symm
  rw [e0, Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨s + U'.relIndex U • m, fun g => ?_⟩
  have e : U'.relIndex U • (z.1 g - (ρ g m - m)) = ρ g s - s := hs g
  show U'.relIndex U • z.1 g = ρ g (s + U'.relIndex U • m) - (s + U'.relIndex U • m)
  rw [smul_sub, smul_sub, sub_eq_iff_eq_add] at e
  rw [e, map_add (f := _), map_nsmul]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenCokerLe
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_ker_eq_coker {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (A ⧸ LinearMap.range f) = Module.length R (LinearMap.ker f) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(f.quotKerEquivRange).length_eq] at h2
  have h3 : Module.length R (LinearMap.range f) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h1
    exact hfin h1
  rw [h1, add_comm] at h2
  exact (WithTop.add_right_inj h3).1 h2

private theorem len_sup_ne_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (S T : Submodule R A) (hS : Module.length R S ≠ ⊤) (hT : Module.length R T ≠ ⊤) :
    Module.length R (S ⊔ T : Submodule R A) ≠ ⊤ := by
  have h := Module.length_le_of_surjective (S.subtype.coprod T.subtype).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.length_prod] at h
  exact ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hS, hT⟩) h

private theorem len_map_le {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (a : R)
    (F : Submodule R N) (hF : Module.length R F ≠ ⊤) :
    Module.length R (F.map (LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))).mkQ) ≤
      Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  let g : F →ₗ[R] F.map P.mkQ := P.mkQ.submoduleMap F
  have hg : Function.Surjective g := LinearMap.submoduleMap_surjective _ _
  have hle : LinearMap.range (a • (LinearMap.id : F →ₗ[R] F)) ≤ LinearMap.ker g := by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    show P.mkQ (a • (x : N)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hg' : Function.Surjective (Submodule.liftQ _ g hle) := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hg').trans ?_
  rw [len_ker_eq_coker _ hF]
  refine Module.length_le_of_injective
    (F.subtype.restrict (p := LinearMap.ker (a • (LinearMap.id : F →ₗ[R] F)))
      (q := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) ?_) ?_
  · intro x hx
    exact congrArg Subtype.val hx
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

theorem UpperTheory.V.Base.lenCokerLe :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N], (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) → ∀ a : R,
      Module.length R (N ⧸ LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))) ≤ Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  intro R N _ _ _ hN a
  by_contra hlt
  rw [not_le] at hlt
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  set K := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N)) with hK
  have key : ∀ k : ℕ, ∃ F : Submodule R N, Module.length R F ≠ ⊤ ∧
      (k : ℕ∞) ≤ Module.length R (F.map P.mkQ) := by
    intro k
    induction k with
    | zero => exact ⟨⊥, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hk⟩ := ih
      have h1 : Module.length R (F.map P.mkQ) ≤ Module.length R K := len_map_le a F hF
      have h2 : F.map P.mkQ ≠ ⊤ := by
        intro h
        rw [h, Module.length_top] at h1
        exact absurd hlt (not_lt.2 h1)
      obtain ⟨y, hy⟩ : ∃ y, y ∉ F.map P.mkQ := by
        by_contra hh
        exact h2 (eq_top_iff.2 fun y _ => by_contra fun h => hh ⟨y, h⟩)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
      refine ⟨F ⊔ Submodule.span R {x}, len_sup_ne_top _ _ hF (hN x), ?_⟩
      have h3 : F.map P.mkQ < (F ⊔ Submodule.span R {x}).map P.mkQ := by
        refine lt_of_le_of_ne (Submodule.map_mono le_sup_left) fun h => hy ?_
        rw [h]
        exact Submodule.mem_map_of_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      have h4 : Order.height (F.map P.mkQ) < ⊤ := by
        rw [← Module.length_submodule]
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le hlt le_top)
      have h5 := Order.height_strictMono h3 h4
      rw [← Module.length_submodule, ← Module.length_submodule] at h5
      rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt (lt_of_le_of_lt hk h5)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lt_of_lt_of_le hlt le_top).ne
  obtain ⟨F, hF, hk⟩ := key (n + 1)
  have h := hk.trans (len_map_le a F hF)
  rw [← hK, ← hn] at h
  exact absurd (Nat.cast_le.1 h) (by omega)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : LinearMap.ker g ≤ LinearMap.range f) :
    Module.length R B ≤ Module.length R C + Module.length R A := by
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [e, add_comm]
  refine add_le_add (Module.length_le_of_injective _ (Submodule.subtype_injective _)) ?_
  exact (Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
    (Module.length_le_of_surjective _ f.surjective_rangeRestrict)

theorem UpperTheory.V.Base.lenComp :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] (a b : Module.End R N),
      Module.length R (LinearMap.ker (a * b)) ≤ Module.length R (LinearMap.ker a) + Module.length R (LinearMap.ker b) ∧
      Module.length R (N ⧸ LinearMap.range (a * b)) ≤ Module.length R (N ⧸ LinearMap.range a) + Module.length R (N ⧸ LinearMap.range b) := by
  intro R N _ _ _ a b
  constructor
  · have h1 : LinearMap.ker b ≤ LinearMap.ker (a * b) := fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [Module.End.mul_apply, hx, map_zero]
    have h2 : ∀ x ∈ LinearMap.ker (a * b), b x ∈ LinearMap.ker a := fun x hx => hx
    refine length_le_of_exact (Submodule.inclusion h1) (LinearMap.restrict b h2) fun x hx => ?_
    exact ⟨⟨x.1, congrArg Subtype.val hx⟩, rfl⟩
  · have h1 : LinearMap.range b ≤ (LinearMap.range (a * b)).comap a := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have h2 : LinearMap.range (a * b) ≤ (LinearMap.range a).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩
      exact ⟨b y, rfl⟩
    refine length_le_of_exact (Submodule.mapQ _ _ a h1) (Submodule.mapQ _ _ LinearMap.id h2) fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, hy]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenLeAdd
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_add {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) :
    Module.length R A ≤ Module.length R B + Module.length R (LinearMap.ker k) := by
  have h1 : Module.length R A = Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.injective_subtype _)
      g.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have h2 : Module.length R (LinearMap.range g) ≤ Module.length R B :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.injective_subtype _)
  have h3 : Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.ker k) :=
    Module.length_le_of_injective (j.restrict (p := LinearMap.ker g) (q := LinearMap.ker k) fun x hx => hk x hx)
      fun x y e => Subtype.ext (hj (congrArg Subtype.val e))
  rw [h1, add_comm]
  exact add_le_add h2 h3

private theorem len_sub {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) (P : Submodule R A) (Q : Submodule R B)
    (hPQ : ∀ x ∈ P, g x ∈ Q) :
    Module.length R P ≤ Module.length R Q + Module.length R (LinearMap.ker k) :=
  len_le_add (g.restrict hPQ) (j.comp P.subtype) k (hj.comp (Submodule.injective_subtype P))
    fun x hx => hk x.1 (congrArg Subtype.val hx)

theorem UpperTheory.V.Base.selUp :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U' 𝒟) + Module.length R (LinearMap.ker (resU ρ h)) ∧
      (∀ [U'.Normal], Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (selEig ρ U' h𝒟 U 1) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      (∀ [U'.Normal] [U.Normal] (W : Subgroup G) (ψ : W →* Rˣ),
        Module.length R (selEig ρ U h𝒟 W ψ) ≤ Module.length R (selEig ρ U' h𝒟 W ψ) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      ∀ [U'.Normal] [U.Normal] (g : G) (s : R), Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) ≤
        Module.length R (Module.End.eigenspace (selRep ρ U' h𝒟 g) s) + Module.length R (LinearMap.ker (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 h𝒟
  have hj := Submodule.injective_subtype (LocSel ρ U 𝒟)
  have hk : ∀ x, selRes ρ h 𝒟 x = 0 → resU ρ h ((LocSel ρ U 𝒟).subtype x) = 0 :=
    fun x hx => congrArg Subtype.val hx
  refine ⟨len_le_add (selRes ρ h 𝒟) _ _ hj hk, ?_, ?_, ?_⟩
  · intro _
    have hm : ∀ x, selRes ρ h 𝒟 x ∈ selEig ρ U' h𝒟 U 1 := fun x => by
      rw [selEig, eig_one]
      intro g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    exact len_le_add ((selRes ρ h 𝒟).codRestrict _ hm) _ _ hj fun x hx => hk x (congrArg Subtype.val hx)
  · intro _ _ W ψ
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [mem_eig] at hx ⊢
    intro g
    have e : selRep ρ U h𝒟 g.1 x = ((ψ g : Rˣ) : R) • x := hx g
    show selRep ρ U' h𝒟 g.1 _ = _
    rw [← selRes_selRep, e, map_smul]
  · intro _ _ g s
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← selRes_selRep, hx, map_smul]
end

