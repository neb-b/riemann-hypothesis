module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0026
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.DualLattices.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndDifferentialRingHom
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

variable {R₀ : Type} [CommRing R₀]

private lemma endDiff_exists_lift {O R : LAlg R₀} (s : LHom O R) (i : (R : Type)) (hi : i * i = 0) :
    ∃ φ : LHom (DualNum.dualPair O).D R, φ.comp (DualNum.dualPair O).σ = s ∧
      φ.1 (DualNum.dualPair O).η = i := by
  let ψ : DualNum.DN O →ₐ[R₀] (R : Type) :=
    Ideal.Quotient.liftₐ _ (Polynomial.aevalTower s.1 i) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [pow_two, hi])
  have hσ : ∀ r, ψ ((DualNum.dualPair O).σ.1 r) = s.1 r := fun r => by
    change ψ (algebraMap (O : Type) (DualNum.DN O) r) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply]
    exact Polynomial.aevalTower_C s.1 i r
  have hη : ψ (DualNum.dualPair O).η = i := by
    change ψ (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aevalTower_X s.1 i
  refine ⟨⟨ψ, ⟨fun d hd => ?_⟩⟩, ?_, hη⟩
  · have hk : d - (DualNum.dualPair O).σ.1 ((DualNum.dualPair O).π.1 d) ∈
        RingHom.ker (DualNum.dualPair O).π.1 := by
      rw [RingHom.mem_ker, map_sub, (DualNum.dualPair O).sect, sub_self]
    rw [(DualNum.dualPair O).ker_eq] at hk
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hk
    have h1 : ψ y * i = ψ d - s.1 ((DualNum.dualPair O).π.1 d) := by
      rw [← hσ, ← hη]
      exact (map_mul ψ _ _).symm.trans ((congrArg ψ hy).trans (map_sub ψ _ _))
    have hn : IsNilpotent (-(ψ y * i)) := ⟨2, by
      rw [show (-(ψ y * i)) ^ 2 = ψ y * ψ y * (i * i) by ring, hi, mul_zero]⟩
    have hu : IsUnit (s.1 ((DualNum.dualPair O).π.1 d)) := by
      have h2 := hn.isUnit_add_left_of_commute (u := ψ d) hd (Commute.all _ _)
      rw [h1] at h2
      simpa using h2
    exact (DualNum.dualPair O).π.2.map_nonunit d (s.2.map_nonunit _ hu)
  · exact Subtype.ext (AlgHom.ext hσ)

private lemma endDiff_ηmap_surj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Surjective Dp.ηmap := by
  rintro ⟨x, hx⟩
  have hx' := hx
  rw [Submodule.restrictScalars_mem, Dp.ker_eq] at hx'
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  have hk : y - Dp.σ.1 (Dp.π.1 y) ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, Dp.sect, sub_self]
  rw [Dp.ker_eq] at hk
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨Dp.π.1 y, Subtype.ext ?_⟩
  change Dp.σ.1 (Dp.π.1 y) * Dp.η = y * Dp.η
  have := Dp.η_sq
  linear_combination (-Dp.η) * (-hz) - z * this

private lemma endDiff_ηmap_inj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Injective Dp.ηmap := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  exact Dp.free r (congrArg Subtype.val hr)

private lemma endDiff_coord {g : ℕ} {V M : Type} [AddCommGroup V] [Module R₀ V] [AddCommGroup M]
    [Module R₀ M] (gb : Module.Basis (Fin g) R₀ V) :
    Function.Bijective (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) := by
  have : (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft gb).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  rw [this]
  exact (TensorProduct.equivFinsuppOfBasisLeft gb).symm.bijective.comp
    Finsupp.equivFunOnFinite.symm.bijective

private def endDiff_IsMat {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) (d : Matrix (Fin g) (Fin g) (O : Type)) : Prop :=
  ∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
    (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (d k l) * i) →
      e.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)

private lemma endDiff_exists {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) : ∃ d, endDiff_IsMat gb e d := by
  let Dp := DualNum.dualPair O
  have h1 : ∀ l, ∃ c : Fin g → (O : Type), e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c k)) := fun l => by
    have h0 : B.map Dp.π (e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk))) = 0 := by
      rw [← e.nat, (B.tg_ker Dp.π Dp.sqZero _).2 ⟨_, rfl⟩, map_zero]
    obtain ⟨v, hv⟩ := (B.tg_ker Dp.π Dp.sqZero _).1 h0
    obtain ⟨m, rfl⟩ := (endDiff_coord (M := Dp.π.ker) gb).2 v
    choose c hc using fun k => endDiff_ηmap_surj Dp (m k)
    exact ⟨c, by rw [← hv]; simp only [hc]⟩
  choose c hc using h1
  refine ⟨fun k l => c l k, ?_⟩
  intro R S s π hπ l i m hm
  have hi : (i : (R : Type)) * i = 0 := by
    have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
    rw [hπ.2] at this
    simpa using this
  obtain ⟨φ, hφ, hη⟩ := endDiff_exists_lift s (i : (R : Type)) hi
  have hs : ∀ r, φ.1 (Dp.σ.1 r) = s.1 r := fun r => by rw [← hφ]; rfl
  have hf : ∀ a ∈ Dp.π.ker, φ.1.toLinearMap a ∈ π.ker := fun a ha => by
    obtain ⟨r, hr⟩ := endDiff_ηmap_surj Dp ⟨a, ha⟩
    have : a = Dp.σ.1 r * Dp.η := (congrArg Subtype.val hr).symm
    rw [this]
    change φ.1 (Dp.σ.1 r * Dp.η) ∈ RingHom.ker π.1
    rw [map_mul, hη]
    exact Ideal.mul_mem_left _ _ i.2
  have hA : gb l ⊗ₜ[R₀] i = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (gb l ⊗ₜ[R₀] Dp.ηk) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    exact Subtype.ext hη.symm
  have hB : ∑ k, gb k ⊗ₜ[R₀] m k = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c l k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.lTensor_tmul]
    congr 1
    refine Subtype.ext ?_
    change _ = φ.1 (Dp.σ.1 (c l k) * Dp.η)
    rw [hm k, map_mul, hη, hs]
  rw [hA, hB, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, ← hc l,
    ← e.nat, hφ]

private lemma endDiff_spec {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (l : Fin g) (r : (O : Type)) :
    e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap r)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d k l * r)) :=
  h Dp.σ Dp.π Dp.sqZero l _ _ fun k => by
    change Dp.σ.1 (d k l * r) * Dp.η = Dp.σ.1 (d k l) * (Dp.σ.1 r * Dp.η)
    rw [map_mul, _root_.mul_assoc]

private lemma endDiff_unique {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (d' : Matrix (Fin g) (Fin g) (O : Type))
    (h' : ∀ l, e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap 1)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d' k l))) : d = d' := by
  ext k l
  have h1 := B.tg_inj _ _ ((endDiff_spec h Dp l 1).symm.trans (h' l))
  have h2 := (endDiff_coord (M := Dp.π.ker) gb).1 h1
  simpa using endDiff_ηmap_inj Dp (congrFun h2 k)

theorem exists_endDifferential_ringHom :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O),
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    ∃ dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type), (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ g B O gb O₀ _ f hf
  choose d hd using fun a => endDiff_exists gb (f a)
  let Dp := DualNum.dualPair O
  have hadd : ∀ a b, d (a + b) = d a + d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).1, endDiff_spec (hd a), endDiff_spec (hd b), ← map_add (f := _),
        ← Finset.sum_add_distrib]
      simp [TensorProduct.tmul_add]
  have hone : d 1 = 1 :=
    endDiff_unique (hd _) Dp _ fun l => by
      rw [(hf _ _).1, Finset.sum_eq_single l]
      · simp
      · intro k _ hk
        simp [Matrix.one_apply_ne hk]
      · simp
  have hmul : ∀ a b, d (a * b) = d a * d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [((hf _ _).2 a b).2, endDiff_spec (hd b), map_sum, map_sum]
      simp only [endDiff_spec (hd a)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.sum_comm]
      simp [Matrix.mul_apply, TensorProduct.tmul_sum]
  have hzero : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  exact ⟨⟨⟨⟨d, hone⟩, hmul⟩, hzero, hadd⟩, fun a => hd a⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable abbrev serNatI (R₀ κ : Type) [CommRing R₀] (N : ℕ) : Ideal (MvPolynomial κ R₀) :=
  Ideal.span (Set.range fun j : κ => (MvPolynomial.X j : MvPolynomial κ R₀) ^ N)

private lemma serNat_coeff {R₀ κ : Type} [CommRing R₀] [DecidableEq κ] {N : ℕ}
    {q : MvPolynomial κ R₀} (hq : q ∈ serNatI R₀ κ N) :
    ∀ m : κ →₀ ℕ, (∀ j, m j < N) → AddMonoidAlgebra.coeff q m = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨j, rfl⟩ m hm
    simp only [MvPolynomial.coeff_X_pow]
    rw [if_neg]
    rintro rfl
    simpa using hm j
  · intro m _; simp
  · intro x y _ _ hx hy m hm
    rw [MvPolynomial.coeff_add, hx m hm, hy m hm, add_zero]
  · intro r x _ hx m hm
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [hx p.2, mul_zero]
    intro j
    have : p.1 + p.2 = m := by simpa using hp
    have h2 := hm j
    rw [← this, Finsupp.add_apply] at h2
    omega

private lemma serNat_nil {R₀ κ : Type} [CommRing R₀] (N : ℕ) (j : κ) :
    (Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)) ^ N = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

private lemma serNat_aeval {R₀ κ : Type} [CommRing R₀] [Fintype κ] [DecidableEq κ]
    {S : Type} [CommRing S] [Algebra R₀ S] {N : ℕ} {a : κ → S} (ha : ∀ i, a i ^ N = 0)
    (q : MvPolynomial κ R₀) :
    MvPolynomial.aeval a q = ∑ e : κ → Fin N, algebraMap R₀ S (AddMonoidAlgebra.coeff
      q (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ))) * ∏ i, a i ^ (e i : ℕ) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add (f := _), MvPolynomial.coeff_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | monomial m r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    by_cases hm : ∀ j, m j < N
    · rw [Finset.sum_eq_single (fun j => (⟨m j, hm j⟩ : Fin N))]
      · rw [MvPolynomial.coeff_monomial, if_pos]
        ext j; simp
      · intro e _ he
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply he
        funext j
        apply Fin.ext
        simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero]
      · push Not at hm
        obtain ⟨j, hj⟩ := hm
        rw [Finset.prod_eq_zero (f := fun i => a i ^ m i) (Finset.mem_univ j)
          (pow_eq_zero_of_le hj (ha j)), mul_zero]
      · intro e _
        rw [MvPolynomial.coeff_monomial, if_neg, map_zero, zero_mul]
        intro h
        apply hm
        intro j
        simp [h]

theorem exists_series_of_natural_on_nilpotent :
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] {κ : Type} [Fintype κ] [DecidableEq κ] (c : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (κ → S) → S),
    (∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : κ → S),
      (∀ i, IsNilpotent (a i)) → φ (c S a) = c S' (fun i => φ (a i))) →
    ∃ f : MvPowerSeries κ R₀, ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, IsNilpotent (a i)) → c S a = nEval f a) := by
  intro hE R₀ _ κ _ _ c hc
  choose p hp using fun N : ℕ => Ideal.Quotient.mk_surjective (I := serNatI R₀ κ N)
    (c (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N)
      (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j)))
  have key : ∀ (N : ℕ) (S : Type) [CommRing S] [Algebra R₀ S] (a : κ → S), (∀ i, a i ^ N = 0) →
      c S a = MvPolynomial.aeval a (p N) := by
    intro N S _ _ a ha
    let φ : (MvPolynomial κ R₀ ⧸ serNatI R₀ κ N) →ₐ[R₀] S :=
      Ideal.Quotient.liftₐ (serNatI R₀ κ N) (MvPolynomial.aeval a) (by
        intro x hx
        have : serNatI R₀ κ N ≤ RingHom.ker (MvPolynomial.aeval (R := R₀) a) := by
          refine Ideal.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp [RingHom.mem_ker, ha j]
        exact this hx)
    have hφ : ∀ x, φ (Ideal.Quotient.mk (serNatI R₀ κ N) x) = MvPolynomial.aeval a x :=
      fun x => rfl
    have h := hc _ S φ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => ⟨N, serNat_nil N j⟩)
    rw [← hp N, hφ] at h
    simp only [hφ, MvPolynomial.aeval_X] at h
    exact h.symm
  have compat : ∀ N M : ℕ, N ≤ M → ∀ m : κ →₀ ℕ, (∀ j, m j < N) →
      AddMonoidAlgebra.coeff (p M) m = AddMonoidAlgebra.coeff (p N) m := by
    intro N M h m hm
    have h1 := key M _ (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
      (fun j => pow_eq_zero_of_le h (serNat_nil N j))
    have h2 : MvPolynomial.aeval (R := R₀)
        (fun j => Ideal.Quotient.mk (serNatI R₀ κ N) (MvPolynomial.X j))
        = Ideal.Quotient.mkₐ R₀ (serNatI R₀ κ N) := by
      ext j; simp
    rw [← hp N, h2, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at h1
    have h3 := serNat_coeff h1 m hm
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at h3
    exact h3.symm
  refine ⟨fun m => AddMonoidAlgebra.coeff (p (Finset.univ.sup m + 1)) m, ?_⟩
  intro S _ _ a ha
  choose n hn using ha
  have hN : ∀ i, a i ^ (Finset.univ.sup n) = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i)
  generalize Finset.univ.sup n = N at hN
  refine Eq.trans ?_ ((hE _ S a).1 N hN).symm
  rw [key N S a hN, serNat_aeval hN]
  unfold tEval
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  set m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ) with hm
  change _ = AddMonoidAlgebra.coeff (p (Finset.univ.sup m + 1)) m
  rw [← compat N (max N (Finset.univ.sup m + 1)) (le_max_left _ _) m (fun j => by simp [hm]),
    compat _ _ (le_max_right _ _) m
      (fun j => Nat.lt_succ_of_le (Finset.le_sup (f := m) (Finset.mem_univ j)))]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FAddNsmulFEqEvalPolyFrob
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def btPolySub (p : ℕ) (g : ℕ) (W : Type) [CommRing W] :
    Subalgebra W (MvPolynomial (Fin g) W) where
  carrier := {q | ∀ m : Fin g →₀ ℕ, (∃ i, ¬ p ∣ m i) →
    AddMonoidAlgebra.coeff q m ∈ Ideal.span {(p : W)}}
  add_mem' := by
    intro a b ha hb m hm
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact Ideal.add_mem _ (ha m hm) (hb m hm)
  mul_mem' := by
    intro a b ha hb m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : p ∣ x.1 i
    · refine Ideal.mul_mem_left _ _ (hb _ ⟨i, fun h2 => hi ?_⟩)
      rw [← hx', Finsupp.add_apply]
      exact dvd_add h1 h2
    · exact Ideal.mul_mem_right _ _ (ha _ ⟨i, h1⟩)
  algebraMap_mem' := by
    intro r m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C, ite_eq_right]
    · exact Ideal.zero_mem _
    · rintro rfl
      exact hi (by simp)

private lemma btPoly_map_tEval {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (f : MvPowerSeries ι R₀) {S S' : Type} [CommRing S] [Algebra R₀ S] [CommRing S']
    [Algebra R₀ S'] (φ : S →ₐ[R₀] S') (a : ι → S) :
    φ (tEval N f a) = tEval N f (fun i => φ (a i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [tEval, map_sum, map_prod]

private lemma btPoly_unif {ι S : Type} [Fintype ι] [CommRing S] (a : ι → S)
    (h : ∀ i, IsNilpotent (a i)) : ∃ M, ∀ M' ≥ M, ∀ i, a i ^ M' = 0 := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun M' hM i => ?_⟩
  exact pow_eq_zero_of_le ((Finset.le_sup (Finset.mem_univ i)).trans hM) (hn i)

private lemma btPoly_nil {R₀ : Type} [CommRing R₀]
    (H : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S]
      [Algebra R₀ S] (a : ι → S), (∀ i, IsNilpotent (a i)) →
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))
    {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (S : Type) [CommRing S] [Algebra R₀ S]
    (a : Fin g → S) (ha : ∀ i, IsNilpotent (a i)) (n : ℕ) :
    ∀ k, IsNilpotent (nsmulF ch.F a n k) := by
  have h0 : ∀ k, algebraMap R₀ S (MvPowerSeries.coeff 0 (ch.F k)) = 0 := by
    intro k
    have h1 := congrFun (ch.F_unit S 0 (fun _ => IsNilpotent.zero)) k
    have h2 := H (ch.F k) S (Sum.elim (0 : Fin g → S) (0 : Fin g → S))
      (by rintro (i | i) <;> exact IsNilpotent.zero)
    have h3 : Ideal.span (Set.range (Sum.elim (0 : Fin g → S) (0 : Fin g → S))) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i | i, rfl⟩ <;> rfl
    rw [h3, Ideal.mem_bot] at h2
    change nEval _ _ = 0 at h1
    rw [h1] at h2
    simpa using h2
  induction n with
  | zero => intro k; exact IsNilpotent.zero
  | succ n ih =>
    intro k
    have hn : ∀ i, IsNilpotent (Sum.elim (nsmulF ch.F a n) a i) := by
      rintro (i | i)
      · exact ih i
      · exact ha i
    have h2 := H (ch.F k) S _ hn
    rw [h0, sub_zero] at h2
    have h3 : Ideal.span (Set.range (Sum.elim (nsmulF ch.F a n) a)) ≤ nilradical S := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    exact h3 h2

theorem fAdd_nsmulF_eq_eval_poly_frob :
  (∀ {R₀ : Type} [CommRing R₀] {ι : Type} [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R₀) (S : Type) [CommRing S] [Algebra R₀ S] (a : ι → S),
    (∀ N : ℕ, (∀ i, a i ^ N = 0) → nEval f a = tEval N f a) ∧
    ((∀ i, IsNilpotent (a i)) → (∀ (S' : Type) [CommRing S'] [Algebra R₀ S'] (φ : S →ₐ[R₀] S'), φ (nEval f a) = nEval f (fun i => φ (a i))) ∧
      nEval f a - algebraMap R₀ S (MvPowerSeries.coeff 0 f) ∈ Ideal.span (Set.range a))) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} (K : LAlg R₀) (ch : FormalChartAtZero B K g), PSerFrobStatement p K ch) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff (Γ k) m ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) := by
  intro H1 H2 R₀ _ p _ g B K ch W _ _ c hc N
  obtain ⟨G, hG, hGe⟩ := H2 p K ch N
  let I : Ideal (MvPolynomial (Fin g) R₀) := Ideal.span (Set.range fun j => MvPolynomial.X j ^ N)
  let x : Fin g → MvPolynomial (Fin g) R₀ ⧸ I := fun j => Ideal.Quotient.mk I (MvPolynomial.X j)
  have hx : ∀ j, x j ^ N = 0 := fun j => by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hae : (MvPolynomial.aeval x : MvPolynomial (Fin g) R₀ →ₐ[R₀] _) = Ideal.Quotient.mkₐ R₀ I := by
    ext j; simp [x]
  have hnil : ∀ k, IsNilpotent (Ideal.Quotient.mk I (G k)) := fun k => by
    have := btPoly_nil (fun f S _ _ a ha => ((H1 f S a).2 ha).2) ch _ x (fun i => ⟨N, hx i⟩) p k
    rw [hGe _ x hx, hae] at this
    exact this
  obtain ⟨M₁, hM₁⟩ := btPoly_unif _ hnil
  obtain ⟨M₂, hM₂⟩ := btPoly_unif _ hc
  let z : Fin g ⊕ Fin g → MvPolynomial (Fin g) W :=
    Sum.elim (fun i => MvPolynomial.C (c i)) (fun i => MvPolynomial.map (algebraMap R₀ W) (G i))
  refine ⟨fun k => tEval (max M₁ M₂) (ch.F k) z, fun k => ?_, fun y hy => ?_⟩
  · change tEval (max M₁ M₂) (ch.F k) z ∈ btPolySub p g W
    unfold tEval
    refine Subalgebra.sum_mem _ fun e _ => Subalgebra.mul_mem _ ?_
      (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · rw [IsScalarTower.algebraMap_apply R₀ W]
      exact Subalgebra.algebraMap_mem _ _
    · rcases i with i | i
      · exact Subalgebra.algebraMap_mem (btPolySub p g W) (c i)
      · intro m hm
        obtain ⟨r, hr⟩ := hG i m hm
        change AddMonoidAlgebra.coeff (MvPolynomial.map (algebraMap R₀ W) (G i)) m ∈ _
        rw [MvPolynomial.coeff_map, hr, map_mul, map_natCast]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · funext k
    have hI : ∀ q ∈ I, MvPolynomial.aeval y q = (0 : W) := by
      intro q hq
      have : I ≤ RingHom.ker (MvPolynomial.aeval y : MvPolynomial (Fin g) R₀ →ₐ[R₀] W) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        simp [RingHom.mem_ker, hy j]
      exact this hq
    have e1 := btPoly_map_tEval (max M₁ M₂) (ch.F k)
      ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀) z
    have e2 : (fun i => ((MvPolynomial.aeval y : MvPolynomial (Fin g) W →ₐ[W] W).restrictScalars R₀)
        (z i)) = Sum.elim c (fun k => MvPolynomial.aeval y (G k)) := by
      funext i
      rcases i with i | i
      · simp [z]
      · simp only [z, AlgHom.coe_restrictScalars', Sum.elim_inr]
        exact MvPolynomial.aeval_map_algebraMap W y (G i)
    rw [e2] at e1
    rw [hGe W y hy]
    change nEval _ _ = _
    rw [(H1 (ch.F k) W _).1 (max M₁ M₂), ← e1]
    · simp
    · rintro (i | i)
      · exact hM₂ _ (le_max_right _ _) i
      · have := hM₁ _ (le_max_left M₁ M₂) i
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at this
        have := hI _ this
        rwa [map_pow] at this

end GlobalTheory
end

