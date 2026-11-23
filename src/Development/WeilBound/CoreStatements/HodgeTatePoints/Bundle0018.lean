module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcIncl
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

private theorem mem_range_bc_of_entries_mem_intL {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (k : K)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ c : A, s • k = algebraMap A K c) :
    ∃ c : A, algebraMap A K c = k := by
  have hk : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
    rw [GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof A K]
    refine (Submodule.mem_iInf _).2 fun p => (Submodule.mem_iInf _).2 fun hp => ?_
    obtain ⟨s, hs, c, hc⟩ := h p.asIdeal p.isPrime hp
    refine ⟨s, hs, ?_⟩
    rw [hc, Subalgebra.mem_toSubmodule]
    exact Subalgebra.algebraMap_mem _ c
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, hc⟩

theorem test_incl : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω), M.IsFullLattice K → Module.Projective A M → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ M) → x ∈ M := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x hlat hproj hloc
  classical
  have hden : ∀ w ∈ Submodule.span K (M : Set Ω), ∃ d ∈ nonZeroDivisors A, d • w ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact ⟨1, one_mem _, by rw [one_smul]; exact hw⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
    | add u w _ _ hu hw =>
      obtain ⟨d1, hd1, h1⟩ := hu
      obtain ⟨d2, hd2, h2⟩ := hw
      refine ⟨d1 * d2, mul_mem hd1 hd2, ?_⟩
      have e1 : (d1 * d2) • u = d2 • (d1 • u) := by rw [mul_comm, mul_smul]
      have e2 : (d1 * d2) • w = d1 • (d2 • w) := by rw [mul_smul]
      rw [smul_add, e1, e2]
      exact M.add_mem (M.smul_mem _ h1) (M.smul_mem _ h2)
    | smul k w _ hw =>
      obtain ⟨d, hd, h1⟩ := hw
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) k
      refine ⟨b * d, mul_mem hb hd, ?_⟩
      have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have e : (b * d) • ((algebraMap A K a / algebraMap A K b) • w) = a • (d • w) := by
        rw [← algebraMap_smul K (b * d), smul_smul, smul_smul a d w, ← algebraMap_smul K (a * d) w]
        congr 1
        rw [map_mul, map_mul]
        field_simp
      rw [e]
      exact M.smul_mem a h1
  letI := hlat
  obtain ⟨d, hd, hdx⟩ := hden x (by rw [Submodule.IsFullLattice.span_eq_top]; trivial)
  have hd0' : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨σ, hσ⟩ := hproj.out
  set z : M := ⟨d • x, hdx⟩ with hzdef
  have hdiv : ∀ m : M, ∃ c : A, σ z m = d * c := by
    intro m
    have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
        ∃ c : A, s • (algebraMap A K (σ z m) / algebraMap A K d) = algebraMap A K c := by
      intro q hq hh
      obtain ⟨s, hs, hsx⟩ := hloc q hq hh
      refine ⟨s, hs, σ ⟨s • x, hsx⟩ m, ?_⟩
      have hz : s • z = d • (⟨s • x, hsx⟩ : M) := Subtype.ext (smul_comm s d x)
      have hm : s * σ z m = d * σ ⟨s • x, hsx⟩ m := by
        have h' := congrArg (fun f => f m) (congrArg σ hz)
        simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hm, map_mul]
      field_simp
    obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := K) _ hl
    refine ⟨c, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hc]
    field_simp
  choose c hc using hdiv
  have hyM : (∑ m ∈ (σ z).support, c m • (m : Ω)) ∈ M :=
    M.sum_mem (fun m _ => M.smul_mem _ m.2)
  have hsum : (∑ m ∈ (σ z).support, (σ z m) • (m : Ω)) = (z : Ω) := by
    have h1 := congrArg Subtype.val (hσ z)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h1
    simpa using h1
  have hzy : d • (∑ m ∈ (σ z).support, c m • (m : Ω)) = d • x := by
    rw [Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hsum
    rw [hc m, mul_smul]
  have hcancel : ∀ u w : Ω, d • u = d • w → u = w := by
    intro u w huw
    have h1 : (algebraMap A K d) • u = (algebraMap A K d) • w := by
      rw [algebraMap_smul, algebraMap_smul]
      exact huw
    have h2 : (algebraMap A K d)⁻¹ • ((algebraMap A K d) • u) =
        (algebraMap A K d)⁻¹ • ((algebraMap A K d) • w) := by rw [h1]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hd0', one_smul, one_smul] at h2
    exact h2
  rw [← hcancel _ _ hzy]
  exact hyM

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a t : A} (ha : a ≠ 0)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ a ∣ s * t) : a ∣ t := by
  classical
  have ha' : algebraMap A (FractionRing A) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha
  have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
      ∃ c : A, s • (algebraMap A (FractionRing A) t / algebraMap A (FractionRing A) a) =
        algebraMap A (FractionRing A) c := by
    intro q hq hh
    obtain ⟨s, hs, u, hu⟩ := h q hq hh
    refine ⟨s, hs, u, ?_⟩
    rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hu, map_mul]
    field_simp
  obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := FractionRing A) _ hl
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc]
  field_simp

theorem smul_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {M : Type} [AddCommGroup M] [Module A M] [Module.Projective A M]
    {a : A} (ha : a ≠ 0) (x : M)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ ∃ y : M, s • x = a • y) :
    ∃ y : M, x = a • y := by
  classical
  obtain ⟨σ, hσ⟩ := ‹Module.Projective A M›.out
  have hdiv : ∀ m : M, a ∣ σ x m := by
    intro m
    refine dvd_of_height_one ha (fun q hq hh => ?_)
    obtain ⟨s, hs, y, hy⟩ := h q hq hh
    refine ⟨s, hs, σ y m, ?_⟩
    have h' := congrArg (fun f => f m) (congrArg σ hy)
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
  choose c hc using hdiv
  refine ⟨∑ m ∈ (σ x).support, c m • m, ?_⟩
  conv_lhs => rw [← hσ x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [hc m, mul_smul, id_eq]

theorem test_div : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x a b _ hproj hx ha hab hloc
  have hloc' : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ y : M, s • (⟨x, hx⟩ : M) = a • y := by
    intro q hq hh
    by_cases hb : b ∈ q
    · obtain ⟨s, hs, y, hy, hsy⟩ := hloc q hq hh hb
      exact ⟨s, hs, ⟨y, hy⟩, Subtype.ext hsy⟩
    · exact ⟨a, fun haq => hb (hab q hq haq), ⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy⟩ := smul_of_height_one ha (⟨x, hx⟩ : M) hloc'
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GeFrame
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Ge

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

noncomputable def qL (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem qL_apply (σ : E →+* K) (x : Fin N → A) : qL D σ x = D.q σ x := rfl

theorem frame_expand {σ : E →+* K} {m j k : ℕ}
    {i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) A (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) A} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → A) (t : Fin k → A) (y : Ω) (hy : y ∈ D.omHT σ)
    (e : D.q σ x = ∑ a, t a • (bM a : Ω) + ((p : A) ^ m) • y) :
    ∃ (s : Fin j → A) (z : Fin N → A), x = g.mulVec (Sum.elim s t) + ((p : A) ^ m) • z := by
  obtain ⟨hcol1, hcol2⟩ := hg
  choose x'' hx'' using hcol1
  choose yM hyM hq using hcol2
  have hx1 : ∃ y₁ ∈ D.omHT σ, D.q σ (x - ∑ a, t a • (fun l => g l (Sum.inr a))) = ((p : A) ^ m) • y₁ := by
    refine ⟨y - ∑ a, t a • yM a, ?_, ?_⟩
    · exact Submodule.sub_mem _ hy (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hyM a))
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← qL_apply, map_sub, map_sum]
      simp only [map_smul, qL_apply, hq, e, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
      simp only [smul_comm (t _) ((p : A) ^ m)]
      abel
  obtain ⟨w, x', hw⟩ := (hex.2.1 _).1 hx1
  refine ⟨bW.repr w, x' - ∑ b, bW.repr w b • x'' b, ?_⟩
  have hiw : i w = ∑ b, bW.repr w b • i (bW b) := by
    conv_lhs => rw [← bW.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  have hcolL : ∀ b, i (bW b) = (fun l => g l (Sum.inl b)) - ((p : A) ^ m) • x'' b := fun b => by
    rw [hx'' b]
    abel
  have hx : x = ∑ a, t a • (fun l => g l (Sum.inr a)) + i w + ((p : A) ^ m) • x' := by
    rw [add_assoc, ← hw]
    abel
  rw [hx, hiw]
  simp only [hcolL]
  ext l
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  ring_nf
  have s1 : ∑ x, g l (Sum.inl x) * (bW.repr w) x = ∑ x, (bW.repr w) x * g l (Sum.inl x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s2 : ∑ x, g l (Sum.inr x) * t x = ∑ x, t x * g l (Sum.inr x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s3 : ∑ x, (p : A) ^ m * (bW.repr w) x * x'' x l = ∑ x, (bW.repr w) x * (p : A) ^ m * x'' x l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2, s3]
  ring

end

theorem frame_exists : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (m j k : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))) (bM : Basis (Fin k) A (D.omHT σ)) (eqv : Fin j ⊕ Fin k ≃ Fin N), (∀ x, D.q σ x ∈ D.omHT σ) → D.ExactMod σ m i → (∃ g, D.IsFrame σ m i bW bM g) ∧ ∀ g, D.IsFrame σ m i bW bM g → ∃ h r : A, (g.submatrix id eqv.symm).det * h = 1 + (p : A) ^ m * r := by
  intro A K _ _ _ _ _ E _ _ c _ p R N _ Ω _ _ _ _ D σ m j k i bW bM eqv hqM hex
  refine ⟨?_, fun g hg => ?_⟩
  · have h3 : ∀ a : Fin k, ∃ x : Fin N → A, ∃ y ∈ D.omHT σ, D.q σ x = (bM a : Ω) + ((p : A) ^ m) • y := by
      intro a
      obtain ⟨x, y', hy', he⟩ := hex.2.2 (bM a) (bM a).2
      refine ⟨x, -y', Submodule.neg_mem _ hy', ?_⟩
      rw [he, smul_neg]
      abel
    choose xs ys hys hxs using h3
    refine ⟨Matrix.of fun l c => Sum.elim (fun a => i (bW a) l) (fun a => xs a l) c, fun a => ⟨0, ?_⟩,
      fun a => ⟨ys a, hys a, ?_⟩⟩
    · funext l
      simp
    · simpa using hxs a
  · have hsurj : ∀ x : Fin N → A, ∃ v : Fin j ⊕ Fin k → A, ∃ z : Fin N → A,
        x = g.mulVec v + ((p : A) ^ m) • z := by
      intro x
      obtain ⟨s, z, hz⟩ := frame_expand D hex hg x (bM.repr ⟨D.q σ x, hqM x⟩) 0 (Submodule.zero_mem _) (by
        rw [smul_zero, add_zero]
        have h5 := congrArg Subtype.val (bM.sum_repr ⟨D.q σ x, hqM x⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h5
        exact h5.symm)
      exact ⟨_, z, hz⟩
    choose v z hvz using fun l : Fin N => hsurj (Pi.single l 1)
    have hprod : g.submatrix id eqv.symm * Matrix.of (fun c l => v l (eqv.symm c)) =
        1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) := by
      ext l l'
      rw [Matrix.mul_apply]
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply]
      have e1 : ∑ c, g l (eqv.symm c) * v l' (eqv.symm c) = (g.mulVec (v l')) l := by
        rw [Matrix.mulVec, dotProduct]
        exact Equiv.sum_comp eqv.symm (fun d => g l d * v l' d)
      rw [e1, eq_sub_of_add_eq (hvz l').symm]
      simp [Matrix.one_apply, Pi.single_apply]
    have hmem : (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A).det - 1 ∈
        Ideal.span {((p : A) ^ m)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
      have e2 : (Ideal.Quotient.mk (Ideal.span {((p : A) ^ m)})).mapMatrix
          (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A) = 1 := by
        ext a b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
          map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, sub_zero,
          Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, Matrix.det_one]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨(Matrix.of (fun c l => v l (eqv.symm c)) : Matrix (Fin N) (Fin N) A).det, r, ?_⟩
    rw [← Matrix.det_mul, hprod]
    linear_combination (-1 : A) * hr

end PositivityTheory.HtPt.Ge
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GeneratesDiffMap
section
noncomputable section

namespace PositivityTheory.HtPt.Gb

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  {D : HTChart A K c p R N Ω}
  {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
  {φ : A →+* O} {P : HTPoint C O c κ' N V Ω'} {ι : D.om →ₛₗ[φ] Ω'}

theorem om'_le_om (D : HTChart A K c p R N Ω) : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem_om' (D : HTChart A K c p R N Ω) {x : Ω} (hx : x ∈ D.om) :
    (p : A) ^ R • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem span_om' (hred : D.ReducesTo φ P ι) (hκ : κ' ∣ (p : O) ^ R) :
    Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) = P.om' := by
  have hn : ∀ y : Ω', (p ^ R) • y = (p : O) ^ R • y := fun y => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hι : ∀ x : D.om, ι ((p : A) ^ R • x) = (p : O) ^ R • ι x := fun x => by
    rw [ι.map_smulₛₗ, map_pow, map_natCast]
  have a1 : ∀ y ∈ P.om, (p : O) ^ R • y ∈ P.om' := by
    intro y hy
    obtain ⟨w, hw⟩ := hκ
    obtain ⟨x, hx, e⟩ := P.κ_mem _ (P.om.smul_mem w hy)
    exact ⟨x, hx, by rw [hw, mul_smul]; exact e⟩
  have a2 : ∀ y ∈ P.om, (p : O) ^ R • y ∈
      Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
    intro y hy
    rw [← hred.span_eq] at hy
    have : Submodule.span O (Set.range ι) ≤ (Submodule.span O
        (ι '' {x : D.om | (x : Ω) ∈ D.om'})).comap ((p : O) ^ R • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span ⟨(p : A) ^ R • x, pow_smul_mem_om' D x.2, hι x⟩
    exact this hy
  have ht : ∀ x, P.tate x ∈ P.T := by
    intro x
    refine P.T.sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (RingOfIntegers.basis E).sum_repr (x i), map_sum, LinearMap.sum_apply]
    refine P.T.sum_mem fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    rw [P.free.2.2]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  apply le_antisymm
  · have h : D.om' ≤ (P.om'.comap ι).map D.om.subtype := by
      refine sup_le (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨x, rfl⟩
        refine ⟨⟨D.h x, D.h_mem x⟩, ?_, rfl⟩
        obtain ⟨y, hy, e⟩ := hred.ht_eq x
        change ι _ ∈ P.om'
        rw [e, hn]
        exact P.om'.add_mem ⟨_, ht x, rfl⟩ (a1 y hy)
      · rintro _ ⟨x, hx, rfl⟩
        refine ⟨(p : A) ^ R • ⟨x, hx⟩, ?_, rfl⟩
        change ι _ ∈ P.om'
        rw [hι]
        refine a1 _ ?_
        rw [← hred.span_eq]
        exact Submodule.subset_span ⟨_, rfl⟩
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', e⟩ := h hx
    rw [← (Subtype.ext e : x' = x)]
    exact hx'
  · rw [HTPoint.om', Submodule.map_le_iff_le_comap]
    conv_lhs => rw [P.free.2.2]
    rw [Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    have e0 : P.ρ (RingOfIntegers.basis E k) (P.t i) =
        P.tate (Pi.single i (RingOfIntegers.basis E k)) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    obtain ⟨y, hy, e⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ Submodule.span O _
    rw [e0, eq_sub_of_add_eq e.symm, hn]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, Submodule.mem_sup_left
      (Submodule.subset_span ⟨_, rfl⟩), rfl⟩) (a2 y hy)

omit [NumberField E] in
theorem transfer_mul [NumberField E] (hAK : Function.Injective (algebraMap A K)) {σ : E →+* K}
    {σ' : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (hφ : ∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E))
    {d a' : A} {e : E} (h : algebraMap A K a' = algebraMap A K d * σ e) :
    algebraMap O C (φ a') = algebraMap O C (φ d) * σ' e := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨α, hα⟩ := hσ a
  obtain ⟨β, hβ⟩ := hσ b
  have h1 : a' * β = d * α := hAK (by
    rw [map_mul, map_mul, h, hα, hβ, map_div₀, mul_assoc,
      div_mul_cancel₀ _ ((map_ne_zero σ).2 hb0)])
  have h2 := congrArg (fun t => algebraMap O C (φ t)) h1
  simp only [map_mul, hφ a α hα, hφ b β hβ] at h2
  rw [map_div₀, ← mul_div_assoc, eq_div_iff ((map_ne_zero σ').2 hb0)]
  exact h2

theorem generatesDiff_map (hAK : Function.Injective (algebraMap A K)) {σ : E →+* K}
    {σ' : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range)
    (hφ : ∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E))
    {d : A} (hd : GeneratesDiff σ d) : GeneratesDiff σ' (φ d) := by
  apply le_antisymm
  · have key : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        ∃ a', algebraMap A K a' = y ∧ algebraMap O C (φ a') ∈
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ' (x : E)} := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨x, hx, rfl⟩ := h
        obtain ⟨a', ha'⟩ := hσ x
        exact ⟨a', ha', Submodule.subset_span ⟨x, hx, hφ x a' ha'⟩⟩
      | zero => exact ⟨0, map_zero _, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, ha'⟩ := hy
        obtain ⟨b, hb, hb'⟩ := hz
        exact ⟨a + b, by rw [map_add (f := _), ha, hb], by
          rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ ha' hb'⟩
      | smul r y _ hy =>
        obtain ⟨a, ha, ha'⟩ := hy
        exact ⟨r * a, by rw [map_mul, ha, Algebra.smul_def], by
          rw [map_mul, map_mul, ← Algebra.smul_def]; exact Submodule.smul_mem _ _ ha'⟩
    obtain ⟨a', ha, ha'⟩ := key _ (hd.le (Submodule.mem_span_singleton_self _))
    rw [hAK ha] at ha'
    exact (Submodule.span_singleton_le_iff_mem _ _).2 ha'
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hd.ge (Submodule.subset_span ⟨x, hx, rfl⟩))
    refine Submodule.mem_span_singleton.2 ⟨φ a, ?_⟩
    rw [← hφ x (a * d) (by rw [map_mul, ← ha, Algebra.smul_def]), map_mul, map_mul,
      Algebra.smul_def]

theorem smul_eigProj_eq (ρ : 𝓞 E →+* Module.End K Ω) {σ : E →+* K} {d : A}
    {cc : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A}
    (h : ∀ k, algebraMap A K (cc k) = algebraMap A K d * σ (dualInt E k)) (x : Ω) :
    d • eigProj ρ σ x = ∑ k, cc k • ρ (RingOfIntegers.basis E k) x := by
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul K (cc k), h, mul_smul, algebraMap_smul]

theorem span_eigQuot {σ : E →+* K} {σ' : E →+* C} {d : A}
    (h1 : ∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om)
    (h2 : ∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x → ι y = φ d • eigProj P.ρΩ σ' (ι x))
    {X : Submodule A Ω} (hX : X ≤ D.om) {X' : Submodule O Ω'}
    (hs : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ X}) = X') :
    Submodule.span O (ι '' {y : D.om | ∃ z ∈ eigQuot D.ρΩ σ X, (y : Ω) = d • z}) =
      (eigQuot P.ρΩ σ' X').map (φ d • LinearMap.id) := by
  rw [eigQuot, eigQuot, ← Submodule.map_comp, ← hs, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨y, ⟨_, ⟨x, hx, rfl⟩, e⟩, rfl⟩
    exact ⟨_, ⟨⟨x, hX hx⟩, hx, rfl⟩, (h2 ⟨x, hX hx⟩ y e).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨⟨_, h1 x x.2⟩, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, h2 x _ rfl⟩

end

theorem red_proj : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (φ a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → GeneratesDiff σ' (φ d) ∧ (∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om) ∧ (∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x → ι y = φ d • eigProj P.ρΩ σ' (ι x)) ∧ Submodule.span O (ι '' {y : D.om | ∃ z ∈ D.omHT σ, (y : Ω) = d • z}) = (P.omHT σ').map (φ d • LinearMap.id) ∧ Submodule.span O (ι '' {y : D.om | ∃ z ∈ eigQuot D.ρΩ σ D.om, (y : Ω) = d • z}) = (P.omRec σ').map (φ d • LinearMap.id) := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D C _ _ _ v O _ _ hv κ' V _ _ _ _ Ω' _ _ _ _
    φ P ι hred σ σ' d hσ hφ hd hκ
  obtain ⟨-, hcc, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose cc hcc using hcc
  have h1 : ∀ x ∈ D.om, d • eigProj D.ρΩ σ x ∈ D.om := by
    intro x hx
    rw [smul_eigProj_eq _ hcc]
    exact D.om.sum_mem fun k _ => D.om.smul_mem _ (D.om_stable _ x hx)
  have h2 : ∀ (x y : D.om), (y : Ω) = d • eigProj D.ρΩ σ x →
      ι y = φ d • eigProj P.ρΩ σ' (ι x) := by
    intro x y e
    have hy : y = ∑ k, cc k • (⟨D.ρΩ (RingOfIntegers.basis E k) x, D.om_stable _ x x.2⟩ : D.om) := by
      apply Subtype.ext
      rw [e, smul_eigProj_eq _ hcc]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum, smul_eigProj_eq (cc := fun k => φ (cc k)) _
      (fun k => transfer_mul hAK hσ hφ (hcc k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ι.map_smulₛₗ, hred.lin]
  refine ⟨generatesDiff_map hAK hσ hφ hd, h1, h2,
    span_eigQuot h1 h2 (om'_le_om D) (span_om' hred hκ), span_eigQuot h1 h2 le_rfl ?_⟩
  rw [← hred.span_eq]
  congr 1
  ext w
  simp

end PositivityTheory.HtPt.Gb
end
end

