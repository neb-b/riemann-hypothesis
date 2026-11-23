module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0018
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GdDual
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcChart
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem {x : Ω} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem ht_mem_span {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι)
    {t : V} (ht : t ∈ P.T) :
    P.ht t ∈ Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
  classical
  set S := Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'})
  have hp : ∀ y ∈ P.om, (p ^ R) • y ∈ S := by
    intro y hy
    rw [← hred.span_eq] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      refine Submodule.subset_span ⟨(p ^ R) • m, ?_, map_nsmul ι _ _⟩
      have := pow_smul_mem D m.2
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
      exact this
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact S.add_mem ha hb
    | smul a w _ hw => rw [smul_comm]; exact S.smul_mem a hw
  have hT : P.T ≤ S.comap (P.ht.restrictScalars O) := by
    rw [P.free.2.2, Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    have h1 : P.tate (Pi.single i (RingOfIntegers.basis E k)) =
        P.ρ (RingOfIntegers.basis E k) (P.t i) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at he
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ S
    rw [← sub_eq_iff_eq_add.2 he]
    exact S.sub_mem (Submodule.subset_span ⟨_, h_mem_om' D _, rfl⟩) (hp y hy)
  exact hT ht

end

theorem chart_ii : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ hκ hP hT
  refine ⟨om'_le D, fun x hx => ?_⟩
  have hp0 : algebraMap A K ((p : A) ^ R) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hlat : D.om'.IsFullLattice K := by
    letI : D.om'.IsLattice K :=
      Submodule.IsLattice.of_fg K (Submodule.FG.of_le D.om_lat.fg (om'_le D))
    refine ⟨?_⟩
    apply top_unique
    rw [← D.om_lat.span_eq_top]
    apply Submodule.span_le.2
    intro x hx
    have hh := Submodule.subset_span (R := K) (pow_smul_mem D hx)
    rw [← IsScalarTower.algebraMap_smul K] at hh
    have hh' := (Submodule.span K (D.om' : Set Ω)).smul_mem
      (algebraMap A K ((p : A) ^ R))⁻¹ hh
    simpa [smul_smul, hp0] using hh'
  refine test_incl A K Ω D.om' _ hlat hP fun q hq h1 => ?_
  by_cases hpq : (p : A) ∈ q
  swap
  · refine ⟨(p : A) ^ R, fun h => hpq (hq.mem_of_pow_mem R h), ?_⟩
    exact pow_smul_mem D (D.om.smul_mem κ hx)
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    hT q hq h1 hpq
  letI : Algebra A O := φ.toAlgebra
  obtain ⟨j, hj, -, hj1⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  obtain ⟨s, hs, hsx⟩ := test_descend A K C v O hv q D.om (D.om'.comap D.om.subtype)
    (κ • ⟨x, hx⟩) hq h1 hφ hcen (by
      obtain ⟨t, ht, hte⟩ := P.κ_mem (ι ⟨x, hx⟩)
        (hred.span_eq ▸ Submodule.subset_span ⟨_, rfl⟩)
      have h2 := ht_mem_span D φ P ι hred ht
      rw [hte, ← ι.map_smulₛₗ, ← hj1] at h2
      have h3 : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) =
          (Submodule.span O ((fun y : D.om => (1 : O) ⊗ₜ[A] y) ''
            (D.om'.comap D.om.subtype : Set D.om))).map j := by
        rw [Submodule.map_span, Set.image_image]
        simp only [hj1]
        rfl
      rw [h3] at h2
      obtain ⟨z, hz, hze⟩ := h2
      rwa [← hj hze])
  exact ⟨s, hs, hsx⟩

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GdChart
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

section SlopeTestRemainingChoices

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {C O : Type} [Field C] [CommRing O]
  [Algebra O C] {E : Type} [Field E] [NumberField E]

theorem map_mem_span (φ : A →+* O) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) {S : Set K} {S' : Set C}
    (hS : ∀ x ∈ S, ψ x ∈ S') {x : K} (hx : x ∈ Submodule.span A S) : ψ x ∈ Submodule.span O S' := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hS x hx)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, map_mul, h, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem generatesDiff_map (φ : A →+* O) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) {σ : E →+* K} {d : A}
    (hd : GeneratesDiff σ d) : GeneratesDiff (ψ.comp σ) (φ d) := by
  unfold GeneratesDiff at hd ⊢
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, ← h]
    refine map_mem_span φ ψ h ?_ (hd.le (Submodule.mem_span_singleton_self _))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_span φ ψ h ?_ (hd.ge (Submodule.subset_span ⟨x, hx, rfl⟩))
    rintro _ rfl
    exact h d

theorem emb_mem [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A K] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range :=
  IsIntegrallyClosed.isIntegral_iff.1
    ((map_isIntegral_int σ (RingOfIntegers.isIntegral_coe a)).tower_top)

variable {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Ω' : Type} [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

theorem qgen_mem (σ : E →+* K) (l : Fin N) :
    eigProj D.ρΩ σ (D.h (Pi.single l 1)) ∈ D.omHT σ :=
  ⟨_, Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩), rfl⟩

theorem omHT_fg [IsNoetherianRing A] (σ : E →+* K) : (D.omHT σ).FG := by
  refine Submodule.FG.map _ (Submodule.FG.of_le D.om_lat.fg (sup_le ?_ ?_))
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem tate_single {κ : O} (P : HTPoint C O c κ N V Ω') (l : Fin N) (a : 𝓞 E) :
    P.tate (Pi.single l a) = P.ρ a (P.t l) := by
  rw [HTPoint.tate, Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

variable [CharZero K] [CharZero C] {κ : O} {P : HTPoint C O c κ N V Ω'} {φ : A →+* O}
  {ι : D.om →ₛₗ[φ] Ω'}

theorem gen_at_point (hAK : Function.Injective (algebraMap A K))
    (hOC : Function.Injective (algebraMap O C)) (hφ : Function.Injective φ) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) (hred : D.ReducesTo φ P ι)
    {σ : E →+* K} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) {d : A}
    (hd : GeneratesDiff σ d) {π : O} (hπ : κ * π ∣ (p : O) ^ R) (J : D.omHT σ → Ω')
    (hJ : ∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → φ d • J z = ι y) (l : Fin N) :
    ∃ y ∈ P.omHT (ψ.comp σ), J ⟨_, qgen_mem D σ l⟩ =
      eigProj P.ρΩ (ψ.comp σ) (P.ht (P.t l)) + π • y := by
  obtain ⟨hd0, hdk, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose u hu using hdk
  let y0 : D.om := ⟨D.h (Pi.single l 1), D.h_mem _⟩
  let y : D.om := ∑ k, u k • ⟨D.ρΩ (RingOfIntegers.basis E k) y0, D.om_stable _ _ y0.2⟩
  have h1 := hJ ⟨_, qgen_mem D σ l⟩ y (by
    simp only [y, eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
      Submodule.coe_sum, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (u k), hu, ← algebraMap_smul K d, smul_smul])
  have h2 : ι y = φ d • eigProj P.ρΩ (ψ.comp σ) (ι y0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, eigProj, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_sum,
      LinearMap.map_smulₛₗ, hred.lin]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul C (φ (u k)), ← h, hu, ← algebraMap_smul C (φ d), smul_smul, map_mul, h]
    rfl
  have hd1 : algebraMap O C (φ d) ≠ 0 := by
    rw [← h]
    exact (map_ne_zero ψ).2 hd0
  have h3 : J ⟨_, qgen_mem D σ l⟩ = eigProj P.ρΩ (ψ.comp σ) (ι y0) := by
    rw [h2, ← algebraMap_smul C (φ d), ← algebraMap_smul C (φ d)] at h1
    exact smul_right_injective Ω' hd1 h1
  obtain ⟨y1, hy1, e1⟩ := hred.ht_eq (Pi.single l 1)
  obtain ⟨x1, hx1, e2⟩ := P.κ_mem y1 hy1
  obtain ⟨r, hr⟩ := hπ
  refine ⟨r • eigProj P.ρΩ (ψ.comp σ) (P.ht x1), Submodule.smul_mem _ _ (proj_ht_mem P _ hx1), ?_⟩
  rw [h3, e1, tate_single, map_one, Module.End.one_apply, map_add (f := _), e2, ← Nat.cast_smul_eq_nsmul O,
    Nat.cast_pow, hr, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, smul_smul, smul_smul]
  congr 2
  ring

theorem gram_at_point (hAK : Function.Injective (algebraMap A K)) (ψ : K →+* C)
    (h : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a)) (hred : D.ReducesTo φ P ι)
    {σ : E →+* K} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) {d : A}
    (hd : GeneratesDiff σ d) (l j : Fin N) :
    ∃ z : O, P.e (φ d • eigProj P.ρ (ψ.comp σ) (P.t l)) (P.t j) =
      ψ (D.gram σ d l j) + algebraMap O C ((p : O) ^ R * z) := by
  obtain ⟨-, hdk, -⟩ := different_generator_dualInt A K E σ d hAK hσ hd
  choose u hu using hdk
  choose z hz using hred.e_eq
  refine ⟨∑ k, φ (u k) * z (Pi.single l (RingOfIntegers.basis E k)) (Pi.single j 1), ?_⟩
  rw [← algebraMap_smul C (φ d)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eigProj, HTChart.gram, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, map_sum,
    map_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 := hz (Pi.single l (RingOfIntegers.basis E k)) (Pi.single j 1)
  rw [tate_single, tate_single, map_one, Module.End.one_apply] at h1
  have h2 := congrArg ψ (hu k)
  rw [h, map_mul, h] at h2
  simp only [h1, smul_eq_mul, map_mul, map_add (f := _), map_natCast, h, h2, RingHom.comp_apply]
  ring

end SlopeTestRemainingChoices

theorem chart_comp_zero_of
    (hdiv : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y)
    (hdesc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L)
    (hbc : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (κ' : O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω' : Type) [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω'] (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[algebraMap A O] Ω') (hred : D.ReducesTo (algebraMap A O) P ι) (σ : E →+* K) (σ' : E →+* C) (d : A), (∀ (a : 𝓞 E) (a' : A), algebraMap A K a' = σ (a : E) → algebraMap O C (algebraMap A O a') = σ' (a : E)) → GeneratesDiff σ d → κ' ∣ (p : O) ^ R → Module.Projective A (D.omHT σ) → ∃ j : O ⊗[A] (D.omHT σ) →ₗ[O] Ω', Function.Injective j ∧ LinearMap.range j = P.omHT σ' ∧ (∀ (z : D.omHT σ) (y : D.om), (y : Ω) = d • (z : Ω) → algebraMap A O d • j (1 ⊗ₜ z) = ι y) ∧ Module.finrank A (D.omHT σ) = Module.finrank C (P.Ωsp σ')) :
    ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ σ d d' m i hκ hd hd' _ hP hP' htest hi w
  have hAK := IsFractionRing.injective A K
  have hq : D.q σ (i w) ∈ D.omHT σ :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (qgen_mem D σ l)
  refine hdiv A K Ω (D.omHT σ) _ ((p : A) ^ m) (p : A) (omHT_fg D σ) hP hq ?_
    (fun 𝔮 h𝔮 h => h𝔮.mem_of_pow_mem m h) fun 𝔮 h𝔮 hht hp𝔮 => ?_
  · refine pow_ne_zero _ fun h0 => hp.out.ne_zero ?_
    have := congrArg (algebraMap A K) h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    htest 𝔮 h𝔮 hht hp𝔮
  letI : Algebra A O := φ.toAlgebra
  have hOC := hv.hom_inj
  let ψ : K →+* C := IsFractionRing.lift (g := (algebraMap O C).comp φ) (hOC.comp hφ)
  have hψ : ∀ a, ψ (algebraMap A K a) = algebraMap O C (φ a) := fun a => IsFractionRing.lift_algebraMap _ a
  have hκ' : φ κ * (p : O) ^ m ∣ (p : O) ^ R := by
    simpa using map_dvd φ hκ
  have hcomp : ∀ (τ : E →+* K) (a : 𝓞 E) (a' : A), algebraMap A K a' = τ (a : E) →
      algebraMap O C (algebraMap A O a') = (ψ.comp τ) (a : E) := fun τ a a' h => by
    rw [RingHom.comp_apply, ← h, hψ]
    rfl
  obtain ⟨j, hjinj, hjr, hj, -⟩ := hbc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred σ (ψ.comp σ) d
    (hcomp σ) hd (dvd_of_mul_right_dvd hκ') hP
  obtain ⟨j', hjinj', hjr', hj', -⟩ := hbc A K E c hc p R N Ω D C v O hv (φ κ) V Ω' P ι hred
    (σ.comp c.toRingHom) ((ψ.comp σ).comp c.toRingHom) d'
    (hcomp _) hd' (dvd_of_mul_right_dvd hκ') hP'
  choose y hy ey using gen_at_point D hAK hOC hφ ψ hψ hred (emb_mem σ) hd hκ' (fun z => j (1 ⊗ₜ z)) hj
  choose y' hy' ey' using gen_at_point D hAK hOC hφ ψ hψ hred (emb_mem _) hd' hκ'
    (fun z => j' (1 ⊗ₜ z)) hj'
  let eq' : (O ⊗[A] D.omHT (σ.comp c.toRingHom)) ≃ₗ[O] P.omHT ((ψ.comp σ).comp c.toRingHom) :=
    (LinearEquiv.ofInjective j' hjinj').trans (LinearEquiv.ofEq _ _ hjr')
  let wO : O ⊗[A] D.omHT (σ.comp c.toRingHom) →ₗ[O] O :=
    LinearMap.liftBaseChange O (Algebra.linearMap A O ∘ₗ w)
  let f : P.omHT ((ψ.comp σ).comp c.toRingHom) →ₗ[O] O := wO ∘ₗ eq'.symm.toLinearMap
  have hf : ∀ z, f (eq' (1 ⊗ₜ z)) = φ (w z) := fun z => by
    simp only [f, wO, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  obtain ⟨w', hw', ew'⟩ := exists_alt_bis hv hc P (ψ.comp σ) f
  have htT : ∀ l, P.t l ∈ P.T := fun l => by
    have h1 : P.t l = P.ρ 1 (P.t l) := by simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, ← (RingOfIntegers.basis E).sum_repr 1, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    refine zsmul_mem ?_ _
    rw [P.free.2.2]
    exact Submodule.subset_span ⟨(l, k), rfl⟩
  obtain ⟨y1, hy1, e1⟩ := pt_comp_zero C v O hv E c hc (φ κ) N V Ω' P (ψ.comp σ) (φ d) ((p : O) ^ m)
    (fun l => φ (i w l)) w' (generatesDiff_map φ ψ hψ hd) hw' (fun l => by
      choose z hz using gram_at_point D hAK ψ hψ hred (emb_mem σ) hd
      obtain ⟨z1, hz1⟩ := hi w l ⟨_, qgen_mem D _ l⟩ rfl
      obtain ⟨r, hr⟩ := dvd_of_mul_left_dvd hκ'
      have h1 : eq' (1 ⊗ₜ ⟨_, qgen_mem D _ l⟩) = ⟨_, proj_ht_mem P _ (htT l)⟩ +
          ((p : O) ^ m) • ⟨y' l, hy' l⟩ := Subtype.ext (ey' l)
      have h2 := hf ⟨_, qgen_mem D _ l⟩
      rw [h1, map_add (f := _), map_smul] at h2
      have h3 := congrArg ψ hz1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hψ, map_add (f := _), map_mul, map_pow, map_natCast, ← h2, map_sum] at h3
      refine ⟨f ⟨y' l, hy' l⟩ + φ z1 + ∑ k, φ (i w k) * (r * z k l), ?_⟩
      simp only [hz, ew' _ (htT l), mul_add, Finset.sum_add_distrib, map_mul, hψ, hr] at h3 ⊢
      rw [h3]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, map_sum, smul_eq_mul, Finset.mul_sum, add_assoc]
      congr 3
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)
  have h2 : j (1 ⊗ₜ ⟨_, hq⟩) = ((p : O) ^ m) • (y1 + ∑ l, φ (i w l) • y l) := by
    have : (⟨_, hq⟩ : D.omHT σ) = ∑ l, i w l • ⟨_, qgen_mem D σ l⟩ := Subtype.ext (by
      simp [HTChart.q])
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, TensorProduct.tmul_sum, map_sum, smul_add, ← e1, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul O (i w l), map_smul, ey, smul_add, smul_comm]
    rfl
  have h3 : y1 + ∑ l, φ (i w l) • y l ∈ LinearMap.range j := by
    rw [hjr]
    exact Submodule.add_mem _ hy1 (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hy l))
  obtain ⟨t, ht⟩ := h3
  rw [← ht, ← map_smul] at h2
  have h4 := hjinj h2
  obtain ⟨s, hs, u, hu⟩ := hdesc A K C v O hv 𝔮 (D.omHT σ)
    (LinearMap.range (((p : A) ^ m) • LinearMap.id)) ⟨_, hq⟩ h𝔮 hht hφ hcen (by
      rw [h4]
      clear h4 h2 ht
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | tmul a b =>
        have : ((p : O) ^ m) • (a ⊗ₜ[A] b) = a • ((1 : O) ⊗ₜ[A] (((p : A) ^ m) • b)) := by
          rw [TensorProduct.tmul_smul, ← algebraMap_smul O ((p : A) ^ m), map_pow, map_natCast,
            smul_comm, TensorProduct.smul_tmul' a, smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨b, rfl⟩, rfl⟩))
  exact ⟨s, hs, u, u.2, (congrArg Subtype.val hu).symm⟩

end PositivityTheory.HtPt.Gd
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinExists
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinExists

theorem join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ i κ' _ w hi ⟨l, hl⟩ hcl
  let p : Cpt M.ξ := ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hic : i (x c) ≠ 0 := (map_ne_zero i).2 hc.1
  have hJ : joinCo i x w (c, l) ≠ 0 := mul_ne_zero hic hl
  have hgen : ∀ j l', joinCo i x w (j, l') / joinCo i x w (c, l) ∈ chRing o (joinCo i x w) (c, l) :=
    fun j l' => Algebra.subset_adjoin ⟨(j, l'), rfl⟩
  have hmap : ∀ a ∈ chRing o x c, i a ∈ chRing o (joinCo i x w) (c, l) := by
    intro a ha
    have ha' : a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := ha
    induction ha' using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have : i (x j / x c) = joinCo i x w (j, l) / joinCo i x w (c, l) := by
        simp only [joinCo, map_div₀]
        rw [mul_div_mul_right _ _ hl]
      rw [this]
      exact hgen _ _
    | algebraMap r =>
      rw [hi]
      exact Subalgebra.algebraMap_mem _ r
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact add_mem (hy (by assumption)) (hz (by assumption))
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem (hy (by assumption)) (hz (by assumption))
  have hAF : ∀ a ∈ chRing o (joinCo i x w) (c, l),
      a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
    fun a ha => Subfield.subset_closure ha
  have hiF : ∀ a : Ω, i a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    intro a
    have h2 := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).2
    have key : ∀ b ∈ regAt M.ξ p, i b ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
      intro b hb
      obtain ⟨s, hs, t, ht, -, rfl⟩ := (h2 b).1 hb
      rw [map_div₀]
      exact div_mem (hAF _ (hmap _ hs)) (hAF _ (hmap _ ht))
    obtain ⟨u, hu, v, hv, -, rfl⟩ := (PositivityTheory.HtPt.Ma.reg_local M.X Ω M.ξ).2.2 M.tie.gen p a
    rw [map_div₀]
    exact div_mem (key u hu) (key v hv)
  have hw : ∀ l', w l' / w l ∈ chRing o (joinCo i x w) (c, l) := by
    intro l'
    have : w l' / w l = joinCo i x w (c, l') / joinCo i x w (c, l) := by
      simp only [joinCo]
      rw [mul_div_mul_left _ _ hic]
    rw [this]
    exact hgen _ _
  have hle : Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) ≤
      Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact hiF a
    · rintro _ ⟨a, b, rfl⟩
      rw [← div_div_div_cancel_right₀ hl (w a) (w b)]
      exact div_mem (hAF _ (hw a)) (hAF _ (hw b))
  have hfrac : ∀ a : Ω', ∃ u ∈ chRing o (joinCo i x w) (c, l), ∃ v ∈ chRing o (joinCo i x w) (c, l),
      a = u / v := by
    intro a
    have ha : a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
      hle (by rw [hcl]; exact Subfield.mem_top a)
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
    have hs : Subring.closure (chRing o (joinCo i x w) (c, l) : Set Ω') =
        (chRing o (joinCo i x w) (c, l)).toSubring :=
      Subring.closure_eq (chRing o (joinCo i x w) (c, l)).toSubring
    rw [hs] at hy hz
    exact ⟨y, hy, z, hz, rfl⟩
  obtain ⟨M'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart o Ω' (κ × κ') (joinCo i x w) ⟨(c, l), hJ, hfrac⟩
  have hctr : ∀ p', p' ∈ ctrSet o x i M'.ξ := fun p' => (PositivityTheory.HtPt.Mb.join_charts o Ω κ κ' x Ω' i w M' hi p').1
  obtain ⟨f, hf, -⟩ := PositivityTheory.HtPt.Mb.morph o Ω κ x M o Ω' (κ × κ') (joinCo i x w) M' i hctr
  exact ⟨M', f, hf⟩

end PositivityTheory.HtPt.Mb.LJoinExists


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i :=
  @PositivityTheory.HtPt.Mb.LJoinExists.join_exists
end

