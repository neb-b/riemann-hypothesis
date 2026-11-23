module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MonMemPow
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem gr_nak {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    (h1 : DirectSum.IsInternal 𝒜) (h2 : SetLike.GradedMonoid 𝒜) (m : Ideal B) (hm : m ≤ Ideal.jacobson ⊥)
    (η : Ideal A) (hη : η = Ideal.span {x | x ∈ η ∧ ∃ j, x ∈ 𝒜 j}) (j : ℤ) (hfg : (𝒜 j).FG)
    (h : ∀ y ∈ 𝒜 j, y ∈ η ⊔ m.map (algebraMap B A)) : ∀ y ∈ 𝒜 j, y ∈ η := by
  classical
  letI : DirectSum.Decomposition 𝒜 := h1.chooseDecomposition
  letI : GradedRing 𝒜 := { toGradedMonoid := h2, toDecomposition := ‹_› }
  have hhom : η.IsHomogeneous 𝒜 := by
    rw [hη]
    exact Ideal.homogeneous_span 𝒜 _ (fun x hx => ⟨hx.2.choose, hx.2.choose_spec⟩)
  let p : A →ₗ[B] A := (𝒜 j).subtype ∘ₗ (DirectSum.component B ℤ (fun i => 𝒜 i) j) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hp : ∀ x, p x = (DirectSum.decompose 𝒜 x j : A) := fun x => rfl
  have key : 𝒜 j ≤ (η.restrictScalars B ⊓ 𝒜 j) ⊔ m • 𝒜 j := by
    intro y hy
    obtain ⟨e, he, f, hf, rfl⟩ := Submodule.mem_sup.1 (h y hy)
    have hpy : p (e + f) = e + f := by
      rw [hp]
      exact DirectSum.decompose_of_mem_same 𝒜 hy
    rw [← hpy, map_add (f := _)]
    refine Submodule.add_mem_sup ⟨?_, ?_⟩ ?_
    · rw [hp]
      exact hhom j he
    · rw [hp]
      exact (DirectSum.decompose 𝒜 e j).2
    · have hf' : f ∈ m • (⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map]
        exact hf
      have hmem := Submodule.mem_map_of_mem (f := p) hf'
      rw [Submodule.map_smul''] at hmem
      refine Submodule.smul_mono le_rfl (fun z hz => ?_) hmem
      obtain ⟨a, -, rfl⟩ := hz
      rw [hp]
      exact (DirectSum.decompose 𝒜 a j).2
  intro y hy
  exact (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hm key hy).1

private theorem w_ge {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) : -2 ≤ w n i - w n j := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w]

private theorem w_lt {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) (h : j < i) : w n i - w n j ≤ -1 := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [w] <;> omega

private theorem w_nlt {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) (h : ¬ j < i) : 0 ≤ w n i - w n j := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [w] <;> omega

private theorem mon_mem_pow {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    (hn : n = 2 ∨ n = 3) {K : Type} [CommRing K] (ρ : NRep F n K) (L : List (F.G0 × Fin n × Fin n)) :
    ∀ M : ℕ, (L.map fun s => w n s.2.1 - w n s.2.2).sum ≤ -2 * (M : ℤ) →
      (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod ∈ ρ.triP ^ M := by
  induction L with
  | nil =>
    intro M hM
    have : M = 0 := by
      simp only [List.map_nil, List.sum_nil] at hM
      omega
    subst this
    simp
  | cons s L ih =>
    intro M hM
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hM ⊢
    by_cases h : s.2.2 < s.2.1
    · rcases M with _ | M
      · simp
      · rw [pow_succ']
        refine Ideal.mul_mem_mul (Ideal.subset_span ⟨s.1, s.2.1, s.2.2, h, rfl⟩) (ih M ?_)
        have := w_ge hn s.2.1 s.2.2
        push_cast at hM
        omega
    · refine Ideal.mul_mem_left _ _ (ih M ?_)
      have := w_nlt hn s.2.1 s.2.2 h
      omega

theorem UpperTheory.V.Fr.l41 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η : Ideal S.A, η.IsPrime → S.IsHom η → ¬ S.u.triP ≤ η → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ η ≤ x.asIdeal := by
  intro l _ O _ _ _ _ F C₀ n hF hn S η hp hη hT
  obtain ⟨hco, hm⟩ := UpperTheory.V.Fr.co_B hF hn S
  obtain ⟨h1, h2, -, hfg, -, hnoeth, hr⟩ := UpperTheory.V.Fr.gr_A hF hn S
  have hrad : ¬ S.u.triP ≤ (η ⊔ S.mB.map (algebraMap S.B S.A)).radical := by
    intro hrad
    obtain ⟨M, hM⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    have hj : S.mB ≤ Ideal.jacobson ⊥ := by
      rw [← hm]
      exact maximalIdeal_le_jacobson _
    apply hT
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, i, j, hij, rfl⟩
    have hw := w_lt hn i j hij
    have hpow := SetLike.pow_mem_graded (2 * M) (hr g i j)
    refine hp.mem_of_pow_mem (2 * M) (gr_nak S.gr h1 h2 S.mB hj η hη _ (hfg _) (fun y hy => hM ?_) _ hpow)
    have : S.gr ((2 * M) • (w n i - w n j)) ≤ (S.u.triP ^ M).restrictScalars S.B := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨L, hL, rfl⟩
      refine mon_mem_pow hn S.u L M ?_
      rw [hL, nsmul_eq_mul]
      push_cast
      nlinarith [Int.natCast_nonneg M]
    exact this hy
  rw [Ideal.radical_eq_sInf, le_sInf_iff] at hrad
  push Not at hrad
  obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := hrad
  obtain ⟨x, ⟨⟨hx1, -⟩, hx2⟩, hx3⟩ := UpperTheory.V.Fr.jac hF hn S (PrimeSpectrum.zeroLocus (η : Set S.A))
    (PrimeSpectrum.isClosed_zeroLocus _) Set.univ isOpen_univ
    ⟨⟨p, hp2⟩, ⟨le_sup_left.trans hp1, trivial⟩, Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hp1), hp3⟩
  exact ⟨x, hx3, hx2, hx1⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.QuotientHomNonvanishingBound
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem finite_lambda_surjective_injective_lift :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (S₂ : Space O F 2) (S₃ : Space O F 3) (I₂ : Ideal S₂.B), S₂.FinLam I₂ → ∀ (C : Type) [CommRing C] [Algebra O C] (K : Type) [CommRing K] [Algebra O K] (p : S₃.B →ₐ[O] C) (q : S₃.A →ₐ[O] K) (j : C →ₐ[O] K), Function.Surjective p → Function.Injective j → (∀ b, q (S₃.inc b) = j (p b)) → ∀ (σ : NRep F 2 K) (ξ : S₂.A →ₐ[O] K) (β : S₂.B →ₐ[O] C), IsCorner (S₃.u.map (q : S₃.A →+* K)) σ → S₂.u.map (ξ : S₂.A →+* K) = σ → (∀ b, ξ (S₂.inc b) = j (β b)) → S₃.FinLam ((I₂.map β).comap p) := by
  intro l _ O _ _ _ _ F C₀ hF S₂ S₃ I₂ hI₂ C _ _ K _ _ p q j hp hj hpq σ ξ β hc hσ hβ
  subst hσ
  obtain ⟨hco₂, hm₂⟩ := co_B hF (Or.inl rfl) S₂
  have hI₂' : S₂.mB ≤ (I₂ ⊔ S₂.lamId).radical := hI₂
  show S₃.mB ≤ ((I₂.map β).comap p ⊔ S₃.lamId).radical
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro P ⟨hJP, hPp⟩
  have hker : ∀ y, p y = 0 → y ∈ P := by
    intro y hy
    apply hJP
    apply Ideal.mem_sup_left
    rw [Ideal.mem_comap, hy]
    exact zero_mem _
  have hPc : (P.map p).comap p = P := by
    rw [Ideal.comap_map_of_surjective _ hp]
    refine sup_eq_left.mpr ?_
    intro y hy
    exact hker y (by simpa using hy)
  have hpull : ∀ y, p y ∈ P.map p → y ∈ P := by
    intro y hy
    rw [← hPc]
    exact hy
  have hlam : S₃.lamId ≤ P := le_sup_right.trans hJP
  have hqeq : ∀ y y' : S₃.B, q (S₃.inc y) = q (S₃.inc y') → y - y' ∈ P := by
    intro y y' h
    rw [hpq, hpq] at h
    exact hker _ (by rw [map_sub, hj h, sub_self])
  have hψ : ∀ v i g, β (S₂.ψB v i g) = p (S₃.ψB v (cor i) g) := by
    intro v i g
    apply hj
    rw [← hβ, ← hpq]
    exact congrArg (fun u : Kˣ => (u : K)) (hc.ψ v i g)
  have hIP : I₂.map β ≤ P.map p := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨y, hy⟩ := hp (β b)
    rw [Ideal.mem_comap, ← hy]
    apply Ideal.mem_map_of_mem
    apply hJP
    apply Ideal.mem_sup_left
    rw [Ideal.mem_comap, hy]
    exact Ideal.mem_map_of_mem _ hb
  haveI : (P.map p).IsPrime := Ideal.map_isPrime_of_surjective hp (fun y hy => hker y hy)
  have hQ : S₂.mB ≤ (P.map p).comap β := by
    refine hI₂'.trans ((Ideal.radical_mono ?_).trans_eq (Ideal.IsPrime.radical inferInstance))
    refine sup_le (Ideal.map_le_iff_le_comap.mp hIP) ?_
    unfold Space.lamId
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes, ← AlgHom.commutes p]
      exact Ideal.mem_map_of_mem _
        (hlam (by unfold Space.lamId; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)))
    · rw [Ideal.span_le]
      rintro _ ⟨v, i, g, hg, hΨ, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_sub, map_one, hψ, ← map_one p, ← map_sub]
      exact Ideal.mem_map_of_mem _ (hlam (by
        unfold Space.lamId
        exact Ideal.mem_sup_right (Ideal.subset_span ⟨v, cor i, g, hg, hΨ, rfl⟩)))
  have hlift : ∀ (b : S₂.B) (y : S₃.B), β b = p y → ∃ c, y - algebraMap O S₃.B c ∈ P := by
    intro b y hy
    obtain ⟨a, ha⟩ := @IsCO.res_surj O S₂.B _ _ _ _ hco₂ b
    rw [hm₂] at ha
    refine ⟨a, hpull _ ?_⟩
    rw [map_sub, AlgHom.commutes, ← hy, ← AlgHom.commutes β, ← map_sub]
    exact hQ ha
  have hmid : ∀ g : F.G0, S₃.aB g 1 - 1 ∈ P :=
    frobenius_corner_middle_mem hF S₃ P hPp hlam
      (fun g h => hqeq _ _ (by rw [map_mul, map_mul]; exact UpperTheory.V.Fr.mid_mul _ hc.odd g h))
      (fun v g => hqeq _ _ (hc.mid v g))
  refine frobenius_corner_maximalIdeal_le hF (Or.inr rfl) S₃ P (le_sup_left.trans hlam) ?_ ?_
  · intro x hx
    obtain ⟨L, hL, hxL⟩ := hx
    have hqx : q (S₃.inc x) ∈ (S₃.u.map (q : S₃.A →+* K)).mon 0 := by
      refine ⟨L, hL, ?_⟩
      have e : S₃.inc x = (L.map (fun s => S₃.u.r s.1 s.2.1 s.2.2)).prod := by
        apply Subtype.ext
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        exact hxL
      rw [e, map_list_prod, List.map_map]
      rfl
    obtain h0 | ⟨T, y, hy, hxy⟩ := frobenius_corner_monomial _ _ hc 0 _ hqx
    · refine ⟨0, ?_⟩
      simpa using hqeq x 0 (by rw [h0, map_zero, map_zero])
    · obtain ⟨L₂, hL₂, rfl⟩ := hy
      have hy₂mon : ((L₂.map (fun s => S₂.u.r s.1 s.2.1 s.2.2)).prod : S₂.R) ∈ S₂.ρ.mon 0 := by
        refine ⟨L₂, hL₂, ?_⟩
        rw [SubmonoidClass.coe_list_prod, List.map_map]
        rfl
      obtain ⟨b₂, hb₂⟩ : ∃ b₂ : S₂.B, S₂.inc b₂ = (L₂.map (fun s => S₂.u.r s.1 s.2.1 s.2.2)).prod :=
        ⟨⟨_, S₂.mon_mem hy₂mon⟩, Subtype.ext rfl⟩
      have hyval : (L₂.map fun s => (S₂.u.map (ξ : S₂.A →+* K)).r s.1 s.2.1 s.2.2).prod = j (β b₂) := by
        rw [← hβ, hb₂, map_list_prod, List.map_map]
        rfl
      obtain ⟨y₃, hy₃⟩ := hp (β b₂)
      obtain ⟨c, hc'⟩ := hlift b₂ y₃ hy₃.symm
      have ht : (T.map fun g => (S₃.u.map (q : S₃.A →+* K)).r g 1 1).prod
          = j (p (T.map fun g => S₃.aB g 1).prod) := by
        rw [← hpq, map_list_prod, map_list_prod, List.map_map, List.map_map]
        rfl
      have hmk : ∀ g, Ideal.Quotient.mk P (S₃.aB g 1) = 1 := fun g => by
        rw [← map_one (Ideal.Quotient.mk P)]
        exact Ideal.Quotient.eq.mpr (hmid g)
      have ht1 : (T.map fun g => S₃.aB g 1).prod - 1 ∈ P := by
        rw [← Ideal.Quotient.eq, map_one, map_list_prod, List.map_map]
        simp [Function.comp_def, hmk]
      have hx2 : x - (T.map fun g => S₃.aB g 1).prod * y₃ ∈ P := by
        refine hqeq _ _ ?_
        rw [hxy, hyval, ht, hpq, map_mul p, map_mul j, hy₃]
      refine ⟨c, ?_⟩
      have e : x - algebraMap O S₃.B c = (x - (T.map fun g => S₃.aB g 1).prod * y₃)
          + ((T.map fun g => S₃.aB g 1).prod - 1) * y₃ + (y₃ - algebraMap O S₃.B c) := by ring
      rw [e]
      exact P.add_mem (P.add_mem hx2 (P.mul_mem_right _ ht1)) hc'
  · intro v i g
    fin_cases i
    · exact hlift _ _ (hψ v 0 g)
    · refine ⟨1, ?_⟩
      show S₃.ψB v 1 g - algebraMap O S₃.B 1 ∈ P
      rw [map_one]
      have e : S₃.ψB v 1 g - 1
          = (S₃.aB (F.loc0 v g) 1 - 1) - (S₃.aB (F.loc0 v g) 1 - S₃.ψB v 1 g) := by ring
      rw [e]
      exact P.sub_mem (hmid _) (hqeq _ _ (hc.mid v g))
    · exact hlift _ _ (hψ v 1 g)

private theorem finite_lambda_two_three_surjection_compat {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (S₂ : Space O F 2) (S₃ : Space O F 3)
    (I₂ : Ideal S₂.B) (hI₂ : S₂.FinLam I₂) (hT : ∀ ξ : Ideal S₂.A, ξ.IsPrime → S₂.u.TI ξ → I₂ ≤ S₂.π ξ)
    (C : Type) [CommRing C] [Algebra O C] [Nontrivial C] (K : Type) [CommRing K] [Algebra O K]
    (p : S₃.B →ₐ[O] C) (q : S₃.A →ₐ[O] K) (j : C →ₐ[O] K) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hj : Function.Injective j) (hpq : ∀ b, q (S₃.inc b) = j (p b)) (hker : RingHom.ker q = S₃.u.ee) :
    ∃ I₃ : Ideal S₃.B, S₃.FinLam I₃ ∧ ∀ ξ : Ideal S₃.A, ξ.IsPrime → S₃.u.TE ξ → I₃ ≤ S₃.π ξ := by
  obtain ⟨hcoB, -⟩ := co_B hF (Or.inr rfl) S₃
  haveI := hcoB
  haveI hcoC : IsCO O C := co_quot O S₃.B C p hp
  letI : Algebra C K := j.toRingHom.toAlgebra
  haveI : IsScalarTower O C K := IsScalarTower.of_algebraMap_eq (fun x => (j.commutes x).symm)
  have hjinj : Function.Injective (algebraMap C K) := hj
  have hcone : Cone O C (S₃.u.map (q : S₃.A →+* K)) :=
    frobenius_corner_cone_map S₃.B S₃.A C K p (q : S₃.A →+* K) (fun c => hpq c) S₃.u (cone_u hF (Or.inr rfl) S₃).1
  have hodd : ∀ (g : F.G0) (i k : Fin 3), Odd (w 3 i - w 3 k) →
      (S₃.u.map (q : S₃.A →+* K)).r g i k = 0 := by
    intro g i k h
    show q (S₃.u.r g i k) = 0
    rw [← RingHom.mem_ker, hker]
    exact Ideal.subset_span ⟨g, i, k, h, rfl⟩
  obtain ⟨σ, hc⟩ := exists_frobenius_corner _ hodd (frobenius_corner_units hF C K _ hcone)
  obtain ⟨ξ, β, hξσ, hβ⟩ := alg hF (Or.inl rfl) S₂ C K hjinj σ (frobenius_corner_mem_cone C K _ σ hc hcone)
  refine ⟨(I₂.map β).comap p, finite_lambda_surjective_injective_lift hF S₂ S₃ I₂ hI₂ C K p q j hp hj hpq σ ξ β hc hξσ hβ, ?_⟩
  intro P hP hTE
  unfold NRep.TE NRep.OffTri at hTE
  obtain ⟨⟨hTP, hTM⟩, -, hee⟩ := hTE
  have hkerP : RingHom.ker q ≤ P := hker ▸ hee
  haveI hP' : (P.map q).IsPrime := Ideal.map_isPrime_of_surjective hq hkerP
  have hPc : (P.map q).comap q = P := by
    rw [Ideal.comap_map_of_surjective _ hq]
    exact sup_eq_left.mpr hkerP
  have hξr : ∀ g (a b : Fin 2), ξ (S₂.u.r g a b) = q (S₃.u.r g (cor a) (cor b)) := by
    intro g a b
    have e : (S₂.u.map (ξ : S₂.A →+* K)).r g a b = σ.r g a b := by rw [hξσ]
    rw [hc.r g a b] at e
    exact e
  have hTI : S₂.u.TI ((P.map q).comap ξ) := by
    unfold NRep.TI NRep.OffTri
    refine ⟨⟨?_, ?_⟩, fun h => absurd h (by decide)⟩
    · intro h
      apply hTP
      rw [NRep.triP, Ideal.span_le]
      rintro _ ⟨g, i, k, hki, rfl⟩
      fin_cases i <;> fin_cases k <;> first
        | exact absurd hki (by decide)
        | exact hee (Ideal.subset_span ⟨g, _, _, by decide, rfl⟩)
        | (rw [← hPc]
           have h1 := h (Ideal.subset_span ⟨g, 1, 0, by decide, rfl⟩)
           rw [Ideal.mem_comap, hξr] at h1
           exact h1)
    · intro h
      apply hTM
      rw [NRep.triM, Ideal.span_le]
      rintro _ ⟨g, i, k, hki, rfl⟩
      fin_cases i <;> fin_cases k <;> first
        | exact absurd hki (by decide)
        | exact hee (Ideal.subset_span ⟨g, _, _, by decide, rfl⟩)
        | (rw [← hPc]
           have h1 := h (Ideal.subset_span ⟨g, 0, 1, by decide, rfl⟩)
           rw [Ideal.mem_comap, hξr] at h1
           exact h1)
  have hT' := hT _ inferInstance hTI
  have hle : I₂.map β ≤ (P.map q).comap j := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    have hb' := hT' hb
    simp only [Space.π, Ideal.mem_comap] at hb' ⊢
    have e : j (β b) = ξ (S₂.inc b) := (hβ b).symm
    rw [e]
    exact hb'
  intro x hx
  rw [Ideal.mem_comap] at hx
  show S₃.inc x ∈ P
  rw [← hPc, Ideal.mem_comap, hpq]
  exact hle hx

theorem UpperTheory.V.Fr.l53 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (S₂ : Space O F 2) (S₃ : Space O F 3) (I₂ : Ideal S₂.B), S₂.FinLam I₂ → (∀ ξ : Ideal S₂.A, ξ.IsPrime → S₂.u.TI ξ → I₂ ≤ S₂.π ξ) → ∃ I₃ : Ideal S₃.B, S₃.FinLam I₃ ∧ ∀ ξ : Ideal S₃.A, ξ.IsPrime → S₃.u.TE ξ → I₃ ≤ S₃.π ξ := by
  intro l _ O _ _ _ _ F C₀ hF S₂ S₃ I₂ hI₂ hT
  by_cases htop : S₃.u.ee = ⊤
  · refine ⟨⊤, ?_, ?_⟩
    · show S₃.mB ≤ _
      rw [top_sup_eq, Ideal.radical_top]
      exact le_top
    · intro P hP hTE
      exact absurd (top_le_iff.mp (htop ▸ hTE.2.2)) hP.ne_top
  · haveI : Nontrivial (S₃.B ⧸ S₃.u.ee.comap S₃.inc) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.comap_ne_top _ htop)
    exact finite_lambda_two_three_surjection_compat hF S₂ S₃ I₂ hI₂ hT (S₃.B ⧸ S₃.u.ee.comap S₃.inc) (S₃.A ⧸ S₃.u.ee)
      (Ideal.Quotient.mkₐ O _) (Ideal.Quotient.mkₐ O _) (Ideal.quotientMapₐ S₃.u.ee S₃.inc le_rfl)
      (Ideal.Quotient.mkₐ_surjective O _) (Ideal.Quotient.mkₐ_surjective O _)
      Ideal.quotientMap_injective (fun b => rfl) (Ideal.Quotient.mkₐ_ker O _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TwoDim
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_dim {K : Type} [Field K] (W : Submodule K (Fin 2 → K))
    (hE : ∀ v ∈ W, (![v 0, 0] : Fin 2 → K) ∈ W) (a b : Matrix (Fin 2) (Fin 2) K)
    (ha : ∀ v ∈ W, a *ᵥ v ∈ W) (hb : ∀ v ∈ W, b *ᵥ v ∈ W) (ha' : a 1 0 ≠ 0) (hb' : b 0 1 ≠ 0) :
    W = ⊥ ∨ W = ⊤ := by
  have h0 : ∀ v ∈ W, v 0 ≠ 0 → (![1, 0] : Fin 2 → K) ∈ W := fun v hv h => by
    convert W.smul_mem (v 0)⁻¹ (hE v hv) using 1
    ext i; fin_cases i <;> simp [h]
  have h1 : ∀ v ∈ W, v 1 ≠ 0 → (![0, 1] : Fin 2 → K) ∈ W := fun v hv h => by
    convert W.smul_mem (v 1)⁻¹ (W.sub_mem hv (hE v hv)) using 1
    ext i; fin_cases i <;> simp [h, vecHead, vecTail]
  have h01 : (![1, 0] : Fin 2 → K) ∈ W → (![0, 1] : Fin 2 → K) ∈ W := fun h =>
    h1 _ (ha _ h) (by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using ha')
  have h10 : (![0, 1] : Fin 2 → K) ∈ W → (![1, 0] : Fin 2 → K) ∈ W := fun h =>
    h0 _ (hb _ h) (by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hb')
  rw [or_iff_not_imp_left]
  intro hW
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
  have key : (![1, 0] : Fin 2 → K) ∈ W ∧ (![0, 1] : Fin 2 → K) ∈ W := by
    by_cases h : v 0 = 0
    · have h' : v 1 ≠ 0 := fun h' => hv0 (by ext i; fin_cases i <;> simp [h, h'])
      exact ⟨h10 (h1 v hv h'), h1 v hv h'⟩
    · exact ⟨h0 v hv h, h01 (h0 v hv h)⟩
  rw [eq_top_iff]
  intro x _
  convert W.add_mem (W.smul_mem (x 0) key.1) (W.smul_mem (x 1) key.2) using 1
  ext i; fin_cases i <;> simp

theorem UpperTheory.V.Fr.typeE :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (K : Type) [Field K] (f : S.A →+* K), S.u.TE (RingHom.ker f) → MatIrr ⊤ fun g : F.G0 => ((S.u.map f).r g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ F C₀ hF S K _ f hT W hW
  obtain ⟨⟨hP, hM⟩, -, hee⟩ := hT
  obtain ⟨hco, -⟩ := co_B hF (Or.inr rfl) S
  have hid := idem hF (Or.inr rfl) S.B S.A S.u (cone_u hF (Or.inr rfl) S).2 0
  have hspan : ∀ M ∈ Submodule.span S.B (Set.range S.u.r), ∀ v ∈ W,
      ((M.map f).submatrix ![0, 2] ![0, 2]) *ᵥ v ∈ W := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g (Subgroup.mem_top g)
    | zero =>
      intro v _
      rw [Matrix.map_zero _ (map_zero f), Matrix.submatrix_zero]
      simp
    | add x y _ _ hx hy =>
      intro v hv
      convert W.add_mem (hx v hv) (hy v hv) using 1
      rw [← Matrix.add_mulVec]
      congr 1
      ext i j
      exact map_add f _ _
    | smul c x _ hx =>
      intro v hv
      convert W.smul_mem (f (algebraMap S.B S.A c)) (hx v hv) using 1
      rw [← Matrix.smul_mulVec]
      congr 1
      ext i j
      exact map_mul f (algebraMap S.B S.A c) _
  have hodd : ∀ g i j, Odd (w 3 i - w 3 j) → f (S.u.r g i j) = 0 := fun g i j h =>
    hee (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  obtain ⟨g, hg⟩ : ∃ g, f (S.u.r g 2 0) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hP (Ideal.span_le.2 ?_)
    rintro x ⟨g, i, j, hij, rfl⟩
    show f _ = 0
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact hc g | exact hodd g _ _ (by decide)
  obtain ⟨g', hg'⟩ : ∃ g, f (S.u.r g 0 2) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hM (Ideal.span_le.2 ?_)
    rintro x ⟨g, i, j, hij, rfl⟩
    show f _ = 0
    fin_cases i <;> fin_cases j <;>
      first | exact absurd hij (by decide) | exact hc g | exact hodd g _ _ (by decide)
  refine two_dim W (fun v hv => ?_) _ _ (hW g (Subgroup.mem_top g)) (hW g' (Subgroup.mem_top g')) hg hg'
  convert hspan _ hid v hv using 1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.single]
end

