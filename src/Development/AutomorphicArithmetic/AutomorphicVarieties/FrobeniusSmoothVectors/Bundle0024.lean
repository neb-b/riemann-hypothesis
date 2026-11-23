module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.JacobsonSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibreClosed
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem fibre_closed {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (m : Ideal B) [m.IsMaximal] (W : Set (PrimeSpectrum A)) (hW : IsLocallyClosed W) (p : PrimeSpectrum A)
    (hp : p ∈ W) (hm : m ≤ p.asIdeal.comap (algebraMap B A)) :
    ∃ x ∈ W, m ≤ x.asIdeal.comap (algebraMap B A) ∧ x.asIdeal.IsMaximal := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hW
  obtain ⟨hpU, hpZ⟩ := hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hfU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU hU
  have hqmax : (p.asIdeal.comap (algebraMap B A)).IsMaximal := by
    have e := Ideal.IsMaximal.eq_of_le ‹m.IsMaximal› (Ideal.IsPrime.comap (algebraMap B A)).ne_top hm
    rw [← e]
    infer_instance
  letI := Ideal.Quotient.field (p.asIdeal.comap (algebraMap B A))
  haveI : IsJacobsonRing (A ⧸ p.asIdeal) :=
    isJacobsonRing_of_finiteType (A := B ⧸ p.asIdeal.comap (algebraMap B A))
  have hbot : (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 ‹_› ⊥ Ideal.isPrime_bot
  have hf0 : Ideal.Quotient.mk p.asIdeal f ∉ (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpf
  have hf1 : ¬ ∀ J ∈ {J : Ideal (A ⧸ p.asIdeal) | ⊥ ≤ J ∧ J.IsMaximal}, Ideal.Quotient.mk p.asIdeal f ∈ J :=
    fun h => hf0 (Ideal.mem_sInf.2 h)
  push_neg at hf1
  obtain ⟨J, ⟨-, hJ⟩, hfJ⟩ := hf1
  haveI := hJ
  haveI := hJ.isPrime
  have hle : p.asIdeal ≤ J.comap (Ideal.Quotient.mk p.asIdeal) := fun a ha => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact J.zero_mem
  refine ⟨⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩, ⟨hfU ?_, ?_⟩, ?_,
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  · exact hfJ
  · have hpx : p ≤ ⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩ := hle
    exact hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 hpZ) ((PrimeSpectrum.le_iff_mem_closure _ _).1 hpx)
  · exact hm.trans (Ideal.comap_mono hle)

theorem UpperTheory.V.Fr.jac :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ C : Set (PrimeSpectrum S.A), IsClosed C → ∀ U : Set (PrimeSpectrum S.A), IsOpen U → (C ∩ U ∩ S.BB).Nonempty → ∃ x ∈ C ∩ U ∩ S.BB, x.asIdeal.IsMaximal := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C hC U hU hne
  obtain ⟨-, -, -, -, hft, -, -⟩ := gr_A hF hn S
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  haveI : S.mB.IsMaximal := hmax ▸ IsLocalRing.maximalIdeal.isMaximal S.B
  obtain ⟨p, ⟨hpC, hpU⟩, hpm, hpT⟩ := hne
  have hO : IsOpen {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal} :=
    (PrimeSpectrum.isClosed_zeroLocus (S.u.triP : Set S.A)).isOpen_compl
  have hW : IsLocallyClosed (C ∩ U ∩ {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal}) :=
    (hC.isLocallyClosed.inter hU.isLocallyClosed).inter hO.isLocallyClosed
  obtain ⟨x, ⟨⟨hxC, hxU⟩, hxT⟩, hxm, hxmax⟩ := fibre_closed S.mB _ hW p ⟨⟨hpC, hpU⟩, hpT⟩ hpm
  exact ⟨x, ⟨⟨hxC, hxU⟩, hxm, hxT⟩, hxmax⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerLiftTwoToThree
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ex_core {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A) [GradedAlgebra 𝒜]
    (h0 : 𝒜 0 = 1) (hinj : Function.Injective (algebraMap B A)) (p : Ideal B) [p.IsPrime] :
    ∃ η : Ideal A, η.IsPrime ∧ η.IsHomogeneous 𝒜 ∧ η.comap (algebraMap B A) = p := by
  classical
  have key : ∀ x ∈ Ideal.map (algebraMap B A) p, ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c := by
    intro x hx
    have hx' : x ∈ (p • (⊤ : Submodule B A)) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    refine Submodule.smul_induction_on (p := fun x => ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c)
      hx' ?_ ?_
    · intro b hb y _
      have hy : GradedAlgebra.proj 𝒜 0 y ∈ 𝒜 0 := by
        rw [GradedAlgebra.proj_apply]
        exact SetLike.coe_mem _
      rw [h0] at hy
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hy
      refine ⟨b * c, p.mul_mem_right c hb, ?_⟩
      rw [LinearMap.map_smul, ← hc, Algebra.smul_def, map_mul]
    · intro x y hx hy
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      exact ⟨c + d, p.add_mem hc hd, by rw [map_add (f := _), hxc, hyd, map_add (f := _)]⟩
  have hdisj : Disjoint ((Ideal.map (algebraMap B A) p : Ideal A) : Set A)
      (Algebra.algebraMapSubmonoid A p.primeCompl : Set A) := by
    rw [Set.disjoint_left]
    rintro x hxJ ⟨s, hs, rfl⟩
    obtain ⟨c, hc, he⟩ := key _ hxJ
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 s)] at he
    exact hs (by rw [hinj he]; exact hc)
  obtain ⟨P, hP, hJP, hPd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  refine ⟨(P.homogeneousCore 𝒜).toIdeal, Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hP,
    (P.homogeneousCore 𝒜).isHomogeneous, ?_⟩
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_comap] at hb
    have hbP : algebraMap B A b ∈ P := Ideal.toIdeal_homogeneousCore_le 𝒜 P hb
    by_contra hnb
    exact Set.disjoint_left.mp hPd hbP ⟨b, hnb, rfl⟩
  · intro b hb
    rw [Ideal.mem_comap]
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨0, SetLike.algebraMap_mem_graded 𝒜 b⟩
      (hJP (Ideal.mem_map_of_mem _ hb))

private theorem one_le_td {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [GradedAlgebra 𝒜] (η : Ideal A) (hη : η.IsPrime) (hh : η.IsHomogeneous 𝒜) {a : A} {α : ℤ} (ha : a ∈ 𝒜 α)
    (hα : α ≠ 0) (ha' : a ∉ η) : 1 ≤ Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  classical
  have key : ∀ Q : Polynomial B, Polynomial.aeval a Q ∈ η → ∀ k, Q.coeff k ∈ η.comap (algebraMap B A) := by
    intro Q hQ k
    have hn : Q.natDegree < Q.natDegree + k + 1 := by omega
    rw [Polynomial.aeval_eq_sum_range' hn] at hQ
    have hmem : ∀ i : ℕ, Q.coeff i • a ^ i ∈ 𝒜 (i • α) := fun i =>
      Submodule.smul_mem _ _ (SetLike.pow_mem_graded i ha)
    have h2 : GradedAlgebra.proj 𝒜 (k • α)
        (∑ i ∈ Finset.range (Q.natDegree + k + 1), Q.coeff i • a ^ i) ∈ η := by
      rw [GradedAlgebra.proj_apply]
      exact (Ideal.IsHomogeneous.mem_iff 𝒜 hh).1 hQ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single k] at h2
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hmem k), Algebra.smul_def] at h2
      rcases hη.mem_or_mem h2 with h | h
      · exact h
      · exact absurd (hη.mem_of_pow_mem _ h) ha'
    · intro i _ hik
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hmem i)]
      intro he
      apply hik
      have he' : (i : ℤ) * α = (k : ℤ) * α := by simpa [nsmul_eq_mul] using he
      exact_mod_cast mul_right_cancel₀ hα he'
    · intro hk
      exact absurd (Finset.mem_range.2 (by omega)) hk
  have htr : Transcendental (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) := by
    rw [transcendental_iff]
    intro P hP
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk (η.comap (algebraMap B A)))
      Ideal.Quotient.mk_surjective P
    have e : Polynomial.aeval (Ideal.Quotient.mk η a) (Q.map (Ideal.Quotient.mk (η.comap (algebraMap B A))))
        = Ideal.Quotient.mk η (Polynomial.aeval a Q) := by
      have e1 := Polynomial.aeval_map_algebraMap (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) Q
      rw [Ideal.Quotient.algebraMap_eq] at e1
      rw [e1, ← Ideal.Quotient.mkₐ_eq_mk B η, Polynomial.aeval_algHom_apply]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at hP
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact key Q hP k
  haveI : Algebra.Transcendental (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := ⟨⟨_, htr⟩⟩
  exact Cardinal.one_le_iff_pos.2 (trdeg_pos _ _)

private theorem pair {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [SetLike.GradedMonoid 𝒜] (h0 : 𝒜 0 = 1) {ξ η : Ideal A} (hξ : ξ.IsPrime)
    (hle : η.comap (algebraMap B A) ≤ ξ.comap (algebraMap B A)) {a b : A} {α β : ℤ} (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β)
    (hα : 0 < α) (hβ : β < 0) (ha' : a ∉ ξ) (hb' : b ∉ ξ) : a ∉ η ∧ b ∉ η := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = α := ⟨α.toNat, Int.toNat_of_nonneg hα.le⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -β := ⟨(-β).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hmem : a ^ k * b ^ m ∈ 𝒜 0 := by
    have h1 := SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) (SetLike.pow_mem_graded m hb)
    have he : k • α + m • β = 0 := by
      rw [nsmul_eq_mul, nsmul_eq_mul, hk, hm]
      ring
    rwa [he] at h1
  rw [h0] at hmem
  obtain ⟨x, hx⟩ := Submodule.mem_one.mp hmem
  have hc : a ^ k * b ^ m ∉ ξ := by
    intro hin
    rcases hξ.mem_or_mem hin with h | h
    · exact ha' (hξ.mem_of_pow_mem _ h)
    · exact hb' (hξ.mem_of_pow_mem _ h)
  have hxξ : x ∉ ξ.comap (algebraMap B A) := by
    rw [Ideal.mem_comap, hx]
    exact hc
  have hxη : x ∉ η.comap (algebraMap B A) := fun hin => hxξ (hle hin)
  rw [Ideal.mem_comap, hx] at hxη
  constructor
  · intro hin
    exact hxη (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hin _ hk0))
  · intro hin
    exact hxη (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hin _ hm0))

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.frobenius_corner_lift_two_to_three :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ η : Ideal S.A, η.IsPrime ∧ S.IsHom η ∧ S.π η = p ∧ S.u.TI η ∧ S.td η = 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hle
  obtain ⟨hint, hgm, h0, -, -, -, hr⟩ := gr_A hF hn S
  letI : GradedAlgebra S.gr := { hgm, hint.chooseDecomposition with }
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  obtain ⟨η, hηp, hηh, hηc⟩ := ex_core S.gr h0 hinj p
  have hP := hTI.1.1
  have hM := hTI.1.2
  simp only [NRep.triP, NRep.triM, Ideal.span_le, Set.not_subset] at hP hM
  obtain ⟨_, ⟨g, i, j, hji, rfl⟩, hb⟩ := hP
  obtain ⟨_, ⟨g', i', j', hij', rfl⟩, ha⟩ := hM
  have hbd : w n i - w n j < 0 := by have := w_lt hji; omega
  have had : 0 < w n i' - w n j' := by have := w_lt hij'; omega
  have hle' : η.comap (algebraMap S.B S.A) ≤ ξ.comap (algebraMap S.B S.A) := by
    rw [hηc]; exact hle
  have hab := pair S.gr h0 hξ hle' (hr g' i' j') (hr g i j) had hbd ha hb
  refine ⟨η, hηp, ?_, hηc, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply le_antisymm
    · have e := (Ideal.IsHomogeneous.iff_eq S.gr η).mp hηh
      calc η = _ := e.symm
        _ ≤ _ := Ideal.span_mono ?_
      rintro _ ⟨⟨x, hxh⟩, hx, rfl⟩
      exact ⟨hx, hxh⟩
    · exact Ideal.span_le.2 fun x hx => hx.1
  · intro h
    exact hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩))
  · intro h
    exact hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))
  · intro h3 h
    have hE := hTI.2 h3
    simp only [NRep.ee, Ideal.span_le, Set.not_subset] at hE
    obtain ⟨_, ⟨g'', i'', j'', hodd, rfl⟩, hc⟩ := hE
    have hne : w n i'' - w n j'' ≠ 0 := by
      rintro h0'
      rw [h0'] at hodd
      exact (Int.not_odd_iff_even.2 ⟨0, by norm_num⟩) hodd
    have hcη : S.u.r g'' i'' j'' ∉ η := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact (pair S.gr h0 hξ hle' (hr g' i' j') (hr g'' i'' j'') had hneg ha hc).2
      · exact (pair S.gr h0 hξ hle' (hr g'' i'' j'') (hr g i j) hpos hbd hc hb).1
    exact hcη (h (Ideal.subset_span ⟨g'', i'', j'', hodd, rfl⟩))
  · exact le_antisymm (fibre hF hn S η hηp ⟨fun h => hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩)),
      fun h => hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))⟩)
      (one_le_td S.gr η hηp hηh (hr g' i' j') had.ne' hab.1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerMaximalIdealLe
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem mem_of_forall_sup_pow {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (P : Ideal B) (b : B) (h : ∀ N : ℕ, ∃ y ∈ P, b - y ∈ maximalIdeal B ^ N) : b ∈ P := by
  by_cases hP : P = ⊤
  · rw [hP]
    exact Submodule.mem_top
  haveI : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  haveI : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hPm : P ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal hP
  have hmap : maximalIdeal B ≤ (maximalIdeal (B ⧸ P)).comap (Ideal.Quotient.mk P) := by
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)
    have h1 : Ideal.Quotient.mk P (x * y - 1) = 0 := by
      rw [map_sub, map_mul, hy, ← hu, Units.mul_inv, map_one, sub_self]
    have h2 := hPm (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have h3 := (maximalIdeal B).sub_mem ((maximalIdeal B).mul_mem_right y hx) h2
    rw [sub_sub_cancel] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hb : Ideal.Quotient.mk P b ∈ ⨅ N : ℕ, (maximalIdeal (B ⧸ P)) ^ N := by
    rw [Ideal.mem_iInf]
    intro N
    obtain ⟨y, hy, hby⟩ := h N
    have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk P) hby
    rw [Ideal.map_pow] at h3
    have h4 := Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmap) N h3
    rwa [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hy, sub_zero] at h4
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top, Ideal.mem_bot,
    Ideal.Quotient.eq_zero_iff_mem] at hb
  exact hb

theorem UpperTheory.V.Fr.frobenius_corner_maximalIdeal_le :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (P : Ideal S.B), (maximalIdeal O).map (algebraMap O S.B) ≤ P → (∀ x : S.B, (x : S.R) ∈ S.ρ.mon 0 → ∃ c : O, x - algebraMap O S.B c ∈ P) → (∀ v i g, ∃ c : O, S.ψB v i g - algebraMap O S.B c ∈ P) → S.mB ≤ P := by
  intro l _ O _ _ _ _ F C₀ n hF hn S P hO hmon hψ
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  obtain ⟨-, -, h0, -, -, -, -⟩ := gr_A hF hn S
  obtain ⟨-, -, -, hcl⟩ := cont_u hF hn S
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  by_cases hPt : P = ⊤
  · rw [hPt]
    exact le_top
  have hPm : P ≤ S.mB := hmax ▸ IsLocalRing.le_maximalIdeal hPt
  let T : Subalgebra O S.R :=
    { carrier := {r | ∃ hr : r ∈ S.B, ∃ c : O, (⟨r, hr⟩ : S.B) - algebraMap O S.B c ∈ P}
      mul_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
        refine ⟨S.B.mul_mem ha hb, c * d, ?_⟩
        have e1 : (⟨a * b, S.B.mul_mem ha hb⟩ : S.B) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        have e : (⟨a, ha⟩ * ⟨b, hb⟩ : S.B) - algebraMap O S.B (c * d) =
            (⟨a, ha⟩ - algebraMap O S.B c) * ⟨b, hb⟩ + algebraMap O S.B c * (⟨b, hb⟩ - algebraMap O S.B d) := by
          rw [map_mul]
          ring
        rw [e1, e]
        exact P.add_mem (P.mul_mem_right _ hc) (P.mul_mem_left _ hd)
      add_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, d, hd⟩
        refine ⟨S.B.add_mem ha hb, c + d, ?_⟩
        have e1 : (⟨a + b, S.B.add_mem ha hb⟩ : S.B) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        have e : (⟨a, ha⟩ + ⟨b, hb⟩ : S.B) - algebraMap O S.B (c + d) =
            (⟨a, ha⟩ - algebraMap O S.B c) + (⟨b, hb⟩ - algebraMap O S.B d) := by
          rw [map_add (f := _)]
          ring
        rw [e1, e]
        exact P.add_mem hc hd
      algebraMap_mem' := by
        intro c
        refine ⟨S.B.algebraMap_mem c, c, ?_⟩
        have e : (⟨algebraMap O S.R c, S.B.algebraMap_mem c⟩ : S.B) = algebraMap O S.B c := rfl
        rw [e, sub_self]
        exact P.zero_mem }
  have hB0 : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ((S.ρ.ψ v i g : S.Rˣ) : S.R)}) ≤ T := by
    rw [Algebra.adjoin_le_iff]
    rintro r (hr | ⟨v, i, g, rfl⟩)
    · exact ⟨S.mon_mem hr, hmon ⟨r, S.mon_mem hr⟩ hr⟩
    · exact ⟨(S.ψB v i g).2, hψ v i g⟩
  intro x hx
  apply mem_of_forall_sup_pow P x
  intro N
  obtain ⟨M, hM⟩ := hcl 0 (N + 1)
  have hxB : ∀ K : ℕ, ∃ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ((S.ρ.ψ v i g : S.Rˣ) : S.R)}),
      (x : S.R) - y ∈ maximalIdeal S.R ^ K := x.2
  obtain ⟨y0, hy0, hxy⟩ := hxB M
  obtain ⟨hy0B, c, hc⟩ := hB0 hy0
  obtain ⟨z, hzdef⟩ : ∃ z : S.B, z = x - ⟨y0, hy0B⟩ := ⟨_, rfl⟩
  have hz : algebraMap S.B S.A z ∈ S.mB ^ (N + 1) • S.gr 0 := by
    refine hM _ ?_ ?_
    · rw [h0]
      exact Submodule.algebraMap_mem z
    · rw [hzdef]
      exact hxy
  rw [h0] at hz
  have key : ∀ a ∈ S.mB ^ (N + 1) • (1 : Submodule S.B S.A), ∃ w ∈ S.mB ^ (N + 1), a = algebraMap S.B S.A w := by
    intro a ha
    refine Submodule.smul_induction_on (p := fun a => ∃ w ∈ S.mB ^ (N + 1), a = algebraMap S.B S.A w) ha ?_ ?_
    · intro r hr t ht
      obtain ⟨s, rfl⟩ := Submodule.mem_one.1 ht
      exact ⟨r * s, Ideal.mul_mem_right _ _ hr, by rw [Algebra.smul_def, map_mul]⟩
    · rintro a b ⟨w1, h1, rfl⟩ ⟨w2, h2, rfl⟩
      exact ⟨w1 + w2, add_mem h1 h2, (map_add _ _ _).symm⟩
  obtain ⟨w, hw, hzw⟩ := key _ hz
  have hzw' : z = w := hinj hzw
  have hzm : z ∈ S.mB := hzw' ▸ Ideal.pow_le_self (Nat.succ_ne_zero N) hw
  have hzN : z ∈ S.mB ^ N := hzw' ▸ Ideal.pow_le_pow_right (Nat.le_succ N) hw
  have hyB : (⟨y0, hy0B⟩ : S.B) ∈ S.mB := by
    have e : (⟨y0, hy0B⟩ : S.B) = x - z := by rw [hzdef, sub_sub_cancel]
    rw [e]
    exact S.mB.sub_mem hx hzm
  have hcB : algebraMap O S.B c ∈ S.mB := by
    have e : algebraMap O S.B c = ⟨y0, hy0B⟩ - (⟨y0, hy0B⟩ - algebraMap O S.B c) := (sub_sub_cancel _ _).symm
    rw [e]
    exact S.mB.sub_mem hyB (hPm hc)
  have hcO : c ∈ maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : ((algebraMap O S.B c : S.B) : S.R) ∈ maximalIdeal S.R := hcB
    have h2 : IsUnit ((algebraMap O S.B c : S.B) : S.R) := hu.map (algebraMap O S.R)
    exact ((IsLocalRing.mem_maximalIdeal _).1 h1) h2
  have hyP : (⟨y0, hy0B⟩ : S.B) ∈ P := by
    have e : (⟨y0, hy0B⟩ : S.B) = (⟨y0, hy0B⟩ - algebraMap O S.B c) + algebraMap O S.B c := (sub_add_cancel _ _).symm
    rw [e]
    exact P.add_mem hc (hO (Ideal.mem_map_of_mem _ hcO))
  refine ⟨⟨y0, hy0B⟩, hyP, ?_⟩
  rw [hmax, ← hzdef]
  exact hzN
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerMiddleMem
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem aux {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} (hF : F.Ok C₀) (B : Type) [CommRing B] [Algebra O B]
    [IsCO O B] (P : Ideal B) (hP : P.IsPrime) (a : F.G0 → B) (hO : ∀ c ∈ maximalIdeal O, algebraMap O B c ∈ P)
    (h1 : a 1 = 1) (hmul : ∀ g h, a (g * h) - a g * a h ∈ P) (hc : AdicCont (maximalIdeal B) a)
    (hres : ∀ g, a g - 1 ∈ maximalIdeal B) (hst : ∀ g, a (F.star g) = a g)
    (hloc : ∀ v g, g ∈ F.Iv v → F.Ψ (F.loc v g) = 1 → a (F.loc0 v g) - 1 ∈ P) (g : F.G0) : a g - 1 ∈ P := by
  haveI : P.IsPrime := hP
  haveI : Nontrivial (B ⧸ P) := inferInstance
  haveI : IsCO O (B ⧸ P) :=
    co_quot O B (B ⧸ P) (Ideal.Quotient.mkₐ O P) (Ideal.Quotient.mkₐ_surjective O P)
  have hm : ∀ x ∈ maximalIdeal B, Ideal.Quotient.mk P x ∈ maximalIdeal (B ⧸ P) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ P)
    have hxy : x * y - 1 ∈ P := by
      rw [← Ideal.Quotient.eq, map_mul, hy, ← hu]
      simp
    have h2 : x * y - 1 ∈ maximalIdeal B := IsLocalRing.le_maximalIdeal hP.ne_top hxy
    have h3 : x * y ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hx
    apply (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using Ideal.sub_mem _ h3 h2
  let χ : F.G0 →* B ⧸ P :=
    { toFun := fun g => Ideal.Quotient.mk P (a g)
      map_one' := by simp [h1]
      map_mul' := fun g h => by
        rw [← map_mul]
        exact Ideal.Quotient.eq.mpr (hmul g h) }
  have hχ : ∀ g, χ g = Ideal.Quotient.mk P (a g) := fun g => rfl
  have key := frobenius_corner_middle_trivial hF (B ⧸ P)
    (fun c hc' => by
      rw [IsScalarTower.algebraMap_apply O B (B ⧸ P), Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hO c hc')
    χ
    (fun N => by
      have hle : ∀ x ∈ maximalIdeal B ^ N,
          Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N) (Ideal.Quotient.mk P x) = 0 := by
        intro x hx
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have hmap : Ideal.map (Ideal.Quotient.mk P) (maximalIdeal B) ≤ maximalIdeal (B ⧸ P) :=
          Ideal.map_le_iff_le_comap.mpr hm
        have := Ideal.pow_right_mono hmap N
        rw [← Ideal.map_pow] at this
        exact this (Ideal.mem_map_of_mem _ hx)
      let f := Ideal.Quotient.lift (maximalIdeal B ^ N)
        ((Ideal.Quotient.mk (maximalIdeal (B ⧸ P) ^ N)).comp (Ideal.Quotient.mk P)) hle
      convert (hc N).comp f using 1
      funext x
      rfl)
    (fun g => by
      rw [hχ, ← map_one (Ideal.Quotient.mk P), ← map_sub]
      exact hm _ (hres g))
    (fun g => by rw [hχ, hχ, hst g])
    (fun v g hg hΨ => by
      rw [hχ, ← map_one (Ideal.Quotient.mk P)]
      exact Ideal.Quotient.eq.mpr (hloc v g hg hΨ))
    g
  rw [hχ, ← map_one (Ideal.Quotient.mk P)] at key
  exact Ideal.Quotient.eq.mp key

theorem UpperTheory.V.Fr.frobenius_corner_middle_mem :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ (S : Space O F 3) (P : Ideal S.B), P.IsPrime → S.lamId ≤ P → (∀ g h, S.aB (g * h) 1 - S.aB g 1 * S.aB h 1 ∈ P) → (∀ v g, S.aB (F.loc0 v g) 1 - S.ψB v 1 g ∈ P) → ∀ g, S.aB g 1 - 1 ∈ P := by
  intro l _ O _ _ _ _ F C₀ hF S P hP hlam hmul hloc
  obtain ⟨hB, hm⟩ := UpperTheory.V.Fr.co_B hF (Or.inr rfl) S
  obtain ⟨-, hc, -, -⟩ := UpperTheory.V.Fr.cont_u hF (Or.inr rfl) S
  obtain ⟨-, -, -, -, hst⟩ := UpperTheory.V.Fr.star hF
  have h1 : S.aB 1 1 = 1 := Subtype.ext (by
    show S.ρ.r 1 1 1 = 1
    rw [map_one, Matrix.one_apply_eq])
  refine aux hF S.B P hP (fun g => S.aB g 1)
    (fun c hc => hlam (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hc))) h1 hmul (hm ▸ hc 1) (fun g => ?_)
    (fun g => Subtype.ext (hst S.ρ g 1 1)) (fun v g hg hΨ => ?_)
  · rw [hm]
    show S.ρ.r g 1 1 - 1 ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff O, map_sub, map_one, sub_eq_zero]
    have h := S.lift.2.1.1 g 1
    have hw : w 3 1 = 0 := rfl
    rw [hw, zpow_zero] at h
    exact h
  · have h2 : S.ψB v 1 g - 1 ∈ P :=
      hlam (Ideal.mem_sup_right (Ideal.subset_span ⟨v, 1, g, hg, hΨ, rfl⟩))
    have h3 := P.add_mem (hloc v g) h2
    rwa [sub_add_sub_cancel] at h3
end

