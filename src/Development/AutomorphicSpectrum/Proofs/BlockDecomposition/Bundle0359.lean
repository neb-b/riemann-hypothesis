module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolveUnitriangular
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0350
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0299
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0332
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltration
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.KmPow

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_quotient_unif_pow (m : ℕ) : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) := by
  have hmax : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {Zls.unif k} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 Zls.irreducible_unif
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k}) := by
    rw [← hmax]
    exact (inferInstance : Finite 𝓀[k])
  have := Ideal.finite_quotient_pow (I := Ideal.span {Zls.unif k}) ⟨{Zls.unif k}, by simp⟩ m
  rwa [Ideal.span_singleton_pow] at this

theorem Km_anti (N : ℕ) {m m' : ℕ} (h : m ≤ m') : Zls.Km k N m' ≤ Zls.Km k N m := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have key : Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g =
      Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)
        (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g) := by
    ext i j
    simp
  rw [MonoidHom.mem_ker] at hg ⊢
  rw [key, hg, map_one]

theorem exists_pow_mem_Km (N m' : ℕ) {m : ℕ} {x : GL (Fin N) k} (hx : x ∈ Zls.Km k N m) :
    ∃ M : ℕ, 0 < M ∧ x ^ M ∈ Zls.Km k N m' := by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  haveI := finite_quotient_unif_pow (k := k) m'
  set f := Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'}))
    with hf
  refine ⟨orderOf (f g), orderOf_pos _, ?_⟩
  rw [← map_pow]
  refine Subgroup.mem_map.2 ⟨g ^ orderOf (f g), ?_, rfl⟩
  rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]

theorem KM_antitone_and_pow : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n),
    Antitone (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd) ∧
    ∀ m m', m ≤ m' → ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd,
      ∃ N : ℕ, 0 < N ∧ u ^ N ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m' + 1)) (fun _ : Fin n => 1) hd := by
  intro k _ _ _ _ n hd
  refine ⟨fun m m' h u hu => Km_anti n (Nat.succ_le_succ h) hu, fun m m' _ u hu => ?_⟩
  obtain ⟨M, hM, hp⟩ := exists_pow_mem_Km n (m' + 1) (show _ ∈ Zls.Km k n (m + 1) from hu)
  refine ⟨M, hM, ?_⟩
  show _ ∈ Zls.Km k n (m' + 1)
  rwa [map_pow]

end GlobalTheory.CompanionTheory.KmPow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetVolumeFormula
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_of_mem_ker {N m : ℕ} {A : GL (Fin N) 𝒪[k]}
    (hA : A ∈ (Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))).ker) (i j : Fin N) :
    (A : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈
      Ideal.span {Zls.unif k ^ m} := by
  rw [MonoidHom.mem_ker] at hA
  have h := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => u.val i j) hA
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h
  rw [← Ideal.Quotient.eq]
  rw [h]
  by_cases e : i = j
  · subst e
    simp
  · simp [Matrix.one_apply_ne e]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (B : Matrix (Fin N) (Fin N) 𝒪[k])
    (hB : ∀ i j, B i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ Ideal.span {Zls.unif k ^ m}) :
    ∃ b ∈ Zls.Km k N m, (b : Matrix (Fin N) (Fin N) k) = B.map (algebraMap 𝒪[k] k) := by
  set J : Ideal 𝒪[k] := Ideal.span {Zls.unif k ^ m} with hJ
  have hmap : B.map (Ideal.Quotient.mk J) = 1 := by
    ext i j
    have := Ideal.Quotient.eq.2 (hB i j)
    simp only [Matrix.map_apply]
    rw [this]
    by_cases e : i = j
    · subst e
      simp
    · simp [Matrix.one_apply_ne e]
  have hdet : Ideal.Quotient.mk J B.det = 1 := by
    have := RingHom.map_det (Ideal.Quotient.mk J) B
    rw [this]
    show (B.map (Ideal.Quotient.mk J)).det = 1
    rw [hmap, Matrix.det_one]
  have hmem : B.det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, hdet, map_one]
  have hJm : J ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [hJ, Ideal.span_singleton_le_iff_mem]
    have : Zls.unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [Zls.irreducible_unif.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.pow_mem_of_mem _ this m (by omega)
  have hunit : IsUnit B.det := by
    by_contra hn
    have h1 : B.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h2 := hJm hmem
    have h3 : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h3
  let G : GL (Fin N) 𝒪[k] := Matrix.GeneralLinearGroup.mk'' B hunit
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) G, ?_, ?_⟩
  · refine ⟨G, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    have h := congrFun (congrFun hmap i) j
    simpa [G, Matrix.GeneralLinearGroup.map_apply] using h
  · rfl

theorem conj_mem_Km {N m : ℕ} {p b : GL (Fin N) k} (hp : p ∈ KO k (Fin N)) (hb : b ∈ Zls.Km k N m) :
    p * b * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨A, hA, rfl⟩ := hb
  refine ⟨P * A * P⁻¹, ?_, by simp⟩
  exact (MonoidHom.normal_ker _).conj_mem A hA P

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    ((Zls.diagPow k N lam : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ lam i) := by
  ext i j
  simp [Zls.diagPow, Zls.unifU, Matrix.diagonal_apply]

theorem exists_cover (N m : ℕ) (hm : 1 ≤ m) (lam : Fin N → ℤ) (hlam : Antitone lam) :
    ∃ s : Finset (GL (Fin N) k),
      s.card ≤ Nat.card 𝓀[k] ^
        (∑ i : Fin N, ∑ j : Fin N, if i < j then (lam i - lam j).toNat else 0) ∧
      ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, ∃ c ∈ s, ∃ b ∈ Zls.Km k N m,
        x * Zls.diagPow k N lam * y = c * b := by
  classical
  obtain ⟨s0, hcard, hs0⟩ := GlobalTheory.CompanionTheory.KmCover.double_coset_cover 𝒪[k] k N (Zls.unif k) m
    Zls.irreducible_unif hm lam hlam
  let f : Matrix (Fin N) (Fin N) k → GL (Fin N) k := fun M =>
    if h : ∃ c : GL (Fin N) k, c.val = M then h.choose else 1
  refine ⟨s0.image f, Finset.card_image_le.trans hcard, ?_⟩
  rintro x ⟨A1, hA1, rfl⟩ y ⟨A2, hA2, rfl⟩
  obtain ⟨M, hM, B, hB, e⟩ := hs0 A1.val A2.val (entries_of_mem_ker hA1) (entries_of_mem_ker hA2)
  obtain ⟨b, hb, hbv⟩ := exists_mem_Km hm B hB
  set X : GL (Fin N) k := Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A1 *
    Zls.diagPow k N lam * Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A2 with hX
  have hXv : X.val = M * b.val := by
    rw [hbv, ← e, hX, Units.val_mul, Units.val_mul, diagPow_val]
    rfl
  have hex : ∃ c : GL (Fin N) k, c.val = M := by
    refine ⟨X * b⁻¹, ?_⟩
    rw [Units.val_mul, hXv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨f M, Finset.mem_image_of_mem f hM, b, hb, ?_⟩
  apply Units.ext
  have hf : (f M).val = M := by
    simp only [f, dif_pos hex]
    exact hex.choose_spec
  rw [Units.val_mul (f M) b, hf]
  exact hXv

theorem measure_translated_doubleCoset_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, 1 ≤ m → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → ∀ g : Fin (N - 1) → ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2}) ≤ (Nat.card 𝓀[k] : ENNReal) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) := by
  intro k _ _ _ _ N _ _ μ hμ m hm p1 p2 hp1 hp2 g
  classical
  obtain ⟨hanti, hgap⟩ := GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N g
  obtain ⟨s, hcard, hcov⟩ := exists_cover (k := k) N m hm (Zls.lamOf g) hanti
  rw [hgap] at hcard
  set U : Set (AdGL k N) :=
    (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k)) with hU
  let T : GL (Fin N) k → Set (AdGL k N) := fun c =>
    (fun q => (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * q) ⁻¹' U
  have hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m,
      ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2} ⊆ ⋃ c ∈ s, T c := by
    rintro _ ⟨h, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, hc, b, hb, e⟩ := hcov x hx y hy
    refine Set.mem_biUnion hc ?_
    refine ⟨p2⁻¹ * b * p2, ?_, ?_⟩
    · have := conj_mem_Km (inv_mem hp2) hb
      simpa using this
    · have e2 : p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2 = p1 * (c * b) * p2 := by
        rw [← e]
        group
      rw [e2]
      show (QuotientGroup.mk (p2⁻¹ * b * p2) : AdGL k N) =
        (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * QuotientGroup.mk (p1 * (c * b) * p2)
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      group
  calc μ _ ≤ μ (⋃ c ∈ s, T c) := measure_mono hsub
    _ ≤ ∑ c ∈ s, μ (T c) := measure_biUnion_finset_le _ _
    _ = ∑ _c ∈ s, μ U := Finset.sum_congr rfl fun c _ => measure_preimage_mul μ _ U
    _ = (s.card : ENNReal) * μ U := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcard

end GlobalTheory.CompanionTheory.KmVolume
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContainingStatement
section
open PositivityTheory.RgBcC.RealD (alg kF)

theorem GlobalTheory.T.exists_k_finite_submodule_containing :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
      (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V,
      (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) → ∀ S₀ : Submodule ℂ V,
      FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
      ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧
        ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S :=
  @GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemKNInvMulMemInfMapConj
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_KN_inv_mul_mem_inf_map_conj
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∀ y ∈ J,
      ∃ a ∈ KN k N J d hd, a⁻¹ * y ∈
        J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro _ _ hfact _ t hdom y hy
  obtain ⟨-, hNl, hM⟩ := hdom
  obtain ⟨u, hu, b, hb, n, hn, hyf⟩ := hfact y⁻¹ (J.inv_mem hy)
  obtain ⟨huJ, -⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hbJ, x, rfl⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hnJ, hnN⟩ := Subgroup.mem_inf.1 hn
  have hy' : y = n⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    have : y = (y⁻¹)⁻¹ := (inv_inv y).symm
    rw [this, hyf]; group
  refine ⟨n⁻¹, (KN k N J d hd).inv_mem (Subgroup.mem_inf.2 ⟨hnJ, hnN⟩), ?_⟩
  have hred : (n⁻¹)⁻¹ * y = (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    rw [hy']; group
  rw [hred]
  set g := leviEmb k (stdBlocks d hd) t with hg
  have hxKM : x⁻¹ ∈ KM k N J d hd :=
    (KM k N J d hd).inv_mem (show x ∈ (J).comap (leviEmb k (stdBlocks d hd)) from hbJ)
  have h1 : g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g ∈ J := by
    have h2 : t⁻¹ * x⁻¹ * t ∈ KM k N J d hd := (hM _ hxKM).2
    have h3 : leviEmb k (stdBlocks d hd) (t⁻¹ * x⁻¹ * t) ∈ J := h2
    simpa [hg, map_mul, map_inv] using h3
  have h4 : g⁻¹ * u⁻¹ * g ∈ J :=
    (Subgroup.mem_inf.1 (hNl _ ((KNl k N J d hd).inv_mem hu))).1
  refine Subgroup.mem_inf.2 ⟨J.mul_mem (J.inv_mem hbJ) (J.inv_mem huJ), ?_⟩
  refine Subgroup.mem_map.2 ⟨(g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g) * (g⁻¹ * u⁻¹ * g),
    J.mul_mem h1 h4, ?_⟩
  simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end GlobalTheory.CompanionTheory.Casselman
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProjectiveOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem exists_sub_of_ample {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : GlobalTheory.IsAmpleLB H) {P : X.Modules} (hP : IsCoherent P) (S : ℕ → Subobject P) (hS : ClosedSys I P S) :
    ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hV : UniformVanishing := @GlobalTheory.T.uniform_vanishing_of_graded_noetherian _root_.GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth
  have hG : UniformGen := @_root_.GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth _root_.GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth (@hV)
  obtain ⟨n₁, h₁⟩ := _root_.GlobalTheory.CompanionTheory.GE.Step.step_uniform (@hG) I H hH hP S hS
  have hW : ∀ n : ℤ, ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧
      (n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1)) := fun n => by
    by_cases hn : n₁ ≤ n
    · obtain ⟨W, a, b⟩ := _root_.GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit I hI H hH hP S hS n (h₁ n hn)
      exact ⟨W, a, fun _ => b⟩
    · exact ⟨∅, fun _ => Set.empty_subset _, fun h => absurd h hn⟩
  choose W a b using hW
  exact _root_.GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs I H hH hP S hS n₁ W a b

theorem statement_open_projective : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {N : ℕ} {Y : Scheme.{0}} (i : Y ⟶ projectiveSpace A N), IsClosedImmersion i → ∀ (O : Y.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩; Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := by
  intro A _ _ I hI N Y i hi O
  letI : Y.Over (Spec (.of A)) := ⟨i ≫ ProjSpace.toSpecBase A N⟩
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (Y ↘ Spec (.of A))⟩
  have hpr : IsProper (ProjSpace.toSpecBase A N) := by
    open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ProjSpace in exact isProper_str A N
  have hp : IsProper (Y ↘ Spec (.of A)) := (inferInstance : IsProper (i ≫ ProjSpace.toSpecBase A N))
  have hln : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of A))
  have hcs : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of A))
  have hno : IsNoetherian Y := ⟨⟩
  have hH : GlobalTheory.IsAmpleLB ((GlobalTheory.ProjSpace.O1 A N).pull i) := (GlobalTheory.isAmple_projective_O_one A N).pull_of_isAffineHom i
  intro E hE S hS _ hP
  obtain ⟨P, hPc, f, hf⟩ := GlobalTheory.T.coherent_extension_surjection_open _ hH O E hE
  obtain ⟨T, hT, hTs⟩ := hP
  obtain ⟨hcl, Sb, hSb, hb, hc⟩ := GlobalTheory.T.closed_system_restriction_open I O hPc hE f hf S hS T hT hTs
  obtain ⟨Bb, hBq, hBb⟩ := exists_sub_of_ample I hI _ hH hPc Sb hSb
  obtain ⟨B, hBq', hB, hBs⟩ := GlobalTheory.T.closed_system_restriction_subobject I O hPc hE f hf S hS Sb hb Bb hBq hBb
  exact ⟨B, hBq', GlobalTheory.T.closed_system_open_ideal_containment I hI O hPc hE f hf (Sb 0) T hcl (hc 0) Bb hBq (hBb 0) B hBs, hB⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowestStatement
section
open PositivityTheory.RgBcC.RealD (gelA)

theorem GlobalTheory.T.gelfand_invariant_eval_lowest :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
        (∀ a b, b < a → ∀ v, ev (E a b v) = 0) →
        (∀ a v, ev (E a a v) = x a * ev v) →
        ∀ (m : ℕ) (v : V), ev (gelA E m v) =
          GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v :=
  GlobalTheory.CompanionTheory.EvGel.ev_gelA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg

section Quot

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y]
  [Module ℂ Y]

end Quot

section Main

variable {k : Type} [Field k] [TopologicalSpace k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem isGeneric_of_surjective {τ : Representation ℂ (GL (Fin N) k) W} {π : Representation ℂ (GL (Fin N) k) V}
    (q : τ.IntertwiningMap π) (hq : Function.Surjective q) (h : IsGeneric π) : IsGeneric τ := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ, h1, h2, nontrivial_twJacquet_of_surjective q.toLinearMap hq
    (fun u v => Submodule.subset_span ⟨u, q v, ?_⟩) h3⟩
  rw [map_sub, map_smul]
  exact congrArg (· - _) (q.isIntertwining _ _ _ v)

end Main

end GlobalTheory.CompanionTheory.BZSeg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterConjIsOpen
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.TopGroup

theorem inter_conj_isOpen :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsOpen (J : Set G) → ∀ g : G,
        IsOpen ((J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro G _ _ _ J hJ g
  have hpre : ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (fun x : G => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hcont : Continuous (fun x : G => g⁻¹ * x * g) := by fun_prop
  have h2 : IsOpen ((J.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [hpre]; exact hJ.preimage hcont
  rw [Subgroup.coe_inf]
  exact hJ.inter h2

end GlobalTheory.CompanionTheory.TopGroup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDominantOneAndMul
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem isDominant_one_and_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (J : Subgroup (GL (Fin N) k)) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N),
      IsDominant k N J d hd 1 ∧ ∀ t t' : Levi k (Bl d), IsDominant k N J d hd t →
        IsDominant k N J d hd t' → IsDominant k N J d hd (t * t') := by
  intro k _ _ _ _ N J h d hd
  refine ⟨⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ?_⟩, ?_⟩
  · simpa using hn
  · simpa using hn
  · simpa using hx
  · rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · have key := h1 _ (h1' n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := h2' _ (h2 n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := (h3 _ (h3' x hx).1).1
      convert key using 1
      group
    · have key := (h3' _ (h3 x hx).2).2
      convert key using 1
      group

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityNeZeroSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), Zc.jm x hd π ≠ 0 → ∃ S T : Subrepresentation (jac (stdBlocks (fun a => (x a).1) hd) π), Nonempty ((subQuot S T).Equiv (piTensor fun a => (x a).rep)) := by
  first | exact @GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero | exact GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero | (intros; apply GlobalTheory.CompanionTheory.JmSub.exists_subQuot_of_jm_ne_zero <;> assumption)
end

