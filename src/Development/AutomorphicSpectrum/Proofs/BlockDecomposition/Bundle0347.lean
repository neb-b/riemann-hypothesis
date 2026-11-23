module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0003
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0007
public import GroundTheory.AutomorphicForms.AdelicGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionCongruence
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.Dblock.CartanCover

theorem sum_tel (A : ℕ → ℤ) (i n : ℕ) (h : i ≤ n) :
    ∑ j ∈ Finset.range n, (if i ≤ j then A j - A (j + 1) else 0) = A i - A n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro j hj
      rw [if_neg]
      simpa using hj
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, if_pos hn]
    ring

theorem exists_lamOf (N : ℕ) (hN : 1 ≤ N) (a : Fin N → ℤ) (ha : Antitone a) :
    ∃ g : Fin (N - 1) → ℕ, ∀ i, Zls.lamOf g i = a i - a ⟨N - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  let A : ℕ → ℤ := fun j => a ⟨min j n, by omega⟩
  have hA : ∀ j, A (j + 1) ≤ A j := fun j => ha (by simp only [Fin.le_def]; omega)
  refine ⟨fun j => (A j - A (j + 1)).toNat, fun i => ?_⟩
  have h1 := sum_tel A i n (by omega)
  rw [Finset.sum_range] at h1
  have hi : A i = a i := by
    simp only [A]
    congr 1
    ext
    simp only
    omega
  have hn : A n = a ⟨n + 1 - 1, by omega⟩ := by
    simp only [A]
    congr 1
    ext
    simp
  rw [← hi, ← hn, ← h1]
  unfold Zls.lamOf
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · exact Int.toNat_of_nonneg (by linarith [hA j])
  · rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

noncomputable abbrev red (N m : ℕ) :
    GL (Fin N) 𝒪[k] →* GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))

noncomputable abbrev incl (N : ℕ) : GL (Fin N) 𝒪[k] →* GL (Fin N) k :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k)

theorem finite_red (N m : ℕ) : Finite (GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m})) := by
  haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k
  haveI : Finite (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) :=
    GlobalTheory.CompanionTheory.Congruence.finite_quotient_span_pow 𝒪[k] (Zls.unif k) m Zls.irreducible_unif
  infer_instance

theorem diag_eq (N : ℕ) (a : Fin N → ℤ) (g : Fin (N - 1) → ℕ) (c : ℤ)
    (hg : ∀ i, Zls.lamOf g i = a i - c) :
    (Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ (a i)) : Matrix (Fin N) (Fin N) k) =
      ((Zls.diagPow k N (Zls.lamOf g) * Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) :
        GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
  have h1 : ((Zls.diagPow k N (Zls.lamOf g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ Zls.lamOf g i : kˣ) : k) := rfl
  have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ c) : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun _ => ((Zls.unifU k ^ c : kˣ) : k) := rfl
  rw [Units.val_mul, h1, h2, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Units.val_mul, ← zpow_add, hg, sub_add_cancel, Units.val_zpow_eq_zpow_val]
  rfl

theorem cartan_cover : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m : ℕ), 1 ≤ m → 1 ≤ N → ∃ s : Finset (GL (Fin N) k × GL (Fin N) k), (∀ p ∈ s, p.1 ∈ KO k (Fin N) ∧ p.2 ∈ KO k (Fin N)) ∧ ∀ h : GL (Fin N) k, ∃ p ∈ s, ∃ g : Fin (N - 1) → ℕ, ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, ∃ z ∈ Subgroup.center (GL (Fin N) k), h = p.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.2 * z := by
  intro k _ _ _ _ N m _ hN
  classical
  haveI : IsFractionRing 𝒪[k] k := GlobalTheory.CompanionTheory.LocalFieldValuationRing.isFractionRing_integer k
  haveI := finite_red k N m

  have hsec : ∀ u : GL (Fin N) 𝒪[k], ∃ w : GL (Fin N) 𝒪[k], red k N m w = red k N m u := fun u => ⟨u, rfl⟩
  let σ : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) → GL (Fin N) 𝒪[k] := fun c =>
    if hc : ∃ w, red k N m w = c then hc.choose else 1
  have hσ : ∀ u, red k N m (σ (red k N m u)) = red k N m u := fun u => by
    have hc : ∃ w, red k N m w = red k N m u := hsec u
    simp only [σ, dif_pos hc]
    exact hc.choose_spec
  let f : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) × GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) →
      GL (Fin N) k × GL (Fin N) k := fun c => (incl k N (σ c.1), incl k N (σ c.2))
  refine ⟨(Set.finite_range f).toFinset, ?_, fun h => ?_⟩
  · intro p hp
    obtain ⟨c, rfl⟩ := (Set.Finite.mem_toFinset _).1 hp
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · have hh : IsUnit (h : Matrix (Fin N) (Fin N) k).det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
    obtain ⟨u, v, a, hu, hv, ha, e⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists 𝒪[k] k N (Zls.unif k)
      Zls.irreducible_unif (h : Matrix (Fin N) (Fin N) k) hh
    obtain ⟨g, hg⟩ := exists_lamOf N hN a ha
    let U : GL (Fin N) 𝒪[k] := Matrix.nonsingInvUnit u hu
    let V : GL (Fin N) 𝒪[k] := Matrix.nonsingInvUnit v hv
    let z : GL (Fin N) k := Matrix.GeneralLinearGroup.scalar (Fin N) (Zls.unifU k ^ a ⟨N - 1, by omega⟩)
    have hz : z ∈ Subgroup.center (GL (Fin N) k) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    have hzc : ∀ w : GL (Fin N) k, z * w = w * z := fun w => ((Subgroup.mem_center_iff.1 hz) w).symm
    have hmat : h = incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V := by
      apply Units.ext
      rw [e, diag_eq k N a g _ hg]
      rfl
    let p₁ := σ (red k N m U)
    let p₂ := σ (red k N m V)
    have hx : p₁⁻¹ * U ∈ (red k N m).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    have hy : V * p₂⁻¹ ∈ (red k N m).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel]
    refine ⟨f (red k N m U, red k N m V), (Set.Finite.mem_toFinset _).2 ⟨_, rfl⟩, g,
      incl k N (p₁⁻¹ * U), ⟨_, hx, rfl⟩, incl k N (V * p₂⁻¹), ⟨_, hy, rfl⟩, z, hz, ?_⟩
    simp only [f, map_mul, map_inv]
    rw [hmat]
    have hzV : ∀ w : GL (Fin N) k, w * z = z * w := fun w => (hzc w).symm
    change incl k N U * (Zls.diagPow k N (Zls.lamOf g) * z) * incl k N V =
      incl k N p₁ * ((incl k N p₁)⁻¹ * incl k N U) * Zls.diagPow k N (Zls.lamOf g) *
        (incl k N V * (incl k N p₂)⁻¹) * incl k N p₂ * z
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    rw [hzc (incl k N V), mul_inv_cancel_left]

end GlobalTheory.CompanionTheory.Dblock.CartanCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClOfSelf
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.WordProd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open Classical in
def clOf (a : IrrGL (k := k)) (d : ℕ) : IrrCl (GL (Fin d) k) :=
  if h : a.1 = d then h ▸ a.2 else (IrrRep.det (Fin d) 1 isSmoothChar_one).cl

theorem clOf_self (a : IrrGL (k := k)) : clOf a a.1 = a.2 := by
  simp [clOf]

end GlobalTheory.CompanionTheory.WordProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitone
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceSubgroups

theorem Km_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  intro k _ _ _ _ N m m' h
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  have hle : Ideal.span {Zls.unif k ^ m'} ≤ Ideal.span {Zls.unif k ^ m} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h)
  have hg' : Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m'})) g = 1 := hg
  have h2 := congrArg (Matrix.GeneralLinearGroup.map (n := Fin N) (Ideal.Quotient.factor hle)) hg'
  rw [map_one] at h2
  show Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})) g = 1
  rw [← h2]
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

end GlobalTheory.CompanionTheory.CongruenceSubgroups
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupBasisNhds
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unif_lt_one : valuation k (algebraMap 𝒪[k] k (Zls.unif k)) < 1 := by
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 Zls.irreducible_unif.not_isUnit

theorem val_le_val_unif (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k (algebraMap 𝒪[k] k (Zls.unif k)) := by
  let y : 𝒪[k] := ⟨x, hx.le⟩
  have hy : ¬ IsUnit y :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hx
  have hmem : y ∈ IsLocalRing.maximalIdeal 𝒪[k] := hy
  rw [Zls.irreducible_unif.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hx' : x = algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) := by
    rw [← map_mul, hc]; rfl
  rw [hx', map_mul]
  exact mul_le_of_le_one_left' c.2

theorem val_sub_one_le_of_mem_Km {N m : ℕ} {g : GL (Fin N) k} (hg : g ∈ Zls.Km k N m) (i j : Fin N) :
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (algebraMap 𝒪[k] k (Zls.unif k) ^ m) := by
  obtain ⟨h, hker, rfl⟩ := Subgroup.mem_map.1 hg
  have h1 := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) =>
    u.1 i j) (MonoidHom.mem_ker.1 hker)
  have h2 : (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))
      ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) = 0 := by
    rw [map_sub, sub_eq_zero]
    simpa [Matrix.one_apply, apply_ite] using h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
  obtain ⟨c, hc⟩ := h2
  have h3 : ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j =
      algebraMap 𝒪[k] k c * algebraMap 𝒪[k] k (Zls.unif k) ^ m := by
    rw [← map_pow, ← map_mul, hc, map_sub]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [h3, map_mul]
  exact mul_le_of_le_one_left' c.2

theorem exists_Km_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (U : Set (GL (Fin N) k)), IsOpen U →
    (1 : GL (Fin N) k) ∈ U → ∃ m : ℕ, 1 ≤ m ∧ (Zls.Km k N m : Set (GL (Fin N) k)) ⊆ U := by
  intro k _ _ _ _ N U hU h1
  have hne : algebraMap 𝒪[k] k (Zls.unif k) ≠ 0 :=
    (map_ne_zero_iff (algebraMap 𝒪[k] k) (IsFractionRing.injective 𝒪[k] k)).2
      Zls.irreducible_unif.ne_zero
  obtain ⟨m, hm, hsub⟩ := exists_congruence_subset k N (algebraMap 𝒪[k] k (Zls.unif k)) hne
    val_unif_lt_one val_le_val_unif U (hU.mem_nhds h1)
  exact ⟨m, hm, fun g hg => hsub fun i j => val_sub_one_le_of_mem_Km hg i j⟩

end GlobalTheory.CompanionTheory.CongruenceBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupFiniteVolume
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_integralGL (N : ℕ) :
    IsCompact {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
      ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  have hO : IsCompact ((𝒪[k] : Subring k) : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hM : IsCompact {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    have h := isCompact_univ_pi fun _ : Fin N => isCompact_univ_pi fun _ : Fin N => hO
    have e : {A : Matrix (Fin N) (Fin N) k | ∀ i j, A i j ∈ 𝒪[k]} =
        Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Fin N => ((𝒪[k] : Subring k) : Set k) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    exact e ▸ h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin N) (Fin N) k)).isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
    have : A = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective e
    exact this ▸ hA i j⟩⟩

theorem Km_subset_integralGL (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) ⊆
      {g : GL (Fin N) k | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]) ∧
        ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]} := by
  have key : ∀ (h : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] := fun h i j =>
    ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j).2
  rintro g ⟨h, -, rfl⟩
  refine ⟨key h, fun i j => ?_⟩
  rw [← map_inv]
  exact key h⁻¹ i j

theorem measure_image_Km_lt_top : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) < ⊤ := by
  intro k _ _ _ _ N _ _ μ hμ m
  refine lt_of_le_of_lt (measure_mono (Set.image_mono (Km_subset_integralGL N m))) ?_
  exact ((isCompact_integralGL N).image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.KmVol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

namespace GlobalTheory.CompanionTheory.CTFin.IwaAd

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {a r : ℕ} (x : BlockIx a r → R) :
    GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM (fun p => f (x p)) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (r s : ℕ)
    (m : GL (Fin r) R × GL (Fin s) R) :
    GeneralLinearGroup.map f (lev R r s m) =
      lev S r s (GeneralLinearGroup.map f m.1, GeneralLinearGroup.map f m.2) := by
  apply Units.ext
  ext i j
  change f (((lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) i j) = ((lev S r s _ : GL (Fin (r + s)) S) : Matrix _ _ S) i j
  have val_emb (T : Type) [CommRing T] (g : GL (Fin r) T × GL (Fin s) T) :
      (GlobalTheory.SmGL.emb₂ T (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g : Matrix _ _ T) =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
          (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
    obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb,
        GlobalTheory.SmGL.leviTwo, GlobalTheory.SmGL.two, Matrix.blockDiagonal'_apply]
  rw [lev, lev, val_emb, val_emb]
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem exists_finset_cover (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Subgroup (GL (Fin n) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin n) (Af E)))) :
    ∃ T : Finset (GL (Fin n) (Af E)), ∀ c ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n,
      ∃ t ∈ T, ∃ l ∈ L, c = t * l := by
  obtain ⟨T, hT⟩ := (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).elim_finite_subcover
    (fun t : GL (Fin n) (Af E) => (fun z => t⁻¹ * z) ⁻¹' (L : Set (GL (Fin n) (Af E))))
    (fun t => hL.preimage (continuous_const.mul continuous_id))
    (fun c _ => Set.mem_iUnion.2 ⟨c, by simp [L.one_mem]⟩)
  refine ⟨T, fun c hc => ?_⟩
  obtain ⟨t, ht, hl⟩ := Set.mem_iUnion₂.1 (hT hc)
  exact ⟨t, ht, t⁻¹ * c, hl, by group⟩

theorem iwasawa_finite_cosets : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  intro E _ _ _ r s L hL
  obtain ⟨T, hT⟩ := exists_finset_cover E (r + s) L hL
  refine ⟨T, fun g => ?_⟩
  obtain ⟨b, hb, k, hy⟩ := GlobalTheory.IwasawaAdelic.exists_upper_mul_unitary_inf E (r + s)
    (GeneralLinearGroup.map (pInf E) g)
  have hb' : (((b⁻¹ : GL (Fin (r + s)) (Cinf E))) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)).BlockTriangular id := by
    letI : Invertible (b : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  obtain ⟨xi, mi, hbi⟩ := IwaFin.exists_unip_mul_lev r s b
    (fun i j hi hj => hb (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
    (fun i j hi hj => hb' (show j < i from Fin.lt_def.2 (lt_of_lt_of_le hj hi)))
  obtain ⟨xf, mf, c, hc, hf⟩ := IwaFin.exists_unip_lev_integral E r s (GeneralLinearGroup.map (pFin E) g)
  obtain ⟨t, ht, l, hl, rfl⟩ := hT c hc
  have e1 : ∀ p, pInf E (sInf E (xi p) + sFin E (xf p)) = xi p := fun p => by
    rw [map_add (f := _), show pInf E (sInf E (xi p)) = xi p from (infEq E).symm_apply_apply _,
      show pInf E (sFin E (xf p)) = 0 from map_zero (infEq E).symm, add_zero]
  have e2 : ∀ p, pFin E (sInf E (xi p) + sFin E (xf p)) = xf p := fun p => by
    rw [map_add (f := _), show pFin E (sInf E (xi p)) = 0 from rfl, show pFin E (sFin E (xf p)) = xf p from rfl, zero_add]
  refine ⟨fun p => sInf E (xi p) + sFin E (xf p),
    (infGL E r mi.1 * finGL E r mf.1, infGL E s mi.2 * finGL E s mf.2), t, k, l, ht, hl, ga_ext ?_ ?_⟩
  · simp only [map_mul, map_unip, map_lev, e1, pInf_infGL, pInf_finGL, mul_one, one_mul]
    rw [hy, hbi]
  · simp only [map_mul, map_unip, map_lev, e2, pFin_infGL, pFin_finGL, mul_one, one_mul]
    rw [hf, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.IwaAd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingUnitAbsPowBounds
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.TopNilp

theorem nabs_absPow_of_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  intro k _ _ _ _ t ht
  have hpos : 0 < nabs k t := nabs_pos' k t
  refine ⟨hpos, ?_, fun d => ?_⟩
  · by_contra hge
    have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (t : k) :=
      (nabs_le_iff 1 t).1 (by rw [nabs_one k]; exact not_lt.1 hge)
    rw [Units.val_one, map_one] at h1
    obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hr0 : r ≠ 0 := by simpa using hr
    have hnh : cball (Units.mk0 r hr0) ∈ 𝓝 (0 : k) :=
      (isOpen_cball _).mem_nhds (by simp [cball])
    obtain ⟨n, hn⟩ := (ht.eventually hnh).exists
    have h2 : valuation k ((t : k) ^ n) ≤ valuation k r := hn
    rw [map_pow] at h2
    exact absurd ((one_le_pow₀ h1).trans h2) (not_le.2 hr1)
  · rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le]

end GlobalTheory.CompanionTheory.TopNilp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_twist_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (hx : x.IsCusp) (a b : ℕ) (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  first | exact @GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | exact GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | (intros; apply GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCoweightAdditiveFundamental
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamOf

theorem lamOf_add_and_single :
    ∀ (N : ℕ), (∀ g g' : Fin (N - 1) → ℕ, Zls.lamOf (g + g') = Zls.lamOf g + Zls.lamOf g') ∧
      ∀ j : Fin (N - 1), Zls.lamOf (Pi.single j 1) = Zls.omegaVec N ((j : ℕ) + 1) := by
  intro N
  refine ⟨fun g g' => ?_, fun j => ?_⟩
  · funext i
    simp only [Zls.lamOf, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  · funext i
    simp only [Zls.lamOf, Zls.omegaVec]
    rw [Finset.sum_eq_single j]
    · by_cases h : (i : ℕ) ≤ (j : ℕ)
      · simp [h, Nat.lt_succ_of_le h]
      · have h' : ¬ (i : ℕ) < (j : ℕ) + 1 := fun h2 => h (Nat.le_of_lt_succ h2)
        simp [h, h']
    · intro l _ hl
      simp [Pi.single_apply, hl]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

end GlobalTheory.CompanionTheory.LamOf
end

