module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsupp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSemisimpleOnLOldSpace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.BlochKatoRank

theorem rank_subquotient_eq {O K X Y : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module K Y] [Module O Y]
    [IsScalarTower O K Y] (φ : X →ₗ[O] Y) (Z B A : Submodule O X) (Zf BV : Submodule K Y)
    (h1 : ∀ a ∈ A, φ a ∈ Zf) (h2 : ∀ b ∈ B, φ b ∈ BV)
    (h3 : ∀ a, φ a ∈ BV → ∃ m : O, m ≠ 0 ∧ m • a ∈ B)
    (h4 : ∀ y ∈ Zf, ∃ m : O, m ≠ 0 ∧ ∃ a ∈ Z, a ∈ A ∧ φ a = m • y) :
    Module.rank O ((A.comap Z.subtype).map (Submodule.mkQ (B.comap Z.subtype))) =
      Module.rank K (Zf ⧸ BV.comap Zf.subtype) := by
  let A' := A.comap Z.subtype
  let g : A' →ₗ[O] (Z ⧸ B.comap Z.subtype) := (Submodule.mkQ _).comp A'.subtype
  have hg : LinearMap.range g = A'.map (Submodule.mkQ (B.comap Z.subtype)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let f0 : A' →ₗ[O] Zf :=
    { toFun := fun a => ⟨φ a.1.1, h1 _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  let f : A' →ₗ[O] (Zf ⧸ BV.comap Zf.subtype) :=
    ((Submodule.mkQ (BV.comap Zf.subtype)).restrictScalars O).comp f0
  have hgk : ∀ a : A', g a = 0 ↔ a.1.1 ∈ B := fun a => Submodule.Quotient.mk_eq_zero _
  have hfk : ∀ a : A', f a = 0 ↔ φ a.1.1 ∈ BV := fun a => Submodule.Quotient.mk_eq_zero _
  have hle : LinearMap.ker g ≤ LinearMap.ker f := fun a ha =>
    (hfk a).2 (h2 _ ((hgk a).1 ha))
  let F := (LinearMap.ker g).liftQ f hle
  haveI : IsLocalizedModule (nonZeroDivisors O) F := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ?_⟩
    · have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b h => ?_, fun a => ⟨(algebraMap O K s)⁻¹ • a, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul K, ← algebraMap_smul K (s : O) b] at h
        exact smul_right_injective _ hs h
      · rw [Module.algebraMap_end_apply, ← algebraMap_smul K, smul_inv_smul₀ hs]
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨m, hm, a, haZ, haA, ha⟩ := h4 y.1 y.2
      refine ⟨(Submodule.Quotient.mk ⟨⟨a, haZ⟩, haA⟩, ⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩), ?_⟩
      have : f0 ⟨⟨a, haZ⟩, haA⟩ = m • y := Subtype.ext ha
      change m • ((BV.comap Zf.subtype).mkQ.restrictScalars O) y =
        ((BV.comap Zf.subtype).mkQ.restrictScalars O) (f0 ⟨⟨a, haZ⟩, haA⟩)
      rw [this, map_smul]
    · rw [← sub_eq_zero, ← map_sub] at h
      suffices H : ∃ m : O, m ≠ 0 ∧ m • (x - y) = 0 by
        obtain ⟨m, hm, H⟩ := H
        exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, by
          rw [smul_sub, sub_eq_zero] at H; exact H⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x - y)
      rw [← ha] at h ⊢
      obtain ⟨m, hm, H⟩ := h3 _ ((hfk a).1 h)
      refine ⟨m, hm, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact (hgk _).2 H
  rw [← hg, ← (LinearMap.quotKerEquivRange g).rank_eq,
    IsLocalization.rank_eq K (nonZeroDivisors O) le_rfl,
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl F]

section Bridge

open GlobalTheory.BlochKatoIntegralScalars

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

include Bw in
theorem natCast_pow_ne_zero (N : ℕ) : (l : O₀) ^ N ≠ 0 := by
  intro h
  have := congrArg Bw.toLL h
  rw [map_pow, map_natCast, map_zero] at this
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))

theorem exists_integral {X : Type} [TopologicalSpace X] [CompactSpace X]
    (c : X → Fin m → ↥Bw.LL.1) (hc : Continuous c) :
    ∃ d : O₀, d ≠ 0 ∧ ∃ f : X → Fin m → O₀, Continuous f ∧
      ∀ g j, Bw.toLL (f g j) = Bw.toLL d * c g j := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc
  refine ⟨(l : O₀) ^ N, natCast_pow_ne_zero Bw N, fun g j => Bw.eO.symm ⟨_, hN g j⟩, ?_, ?_⟩
  · refine continuous_pi fun j => Bw.eO_symm_cont.comp ?_
    exact Continuous.subtype_mk (continuous_const.mul ((continuous_apply j).comp hc)) _
  · intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply, map_pow, map_natCast]

end Bridge

end GlobalTheory.BlochKatoRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSq
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem normSq_hcParam_sub_rhoSq (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ) :
    normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  have hr : rhoSq (p + q) = ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2
      + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    unfold rhoSq
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2) p,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (((p : ℚ) + q - 1) / 2 - (i : ℕ)) ^ 2) q,
      Nat.add_comm p q, Finset.sum_range_add, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> push_cast <;> ring
  rw [hr]
  unfold normSq
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ i : Fin p, hcParam n ap am (Sum.inl i) ^ 2
      = ∑ i : Fin p, wtK n ap am (Sum.inl i) ^ 2
        + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ))
        + ∑ i : Fin p, (((p : ℚ) - q - 1) / 2 - (i : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  have h2 : ∑ j : Fin q, hcParam n ap am (Sum.inr j) ^ 2
      = ∑ j : Fin q, wtK n ap am (Sum.inr j) ^ 2
        + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))
        + ∑ j : Fin q, (((p : ℚ) + q - 1) / 2 - (j : ℕ)) ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hcParam, wtK]
    ring
  rw [h1, h2]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansion
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.DlogOne GlobalTheory.Sieg.Model

namespace GlobalTheory.SiegTwo

theorem map_smF {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (ε : K →+* K') (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : ε (smF c j M ζ a b n) = smF c j M (ε ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite ε, map_ofNat]

theorem map_finsum_zpow {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (θ : ℤ →₀ ℤ) (w : ℤ → ℤ → ℤ) (hw : ∀ k, w k 0 = 0) (ζ : Ω)
    (g : ℤ) : ε (∑ᶠ k : ℤ, ((w k (θ k) : ℤ) : Ω) * ζ ^ (g * k)) = θ.sum fun k n => ((w k n : ℤ) : ℂ) * (ε ζ ^ g) ^ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_support_subset (s := θ.support), map_sum]
  · simp [Finsupp.sum, zpow_mul]
  · intro k hk
    by_contra h
    have : θ k = 0 := by simpa using h
    exact hk (by simp [this, hw])

theorem coeff_sgN {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : GlobalTheory.KZ.Tower Ω ε) (c : ℕ) {N : ℕ}
    (hN : 0 < N) (M : ℕ) (a : ℤ × ℤ) (r : ℚ) :
    (X.exp (sgN X c N M a)).coeff (r * N) = (X.exp (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])).coeff r := by
  have hd : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two] using hN
  have he : ∀ i k, ent (toGQ !![(N : ℤ), 0; 0, 1]) i k = ((!![(N : ℤ), 0; 0, 1] i k : ℤ) : ℚ) := fun i k => by
    simp only [ent, toGQ, dif_pos hd]; rfl
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) (by rw [he]; simp) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M]) r
  rw [he, he, he] at h
  have h0 : eOm ε 0 = 1 := ε.injective (by rw [GalUnits.eps_eOm]; simp [ee])
  simpa [h0, sgN] using h

theorem sgN_two_variable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  intro Ω _ _ _ ε X _ p hp _ L N c A₁ a₂ g _ hg hNa hN hNp hc hcop hA
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨g', rfl⟩ := hNa
  set M := N * p ^ L with hMd
  have hp0 : 0 < p := hp.out.pos
  have hM : 0 < M := by positivity
  have hMq : (M : ℚ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hMc : (M : ℂ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hc6 : Nat.Coprime c 6 := (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_right_right
  have hcM : Nat.Coprime c M := Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_left_right
    (hcop.coprime_mul_left_right.pow_right L)
  have hA2 : ¬ (M : ℤ) ∣ A₁ * c := fun h =>
    hA ((Nat.isCoprime_iff_coprime.2 hcM.symm).dvd_of_dvd_mul_right h)
  have hadm : admitted c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M] := by
    refine ⟨hc, hc6, fun ⟨⟨m, hm⟩, _⟩ => hA2 ⟨m, ?_⟩⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have : (A₁ : ℚ) * c = M * m := by
      rw [hm]; simp only [Matrix.cons_val_zero]; field_simp
    exact_mod_cast this
  have ez : ε (zt ε p L) = ee (1 / (p : ℂ) ^ L) := by rw [zt, GalUnits.eps_eOm]; push_cast; rfl
  have eM : ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by rw [GalUnits.eps_eOm]; push_cast; rfl
  have hz1 : ee (1 / (p : ℂ) ^ L) ^ ((p : ℤ) ^ L) = 1 := by
    rw [← ee_int_mul]; push_cast; rw [mul_one_div_cancel (pow_ne_zero _ hpc)]; simp [ee]
  have hv : ee (((N * g' : ℤ) : ℂ) / M) = ε (zt ε p L) ^ g := by
    have hco : IsCoprime ((p : ℤ) ^ L) (N : ℤ) := (Nat.isCoprime_iff_coprime.2 hNp.symm).pow_left
    obtain ⟨u, hu⟩ := hco.dvd_of_dvd_mul_left (by simpa only [← mul_sub] using hg.dvd : (p : ℤ) ^ L ∣ N * (g - g'))
    rw [ez, show g = g' + (p : ℤ) ^ L * u by linarith, zpow_add₀ (ee_ne_zero _), zpow_mul, hz1, one_zpow, mul_one,
      ← ee_int_mul, hMc]
    congr 1
    push_cast
    field_simp
  obtain ⟨k, a, b, qa, qb, hj, i, hi⟩ := sg_jets hM hadm hA hA2
  rw [hv] at hj hi
  obtain ⟨r1, r2⟩ := exp_of_hasQ X _ _ hM k a (SiegelMem.an_siegel_eq Ω ε X c _ hadm) qa
  set y := X.exp (sgN X c N M (A₁, N * g')) with hy
  have hco : ∀ r : ℤ, y.coeff ((r : ℚ) / (p : ℚ) ^ L) =
      (X.exp (siegel X c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M])).coeff ((r : ℚ) / M) := fun r => by
    rw [← coeff_sgN X c hN M (A₁, N * g')]
    congr 1
    rw [hMq]; field_simp
  have c1 : ∀ n : ℕ, ε (y.coeff (((k + n : ℤ) : ℚ) / (p : ℚ) ^ L)) = a n := fun n => by
    rw [hco, ← r1]; push_cast; rfl
  have c0 : ∀ r : ℤ, r < k → y.coeff ((r : ℚ) / (p : ℚ) ^ L) = 0 := fun r hr => by
    rw [hco]
    refine r2 _ fun n h => ?_
    rw [div_left_inj' (by exact_mod_cast hM.ne')] at h
    have : r = k + n := by exact_mod_cast h
    omega
  have hb := HasQ.coeff_unique hM qb (by
    simpa only [neg_mul, one_mul] using ((_root_.GlobalTheory.Sieg.EisQ.hasQ_cF_one c M A₁ (N * g') hM).mul_conv qa).const_mul (-1))
  choose θ t1 t2 t3 using fun n => exists_finsupp (hj n)
  have cases : ∀ r : ℤ, r < k ∨ ∃ n : ℕ, r = k + n := fun r => by
    rcases lt_or_ge r k with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(r - k).toNat, by omega⟩
  set Θ : ℤ → ℤ → ℤ := fun l r => if r < k then 0 else θ (r - k).toNat l with hΘ
  have T0 : ∀ l r, r < k → Θ l r = 0 := fun l r h => if_pos h
  have T1 : ∀ l (n : ℕ), Θ l (k + n) = θ n l := fun l n => by
    simp only [hΘ]
    rw [if_neg (by omega), add_sub_cancel_left, Int.toNat_natCast]
  refine ⟨Θ, fun r => ?_, ⟨k, T0⟩, fun l r h => ?_, fun r => ?_, fun r => ?_, ?_, k, g * i, ?_⟩
  · rcases cases r with h | ⟨n, rfl⟩
    · exact ⟨0, fun l _ => T0 l r h⟩
    · refine ⟨(θ n).support.sup Int.natAbs, fun l hl => ?_⟩
      rw [T1]
      by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.2 h)
      rw [Int.abs_eq_natAbs] at hl
      omega
  · rcases cases r with h' | ⟨n, rfl⟩
    · exact absurd (T0 l r h') h
    · rw [T1] at h
      refine Dvd.dvd.trans ⟨N, ?_⟩ (t1 n l h)
      rw [hMd]; push_cast; ring
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp [c0 r h', T0 _ r h']
    · simp only [T1]
      apply ε.injective
      rw [c1, map_finsum_zpow ε (θ n) (fun _ m => m) (fun _ => rfl)]
      exact t2 n
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp only [T0 _ r h', mul_zero, Int.cast_zero, zero_mul, finsum_zero]
      rw [finsum_eq_zero_of_forall_eq_zero, neg_zero]
      intro l
      split_ifs with h
      · rw [c0 _ (by omega), mul_zero]
      · rw [zero_mul]
    · simp only [T1]
      apply ε.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_finsum_zpow ε (θ n) (fun l m => l * m) (fun _ => mul_zero _), ← t3 n,
        finsum_eq_sum_of_support_subset (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ)),
        Finset.sum_image (fun _ _ _ _ h => by exact_mod_cast h), hb, map_neg, map_sum]
      · simp only [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, neg_inj]
        refine Finset.sum_congr rfl fun l hl => ?_
        have := Finset.mem_range.1 hl
        rw [map_mul, if_pos (by omega), Int.toNat_natCast, map_smF, eM, ← c1,
          show k + n - l = k + ((n - l : ℕ) : ℤ) by omega]
      · intro l hl
        by_contra h
        apply hl
        dsimp only
        split_ifs with h1
        · rw [c0, mul_zero]
          by_contra h2
          exact h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l.toNat, Finset.mem_range.2 (by omega), by omega⟩))
        · rw [zero_mul]
  · have hz : eOm ε (1 / (M : ℚ)) ^ (N * g') = zt ε p L ^ g := ε.injective (by
      rw [map_zpow₀, map_zpow₀, ← hv, eM, ← ee_int_mul, mul_one_div])
    have m0 : zt ε p L ∈ Subring.closure {zt ε p L} := Subring.subset_closure rfl
    have m1 : (zt ε p L)⁻¹ ∈ Subring.closure {zt ε p L} := by
      have h1 : zt ε p L ^ (p ^ L) = 1 := ε.injective (by
        rw [map_pow, ez, map_one, ← zpow_natCast]; push_cast; exact hz1)
      have : (zt ε p L)⁻¹ = zt ε p L ^ (p ^ L - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hp0 L), h1]
      rw [this]
      exact pow_mem m0 _
    have m2 : ∀ m : ℤ, zt ε p L ^ m ∈ Subring.closure {zt ε p L} := fun m => by
      rcases Int.eq_nat_or_neg m with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast]; exact pow_mem m0 _
      · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem m1 _
    refine _root_.GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring Ω _ c M _ A₁ _ hM hcM hA (by rw [hz]; exact m2 _) ?_
    rw [zpow_neg, hz, ← zpow_neg]
    exact m2 _
  · have := c1 0
    rw [Nat.cast_zero, add_zero] at this
    refine hi.imp (fun h => ε.injective ?_) (fun h => ε.injective ?_)
    · rw [this, h, map_zpow₀, zpow_mul]
    · rw [this, h, map_neg, map_zpow₀, zpow_mul]

end GlobalTheory.SiegTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSmulPos
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.UlSemisimple

theorem toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    (toGL g : Matrix (Fin 2) (Fin 2) ℝ).det = (g.det : ℝ) := by
  unfold toGL
  rw [dite_eq_right hg]
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]
  simp [Matrix.det_fin_two]

theorem slash_smul_pos (k : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] toGL g = c • (f ∣[k] toGL g) := by
  rw [ModularForm.smul_slash]
  congr 1
  simp only [UpperHalfPlane.σ]
  rw [if_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det g hg.ne']; exact_mod_cast hg)]
  rfl

def ulLin (k : ℤ) (l : ℕ) (hl : 0 < l) : Module.End ℂ (ℍ → ℂ) where
  toFun := UlF k l
  map_add' f g := by simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [UlF, hkF, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => slash_smul_pos k _ ?_ c f
    simp [ulFam, Matrix.det_fin_two]
    exact_mod_cast hl

theorem ulLin_apply (k : ℤ) (l : ℕ) (hl : 0 < l) (F : ℍ → ℂ) : ulLin k l hl F = UlF k l F := rfl

def ChiLaw (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (F : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → F ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • F

def oldSp (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (hl : 0 < l) : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) k, ChiLaw N k χ ⇑f₁ ∧ ChiLaw N k χ ⇑f₂ ∧
    F = ⇑f₁ + ⇑f₂ ∣[k] toGL (dg l 1)}
  add_mem' := by
    rintro F G ⟨f₁, f₂, h₁, h₂, rfl⟩ ⟨g₁, g₂, h₁', h₂', rfl⟩
    refine ⟨f₁ + g₁, f₂ + g₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₁ γ hγ, h₁' γ hγ, smul_add]
    · rw [CuspForm.coe_add, SlashAction.add_slash, h₂ γ hγ, h₂' γ hγ, smul_add]
    · rw [CuspForm.coe_add, CuspForm.coe_add, SlashAction.add_slash]; abel
  zero_mem' := ⟨0, 0, fun γ _ => by simp, fun γ _ => by simp, by simp⟩
  smul_mem' := by
    rintro c F ⟨f₁, f₂, h₁, h₂, rfl⟩
    have hd : 0 < (dg (l : ℤ) 1).det := by simp [dg, Matrix.det_fin_two]; exact_mod_cast hl
    refine ⟨c • f₁, c • f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₁ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, ModularForm.SL_smul_slash, h₂ γ hγ, smul_comm]
    · rw [CuspForm.coe_smul, CuspForm.coe_smul, slash_smul_pos k _ hd, smul_add]

theorem aeval_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (U : Module.End ℂ M) (O : Submodule ℂ M)
    (hU : ∀ x ∈ O, U x ∈ O) (p : ℂ[X]) (x : M) (hx : x ∈ O) : aeval U p x ∈ O := by
  have hpow : ∀ m : ℕ, ∀ y ∈ O, (U ^ m) y ∈ O := by
    intro m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hU _ (ih y hy)
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  exact O.sum_mem fun i _ => by rw [LinearMap.smul_apply]; exact O.smul_mem _ (hpow i x hx)

end GlobalTheory.HeckeFamilyMatrices.UlSemisimple


open GlobalTheory.HeckeFamilyMatrices.UlSemisimple in
theorem GlobalTheory.HeckeFamilyMatrices.ul_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) → α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 2) →
  ∀ f : CuspForm (Lev N l) (k : ℤ), (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] ⇑f = 0 → UlF (k : ℤ) l ⇑f = α • ⇑f := by
  intro N l k hN hl hlN hk χ α hα1 hα2 f hf n hn
  have hl0 : 0 < l := hl.pos
  set U := ulLin (k : ℤ) l hl0 with hUdef
  set O := oldSp N l (k : ℤ) χ hl0 with hOdef
  have hUO : ∀ F ∈ O, U F ∈ O := by
    rintro F ⟨f₁, f₂, h₁, h₂, rfl⟩
    obtain ⟨g₁, g₂, hg₁, hg₂, he⟩ := (_root_.GlobalTheory.OldSpace.ul_oldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).1
    exact ⟨g₁, g₂, hg₁, hg₂, he⟩
  set c : ℂ := χ l * (l : ℂ) ^ (k - 2) with hc
  have hcop : IsCoprime ((X - C α) ^ n) (X ^ 2 - C c) := by
    apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C α).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def]
    simpa [sub_eq_zero] using hα2
  obtain ⟨A, B, hAB⟩ := hcop
  have key : aeval U A (aeval U ((X - C α) ^ n) ⇑f) + aeval U B (aeval U (X ^ 2 - C c) ⇑f) = ⇑f := by
    have := congrArg (fun p => aeval U p ⇑f) hAB
    simpa only [map_add (f := _), map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.one_apply] using this
  have h1 : aeval U ((X - C α) ^ n) ⇑f = 0 := by
    rw [map_pow, map_sub, aeval_X, aeval_C, Module.End.pow_apply]
    convert hn using 2
    funext F
    simp [hUdef, ulLin_apply, Module.algebraMap_end_apply]
  have h2 : aeval U (X ^ 2 - C c) ⇑f ∈ O := by
    obtain ⟨f₁, f₂, h₁, h₂, he⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.ulSq_old N l k hN hl hlN hk χ f hf
    refine ⟨f₁, f₂, h₁, h₂, ?_⟩
    rw [← he, map_sub, aeval_C, map_pow, aeval_X, LinearMap.sub_apply, Module.algebraMap_end_apply,
      pow_two, Module.End.mul_apply]
    rfl
  have hfO : ⇑f ∈ O := by
    rw [← key, h1, map_zero, zero_add]
    exact aeval_mem U O hUO B _ h2
  obtain ⟨f₁, f₂, h₁, h₂, he⟩ := hfO
  have hss := (_root_.GlobalTheory.OldSpace.ul_oldSpace N l k hN hl hlN hk χ α hα1 f₁ f₂ h₁ h₂).2 n
  rw [he] at hn ⊢
  exact hss hn

end
end

