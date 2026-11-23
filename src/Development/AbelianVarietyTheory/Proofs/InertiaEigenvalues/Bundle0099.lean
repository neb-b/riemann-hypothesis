module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem valuation_map_eq_of_unr (hU : IsUnrExt K K' d φ) (x : K.E) :
    (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hU.2.2.1 x
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  have h0' : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_log h0']
  congr 1
  omega

theorem exists_intMap_of_unr (hU : IsUnrExt K K' d φ) :
    ∃ ψ : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ψ a) = φ (algebraMap K.O K.E a) := by
  choose f hf using exists_int_image hU
  have inj := IsFractionRing.injective K'.O K'.E
  let ψ : K.O →+* K'.O :=
    { toFun := f, map_one' := inj (by simp only [hf, map_one]),
      map_mul' := fun a b => inj (by simp only [hf, map_mul]),
      map_zero' := inj (by simp only [hf, map_zero]),
      map_add' := fun a b => inj (by simp only [hf, map_add (f := _)]) }
  exact ⟨ψ, hf⟩

theorem exists_int_basis_of_unr (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_intMap_of_unr hU
  have hv := valuation_map_eq_of_unr hU
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hvdef
  set v' := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv'def

  have memK : ∀ a : K.O, a ∈ maximalIdeal K.O ↔ v (algebraMap K.O K.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K.O) a).symm
  have memK' : ∀ a : K'.O, a ∈ maximalIdeal K'.O ↔ v' (algebraMap K'.O K'.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K'.O) a).symm
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal K.O := (mem_maximalIdeal a).2 hna
    have h2 : ψ a ∈ maximalIdeal K'.O := by
      rw [memK', hψ, hv]; exact (memK a).1 h1
    exact (mem_maximalIdeal _).1 h2 ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ψ).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hfr : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have h1 := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    have c1 : Fintype.card (ResidueField K.O) = K.q ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact K.card_res
    have c2 : Fintype.card (ResidueField K'.O) = (K.q ^ 2) ^ d := by
      rw [← Nat.card_eq_fintype_card, K'.card_res, hU.1, ← pow_mul, ← pow_mul, mul_comm]
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← c1]; exact Fintype.one_lt_card
    rw [c1, c2] at h1
    exact (Nat.pow_right_injective h2 h1).symm
  let b := Module.finBasisOfFinrankEq (ResidueField K.O) (ResidueField K'.O) hfr
  choose u hu using fun i => IsLocalRing.residue_surjective (b i)

  have hres : ∀ c : Fin d → K.O, ∀ j, c j = 1 → ∑ i, ψ (c i) * u i ∉ maximalIdeal K'.O := by
    intro c j hj hmem
    have h0 : residue K'.O (∑ i, ψ (c i) * u i) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h0
    simp only [map_mul, ← ResidueField.map_residue, hu] at h0
    have h1 : ∑ i, residue K.O (c i) • b i = 0 := by
      simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h0
    have := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 j
    rw [hj, map_one] at this
    exact one_ne_zero this

  set U : Fin d → K'.E := fun i => algebraMap K'.O K'.E (u i) with hUdef

  have key : ∀ e : Fin d → K.E, ∀ j, (∀ i, v (e i) ≤ v (e j)) → e j ≠ 0 →
      v (e j) ≤ v' (∑ i, φ (e i) * U i) := by
    intro e j hmax hj
    have hpos : 0 < v (e j) := zero_lt_iff.2 (by simpa using hj)
    have hc : ∀ i, ∃ a : K.O, algebraMap K.O K.E a = e i / e j := fun i =>
      IsDiscreteValuationRing.exists_lift_of_le_one (by
        rw [map_div₀]; exact (div_le_one₀ hpos).2 (hmax i))
    choose a ha using hc
    have haj : a j = 1 := IsFractionRing.injective K.O K.E (by rw [ha, div_self hj, map_one])
    have h1 := hres a j haj
    rw [memK', not_lt] at h1
    have h2 : algebraMap K'.O K'.E (∑ i, ψ (a i) * u i) = ∑ i, φ (e i / e j) * U i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hψ, ha, hUdef]
    have h3 : ∑ i, φ (e i) * U i = φ (e j) * ∑ i, φ (e i / e j) * U i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hj]
    rw [h3, map_mul, hv, ← h2]
    exact le_mul_of_one_le_right' h1
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hsmul : ∀ (x : K.E) (y : K'.E), x • y = φ x * y := fun x y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent K.E U := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i)) ⟨i, Finset.mem_univ i⟩
    have hgi : 0 < v (g i) := zero_lt_iff.2 (by simpa using hi)
    have hgj : g j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd this (not_le.2 hgi)
    have := key g j (fun i => hj i (Finset.mem_univ i)) hgj
    simp only [← hsmul] at this
    rw [hg, map_zero] at this
    exact hgj ((map_eq_zero v).1 (le_antisymm this zero_le'))
  have hd : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : Nonempty (Fin d) := by
    have : 0 < d := hfr ▸ Module.finrank_pos
    exact ⟨⟨0, this⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hd])
  refine ⟨u, fun y => ?_⟩
  have hy : algebraMap K'.O K'.E y ∈ Submodule.span K.E (Set.range U) := hspan ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun K.E).1 hy
  have hint : ∀ i, v (e i) ≤ 1 := by
    intro i
    by_contra hi
    rw [not_le] at hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (e i)) ⟨i, Finset.mem_univ i⟩
    have hej : e j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd (lt_of_lt_of_le hi this) (not_lt.2 zero_le')
    have h1 := key e j (fun i => hj i (Finset.mem_univ i)) hej
    simp only [← hsmul] at h1
    rw [he] at h1
    have h2 := HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K'.O) (K := K'.E) y
    exact absurd (lt_of_lt_of_le hi (le_trans (hj i (Finset.mem_univ i)) (le_trans h1 h2))) (lt_irrefl _)
  choose a ha using fun i => IsDiscreteValuationRing.exists_lift_of_le_one (hint i)
  refine ⟨a, ?_⟩
  rw [← he]
  simp only [hsmul, ha, hUdef]

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralGLMulDiagOneOfUnitIndicatorLiftNeZ
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem exists_emb_of_last {F : Type} [Field F] (r : ℕ) (m : GL (Fin (r + 1)) F)
    (hc : (m : Matrix _ _ F) *ᵥ GlobalTheory.JR.Step.eL r F = GlobalTheory.JR.Step.eL r F)
    (hr : GlobalTheory.JR.Step.eL r F ᵥ* (m : Matrix _ _ F) = GlobalTheory.JR.Step.eL r F) :
    ∃ s : GL (Fin r) F, m = GlobalTheory.JR.Step.emb r F s := by
  classical
  set t : Matrix (Fin r) (Fin r) F := (m : Matrix _ _ F).submatrix Fin.castSucc Fin.castSucc with ht
  have hcol : ∀ i, (m : Matrix _ _ F) i (Fin.last r) = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) i := by
    intro i
    have := congrFun hc i
    simpa [GlobalTheory.JR.Step.eL, Matrix.mulVec_single_one] using this
  have hrow : ∀ j, (m : Matrix _ _ F) (Fin.last r) j = (Pi.single (Fin.last r) (1 : F) : Fin (r + 1) → F) j := by
    intro j
    have := congrFun hr j
    simpa [GlobalTheory.JR.Step.eL, Matrix.single_one_vecMul] using this
  have hm : (m : Matrix _ _ F) = GlobalTheory.JR.Step.embHom r F t := by
    ext i j
    induction i using Fin.lastCases with
    | last =>
      rw [hrow j]
      induction j using Fin.lastCases with
      | last => simp [GlobalTheory.JR.Step.embHom]
      | cast j => simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hcol]; simp [GlobalTheory.JR.Step.embHom, Fin.castSucc_ne_last]
      | cast j => simp [GlobalTheory.JR.Step.embHom, ht]
  have hdet : (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F).det = t.det := by
    rw [hm]
    simp [GlobalTheory.JR.Step.embHom, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit t.det := by
    rw [← hdet]
    exact (Matrix.isUnit_iff_isUnit_det (m : Matrix (Fin (r + 1)) (Fin (r + 1)) F)).mp (Units.isUnit m)
  refine ⟨Matrix.nonsingInvUnit t hu, ?_⟩
  ext : 1
  rw [hm]
  rfl

end GlobalTheory.JR.GLift

namespace GlobalTheory.JR.GLift

theorem support_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    ∀ g : GL (Fin (r + 1)) F, unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
      ∃ k ∈ glO (r + 1) F, ∃ s : GL (Fin r) F, g = k * GlobalTheory.JR.Step.emb r F s := by
  intro F E _ _ _ _ _ r Z μ l hμ g hg
  classical
  obtain ⟨-, hb, hc, -⟩ := Set.mem_of_indicator_ne_zero hg
  simp only [act, GlobalTheory.JR.Step.lift] at hb hc
  set e : Fin (r + 1) → F := GlobalTheory.JR.Step.eL r F with he
  have hv : ∀ i, ‖((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) i‖ ≤ 1 := by
    intro i
    have := hb i
    rwa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hμ, one_mul] at this
  have hw : ∀ i, ‖(e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) i‖ ≤ 1 := hc
  have hgg : ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul g
  have hee : e ⬝ᵥ e = 1 := by simp [he, GlobalTheory.JR.Step.eL]
  have hwv : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ⬝ᵥ ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e) = 1 := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, hee]
  obtain ⟨k, hk, hkv, hkw⟩ := GlobalTheory.LatL.glO_transitive_pairs F E r _ _ hv hw hwv
  have hkv' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e = (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) *ᵥ e := hkv
  have hkw' : (e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) ᵥ* (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e := hkw
  have hkk : ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.inv_mul k
  have hkk' : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F) * ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = 1 :=
    Units.mul_inv k
  have hek : e ᵥ* ((k⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) = e ᵥ* ((g⁻¹ : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
    conv_lhs => rw [← hkw']
    rw [Matrix.vecMul_vecMul, hkk', Matrix.vecMul_one]
  obtain ⟨s, hs⟩ := exists_emb_of_last r (k⁻¹ * g) (by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hkv', Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec])
    (by rw [Units.val_mul, ← Matrix.vecMul_vecMul, hek, Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one])
  exact ⟨k, hk, s, by rw [← hs, mul_inv_cancel_left]⟩

end GlobalTheory.JR.GLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIntegralSmallElementPowSmul
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc

theorem dvr_dvd_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a y : O}
    (ha : a ∈ IsLocalRing.maximalIdeal O) (hy : y ≠ 0) : ∃ k : ℕ, y ∣ a ^ k := by
  have hyt : IsDiscreteValuationRing.addVal O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hyt
  have ha1 : 1 ≤ IsDiscreteValuationRing.addVal O a := by
    rw [ENat.one_le_iff_ne_zero, Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
    exact ha
  refine ⟨n, IsDiscreteValuationRing.addVal_le_iff_dvd.1 ?_⟩
  rw [IsDiscreteValuationRing.addVal_pow, ← hn]
  calc ((n : ℕ∞)) = n • (1 : ℕ∞) := by simp
    _ ≤ n • IsDiscreteValuationRing.addVal O a := nsmul_le_nsmul_right ha1 n

theorem smul_pow_integral (K : UQ) (B : InvAlg K) (a : K.O) (ha : K.Small a) (x : B.A) :
    ∃ k : ℕ, IsIntegral K.O ((al K a ^ k) • x) := by
  have hxE : IsIntegral K.E x := Algebra.IsIntegral.isIntegral x
  obtain ⟨⟨m, hm⟩, hmx⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors K.O) x hxE
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, w, hw⟩ := dvr_dvd_pow ha.2.1 hm0
  refine ⟨k, ?_⟩
  have hsm : (m • x : B.A) = (⟨m, hm⟩ : nonZeroDivisors K.O) • x := rfl
  have : (al K a ^ k) • x = algebraMap K.O B.A w * (m • x) := by
    rw [← map_pow, algebraMap_smul, hw, mul_comm, mul_smul, Algebra.smul_def]
  rw [this]
  exact isIntegral_algebraMap.mul (hsm ▸ hmx)

end GlobalTheory.UnitLemma.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLeftMulMatrixOfCommuteCompanion
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.LinDesc

theorem exists_leftMul_of_comm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
    (hG : A.IsGen τ p) (M : Matrix (Fin r) (Fin r) F) (hM : M * companion p = companion p * M) :
    ∃ k : A.K, M = Algebra.leftMulMatrix (bas A hG) k := by
  set b := bas A hG
  set φ : A.K →ₗ[F] A.K := Matrix.toLin b b M with hφ
  have hMφ : LinearMap.toMatrix b b φ = M := by simp [hφ]
  have hlm : ∀ x : A.K, Algebra.leftMulMatrix b x = LinearMap.toMatrix b b (Algebra.lmul F A.K x) := fun x => rfl
  have hτ : φ ∘ₗ Algebra.lmul F A.K τ = Algebra.lmul F A.K τ ∘ₗ φ := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b, hMφ, ← hlm, leftMul_tau]
    exact hM
  have hτx : ∀ x, φ (τ * x) = τ * φ x := fun x => by
    have := congrArg (fun f => f x) hτ
    simpa using this
  have hpow : ∀ (n : ℕ) x, φ (τ ^ n * x) = τ ^ n * φ x := by
    intro n; induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', mul_assoc, hτx, ih, ← mul_assoc]
  have hall : ∀ k x, φ (k * x) = k * φ x := by
    intro k x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr k, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_mul_assoc, bas_apply, hpow]
  refine ⟨φ 1, ?_⟩
  rw [← hMφ, hlm]
  congr 1
  ext x
  rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [mul_comm, ← hall, mul_one]

theorem centr : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (t : GL (Fin r) F), (t : Matrix (Fin r) (Fin r) F) * companion p = companion p * (t : Matrix (Fin r) (Fin r) F) → ∃ t₁ : A.Kˣ, LinDesc.tm A hG t₁ = t := by
  intro F E _ _ _ _ A r τ p hG t ht
  have ht' : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p =
      companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
    have h1 : ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (t : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p
        = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * companion p *
            ((t : Matrix (Fin r) (Fin r) F) * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) := by
          rw [h2, Matrix.mul_one]
      _ = ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * ((t : Matrix (Fin r) (Fin r) F) * companion p) *
            ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [ht]; simp only [Matrix.mul_assoc]
      _ = companion p * ((t⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨k, hk⟩ := exists_leftMul_of_comm A hG _ ht
  obtain ⟨k', hk'⟩ := exists_leftMul_of_comm A hG _ ht'
  have hinj := Algebra.leftMulMatrix_injective (bas A hG)
  have e1 : k * k' = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hk, ← hk', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : k' * k = 1 := by rw [mul_comm, e1]
  refine ⟨⟨k, k', e1, e2⟩, ?_⟩
  apply Units.ext
  rw [tm_coe]
  exact hk.symm

end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittBasis
section
namespace GlobalTheory.UnitLemma.Witt

open GlobalTheory.UnitLemma Polynomial

theorem exists_conj (K : UQ) : ∃ s : K.O →+* K.O,
    ∀ x, algebraMap K.O K.E (s x) = K.c (algebraMap K.O K.E x) := by
  choose f hf using K.c_int
  have inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [← hf]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, ← hf, ← hf, ← hf]; simp)
            map_zero' := inj (by rw [← hf]; simp)
            map_add' := fun x y => inj (by rw [map_add (f := _), ← hf, ← hf, ← hf]; simp) }, fun x => (hf x).symm⟩

end GlobalTheory.UnitLemma.Witt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FewRootsSmallDisc
section
open Polynomial
open Classical

namespace GlobalTheory

theorem roots_taylor_eq_map_sub {K : Type*} [Field K] (p : K[X]) (w : K) :
    (taylor w p).roots = p.roots.map (fun x => x - w) := by
  have h := roots_comp_C_mul_X_add_C p (1 : K) w isUnit_one
  rw [taylor_apply]
  simpa using h

theorem coeff_sum_monomial_pow (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (k : ℕ)
    (hk : k ≤ E) :
    (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff (l ^ k) = a k := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp [coeff_monomial]
  · intro i _ hik
    rw [coeff_monomial, Finsupp.single_apply, if_neg]
    intro h
    exact hik (Nat.pow_right_injective hl h)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_sum_monomial_small (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hgt : ∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) (j : ℕ) (hj : l ^ M < j) :
    ‖(∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j‖ * ρ ^ j
      < ‖(l : ℂ_[l])‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  by_cases h : ∃ k, k ≤ E ∧ l ^ k = j
  · obtain ⟨k, hkE, rfl⟩ := h
    rw [coeff_sum_monomial_pow l E a k hkE]
    have hMk : M < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hj
    exact hgt k hMk hkE
  · have h0 : (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j = 0 := by
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_monomial, Finsupp.single_apply, if_neg]
      intro hij
      exact h ⟨i, by have := Finset.mem_range.mp hi; omega, hij⟩
    rw [h0, norm_zero, zero_mul]
    exact hlpos

theorem few_roots_small_disc : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  intro l _ E M a ρ W hME ha hρ0 hρ1 hM hgt hW
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k) with hG
  set H := taylor W G with hH
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  have hroots : Multiset.card (G.roots.filter fun z => ‖z - W‖ ≤ ρ)
      = Multiset.card (H.roots.filter fun z => ‖z‖ ≤ ρ) := by
    rw [hH, roots_taylor_eq_map_sub, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [hroots]
  have hd1 : 1 ≤ l ^ M := Nat.one_le_pow _ _ (by omega)
  have hGd : G.coeff (l ^ M) = a M := coeff_sum_monomial_pow l E a M hME
  have hdiff : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ ≤ ‖(l : ℂ_[l])‖ :=
    _root_.GlobalTheory.additive_poly_taylor_coeff_sub_norm_le l E a W ha hW
  have hρj : ∀ j, 1 ≤ j → ρ ^ j < 1 := fun j hj => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hdiffsmall : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ * ρ ^ j < ‖(l : ℂ_[l])‖ := by
    intro j hj
    calc ‖H.coeff j - G.coeff j‖ * ρ ^ j ≤ ‖(l : ℂ_[l])‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right (hdiff j hj) (by positivity)
      _ < ‖(l : ℂ_[l])‖ := mul_lt_of_lt_one_right hlpos (hρj j hj)
  have hHd : ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ := by
    have hlt : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ < ‖G.coeff (l ^ M)‖ := by
      have h1 : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ * ρ ^ l ^ M
          < ‖G.coeff (l ^ M)‖ * ρ ^ l ^ M := by
        rw [hGd, hM]; have h0 := hdiffsmall _ hd1; rwa [hGd] at h0
      exact lt_of_mul_lt_mul_right h1 (by positivity)
    have h2 : H.coeff (l ^ M) = G.coeff (l ^ M) + (H.coeff (l ^ M) - G.coeff (l ^ M)) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hGd, hM]
  have hHd0 : H.coeff (l ^ M) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hHd
    exact hlpos.ne hHd
  have hbig : ∀ j, l ^ M < j → ‖H.coeff j‖ * ρ ^ j < ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M := by
    intro j hj
    rw [hHd]
    have h2 : H.coeff j = G.coeff j + (H.coeff j - G.coeff j) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max (G.coeff j) (H.coeff j - G.coeff j)
    rw [← h2] at h3
    have hρ : 0 ≤ ρ ^ j := by positivity
    calc ‖H.coeff j‖ * ρ ^ j ≤ max ‖G.coeff j‖ ‖H.coeff j - G.coeff j‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right h3 hρ
      _ = max (‖G.coeff j‖ * ρ ^ j) (‖H.coeff j - G.coeff j‖ * ρ ^ j) := max_mul_of_nonneg _ _ hρ
      _ < ‖(l : ℂ_[l])‖ := max_lt (coeff_sum_monomial_small l E M a ρ hρ0 hgt j hj)
          (hdiffsmall j (by omega))
  exact (_root_.GlobalTheory.card_roots_le_radius_bounds ℂ_[l] H ρ (l ^ M) hρ0 hHd0).2 hbig

end GlobalTheory
end

