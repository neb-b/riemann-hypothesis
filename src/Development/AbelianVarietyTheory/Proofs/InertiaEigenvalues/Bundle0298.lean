module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerFixedFieldTraceEqSqMulOfAx
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ) (J : Subgroup (L ≃ₐ[F] L)) [J.Normal] (σ₁ : L ≃ₐ[F] L) (c : ℤ), (p : L) ≠ 0 → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∀ σ ∈ J, (p : ℤ) ^ r ∣ a σ) → c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ → ∃ z : 𝒪[↥(IntermediateField.fixedField J)], Algebra.trace F ↥(IntermediateField.fixedField J) (z : ↥(IntermediateField.fixedField J)) = (p : F) ^ 2 * (c : F) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p r x a J _ σ₁ c hp hAx hx hJ hc
  set M := IntermediateField.fixedField J with hMdef
  have hpr : (p : L) ^ r ≠ 0 := pow_ne_zero _ hp
  have hint : ∀ n : ℤ, (n : L) ∈ 𝒪[L] := fun n => intCast_mem _ n
  have hσO : ∀ (σ : L ≃ₐ[F] L) (w : L), w ∈ 𝒪[L] → σ w ∈ 𝒪[L] := by
    intro σ w hw
    rw [Valuation.mem_integer_iff] at hw ⊢
    rwa [valuation_algEquiv_apply F L σ w]
  have hdiff : ∀ σ : L ≃ₐ[F] L, σ (x / (p : L) ^ r) - x / (p : L) ^ r = (σ x - x) / (p : L) ^ r := by
    intro σ
    rw [map_div₀, map_pow, map_natCast, sub_div]

  have hJint : ∀ σ ∈ J, σ (x / (p : L) ^ r) - x / (p : L) ^ r ∈ 𝒪[L] := by
    intro σ hσ
    obtain ⟨z, hz, e⟩ := hx σ
    obtain ⟨k, hk⟩ := hJ σ hσ
    rw [hdiff, e, hk]
    have : (((p : ℤ) ^ r * k : ℤ) : L) + (p : L) ^ r * z = (p : L) ^ r * ((k : L) + z) := by
      push_cast; ring
    rw [this, mul_div_cancel_left₀ _ hpr]
    exact add_mem (hint k) hz
  obtain ⟨y, hyJ, hw⟩ := hAx J (x / (p : L) ^ r) hJint
  obtain ⟨z₁, hz₁, e₁⟩ := hx σ₁
  have hyM : y ∈ M := (IntermediateField.mem_fixedField_iff J y).2 hyJ
  set yM : M := ⟨y, hyM⟩
  set sM : M := σ₁.restrictNormal M yM
  have hsM : (sM : L) = σ₁ y := AlgEquiv.restrictNormal_commutes σ₁ M yM
  have hpF : (p : F) ^ r ≠ 0 := by
    intro h; apply hpr
    have := congrArg (algebraMap F L) h
    simpa using this
  set kF : F := (a σ₁ : F) / (p : F) ^ r
  set zM : M := (p : M) ^ 2 * (algebraMap F M kF - (sM - yM))
  have hzL : (zM : L) = σ₁ ((p : L) ^ 2 * (x / (p : L) ^ r - y)) - (p : L) ^ 2 * (x / (p : L) ^ r - y)
      - (p : L) ^ 2 * z₁ := by
    have h1 : (algebraMap F L kF) = (a σ₁ : L) / (p : L) ^ r := by
      simp [kF]
    have h2 : σ₁ (x / (p : L) ^ r) = x / (p : L) ^ r + (a σ₁ : L) / (p : L) ^ r + z₁ := by
      have := hdiff σ₁
      rw [e₁, add_div, mul_div_cancel_left₀ _ hpr] at this
      linear_combination this
    have h3 : (zM : L) = (p : L) ^ 2 * (algebraMap F L kF - (σ₁ y - y)) := by
      simp only [zM, MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
        IntermediateField.coe_algebraMap_apply, hsM]
      simp [yM]
    rw [h3, map_mul, map_sub, map_pow, map_natCast, h2, h1]
    ring
  have hzO : (zM : L) ∈ 𝒪[L] := by
    rw [hzL]
    exact sub_mem (sub_mem (hσO σ₁ _ hw) hw) (mul_mem (pow_mem (natCast_mem _ p) 2) hz₁)
  have hfin : Module.finrank F M = J.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, hMdef, IntermediateField.fixingSubgroup_fixedField]
  refine ⟨⟨zM, ?_⟩, ?_⟩
  · rw [Valuation.mem_integer_iff] at hzO ⊢
    have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := M) (B := L)
    rw [IntermediateField.valuation_coe, ← map_one (ValuativeExtension.mapValueGroupWithZero M L)] at hzO
    exact hmono.le_iff_le.mp hzO
  · have hz : zM = algebraMap F M ((p : F) ^ 2 * kF) - algebraMap F M ((p : F) ^ 2) * (sM - yM) := by
      simp only [zM, map_mul, map_pow, map_natCast]; ring
    have htr : Algebra.trace F M sM = Algebra.trace F M yM := Algebra.trace_eq_of_algEquiv (σ₁.restrictNormal M) yM
    show Algebra.trace F M zM = _
    rw [hz, map_sub, Algebra.trace_algebraMap, ← Algebra.smul_def, LinearMap.map_smul, map_sub, htr, sub_self,
      smul_zero, sub_zero, hfin, nsmul_eq_mul]
    have hcF : (c : F) * (p : F) ^ r = (J.index : F) * (a σ₁ : F) := by exact_mod_cast congrArg (fun t : ℤ => (t : F)) hc
    have hk : (J.index : F) * kF = c := by
      simp only [kF]
      rw [mul_div_assoc', div_eq_iff hpF]
      linear_combination -hcF
    linear_combination (p : F) ^ 2 * hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctional
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.IntDual

theorem lattice_basis (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ_[l] LL),
      (∀ i, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (b i)) ∧
      ∀ x : LL, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem x →
        ∀ i, ∃ z : ℤ_[l], b.repr x i = (z : ℚ_[l]) := by
  letI : Algebra ℤ_[l] LL := ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] LL := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure ℤ_[l] LL
  haveI : IsIntegralClosure S ℤ_[l] LL := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] S := IsIntegralClosure.finite ℤ_[l] ℚ_[l] LL S
  have hinj : Function.Injective (algebraMap ℤ_[l] LL) := by
    intro a c h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] LL).injective h)
  haveI : Module.IsTorsionFree ℤ_[l] S := ⟨fun r hr a c hac => by
    have hr0 : algebraMap ℤ_[l] LL r ≠ 0 := by
      intro h0; exact hr.ne_zero (hinj (h0.trans (map_zero _).symm))
    apply Subtype.ext
    have h1 := congrArg (fun s : S => (s : LL)) hac
    simp only [Subalgebra.coe_smul, Algebra.smul_def] at h1
    exact mul_left_cancel₀ hr0 h1⟩
  haveI : Module.Free ℤ_[l] S := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors ℤ_[l])) LL :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] LL S
  let bO := (Module.Free.chooseBasis ℤ_[l] S).reindex (Fintype.equivFin _)
  let b := bO.localizationLocalization ℚ_[l] (nonZeroDivisors ℤ_[l]) LL
  have hb : ∀ i, b i = (bO i : LL) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ i
  refine ⟨_, b, fun i => ?_, fun x hx i => ?_⟩
  · rw [hb]; exact (bO i).2
  · have := bO.localizationLocalization_repr_algebraMap ℚ_[l] (nonZeroDivisors ℤ_[l]) LL ⟨x, hx⟩ i
    exact ⟨bO.repr ⟨x, hx⟩ i, this⟩

theorem intDual_coef : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  intro l _ LL _ _ _ O _ _ hO
  have H := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hfd, -, -, -⟩ := hO
  haveI := hdom
  haveI := hdvr
  haveI := hfrac
  haveI := hfd
  have hmem := H.1
  obtain ⟨n, b, hbint, hcoord⟩ := lattice_basis l LL
  let ι := algebraMap O LL
  have hιinj : Function.Injective ι := IsFractionRing.injective O LL
  let Tr := Algebra.trace ℚ_[l] LL
  let B := Algebra.traceForm ℚ_[l] LL
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ_[l] LL
  let f' := B.dualBasis hB b
  have hcoef : ∀ x i, Tr (f' i * x) = b.repr x i := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    have : ∀ j, Tr (f' i * (b.repr x j • b j)) = b.repr x j * (if j = i then 1 else 0) := by
      intro j
      rw [mul_smul_comm, map_smul, smul_eq_mul, ← LinearMap.BilinForm.apply_dualBasis_left hB b i j]
      rfl
    simp_rw [this, mul_ite, mul_one, mul_zero]
    simp

  let Zs : Subring ℚ_[l] := (algebraMap ℤ_[l] ℚ_[l]).range
  have hZ : ∀ q : ℚ_[l], q ∈ Zs ↔ ∃ z : ℤ_[l], q = (z : ℚ_[l]) := by
    intro q; constructor
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
    · rintro ⟨z, hz⟩; exact ⟨z, hz.symm⟩
  have hintO : ∀ o : O, ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem (ι o) :=
    fun o => (hmem (ι o)).1 ⟨o, rfl⟩
  have hf'M : ∀ i (s : O), Tr (f' i * ι s) ∈ Zs := by
    intro i s
    obtain ⟨z, hz⟩ := hcoord (ι s) (hintO s) i
    rw [hcoef, hZ]; exact ⟨z, hz⟩
  obtain ⟨⟨c, hc⟩, hcint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin n)) f'
  let D := ι c
  have hD : D ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero ⟨c, hc⟩ (hιinj (h0.trans (map_zero ι).symm))
  have ho : ∀ i, ∃ o : O, ι o = D * f' i := by
    intro i
    obtain ⟨o, ho⟩ := hcint i (Finset.mem_univ i)
    exact ⟨o, by rw [ho, Algebra.smul_def]⟩
  choose o hoD using ho
  let I : Ideal O :=
    { carrier := {a | ∀ s : O, Tr (D⁻¹ * ι a * ι s) ∈ Zs}
      add_mem' := by
        intro a a' ha ha' s
        have e : D⁻¹ * ι (a + a') * ι s = D⁻¹ * ι a * ι s + D⁻¹ * ι a' * ι s := by
          rw [map_add (f := _)]; ring
        rw [e, map_add (f := _)]; exact Zs.add_mem (ha s) (ha' s)
      zero_mem' := by
        intro s; simp only [map_zero, mul_zero, zero_mul]; exact Zs.zero_mem
      smul_mem' := by
        intro r a ha s
        have e : D⁻¹ * ι (r • a) * ι s = D⁻¹ * ι a * ι (r * s) := by
          rw [smul_eq_mul, map_mul, map_mul]; ring
        rw [e]; exact ha (r * s) }
  have hoI : ∀ i, o i ∈ I := by
    intro i s
    show Tr (D⁻¹ * ι (o i) * ι s) ∈ Zs
    rw [hoD i, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
    exact hf'M i s
  let g := Submodule.IsPrincipal.generator I
  have hgI : g ∈ I := Submodule.IsPrincipal.generator_mem I
  have ha : ∀ i, ∃ a : O, a * g = o i := by
    intro i
    have h := hoI i
    rw [← Submodule.IsPrincipal.span_singleton_generator I] at h
    exact Ideal.mem_span_singleton'.1 h
  choose a hag using ha
  let δ := D⁻¹ * ι g
  let lam : LL →ₗ[ℚ_[l]] ℚ_[l] := Tr.comp (LinearMap.mulLeft ℚ_[l] δ)
  have hlam : ∀ y, lam y = Tr (δ * y) := fun y => rfl
  have hδa : ∀ i, δ * ι (a i) = f' i := by
    intro i
    show D⁻¹ * ι g * ι (a i) = f' i
    rw [mul_assoc, ← map_mul, mul_comm g, hag, hoD, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  have he : ∀ i, ∃ e : O, ι e = b i := fun i => (hmem (b i)).2 (hbint i)
  choose e he using he
  refine ⟨lam, n, e, a, fun z => ?_, fun y => ?_, fun x => ?_⟩
  · have hz : ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])).IsIntegralElem
        (algebraMap ℚ_[l] LL (z : ℚ_[l])) := RingHom.isIntegralElem_map _
    exact (hmem _).2 hz
  · have h := hgI y
    rw [hZ] at h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [hlam]; exact hz⟩
  · conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlam, ← mul_assoc, hδa, hcoef, he]
end GlobalTheory.IntDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDR
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per Matrix

noncomputable section

namespace GlobalTheory.DRMat

theorem exists_fixed_of_stable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (S : Set (F →+* F)) (N : Submodule F (ι → F))
    (hN : ∀ σ ∈ S, ∀ v ∈ N, (fun j => σ (v j)) ∈ N) (v₀ : ι → F) (hv₀ : v₀ ∈ N) (h0 : v₀ ≠ 0) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ σ ∈ S, ∀ j, σ (v j) = v j := by
  classical
  have hex : ∃ k, ∃ v ∈ N, v ≠ 0 ∧ (Finset.univ.filter fun j => v j ≠ 0).card = k :=
    ⟨_, v₀, hv₀, h0, rfl⟩
  obtain ⟨w, hwN, hw0, hwk⟩ := Nat.find_spec hex
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  set v := (w j₀)⁻¹ • w with hv
  have hvN : v ∈ N := N.smul_mem _ hwN
  have hvj : v j₀ = 1 := by simp [hv, hj₀]
  have hsupp : ∀ j, v j ≠ 0 ↔ w j ≠ 0 := by
    intro j; simp [hv, hj₀]
  refine ⟨v, hvN, fun h => by simp [h] at hvj, fun σ hσ => ?_⟩
  by_contra hne
  push_neg at hne
  set u : ι → F := (fun j => σ (v j)) - v with hu
  have huN : u ∈ N := N.sub_mem (hN σ hσ v hvN) hvN
  have hu0 : u ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    intro h; apply hj; have := congrFun h j; simpa [hu, sub_eq_zero] using this
  have hlt : (Finset.univ.filter fun j => u j ≠ 0).card < Nat.find hex := by
    rw [← hwk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j₀, by simp [hj₀], by simp [hu, hvj]⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hsupp]; intro hvj0; apply hj; simp [hu, hvj0]
  exact Nat.find_min hex hlt ⟨u, huN, hu0, rfl⟩

theorem exists_period_matrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ hDR
  set M : ↥(GK K) → Matrix n n P.R.BdR := fun g =>
    (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (x : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * x) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) x := by
    intro g k x
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let D : Submodule ↥K.1 (n → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro x y hx hy g
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have : (fun i => P.actQdR (g : GQ l) ((x + y) i)) =
            (fun i => P.actQdR (g : GQ l) (x i)) + (fun i => P.actQdR (g : GQ l) (y i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hx g, hy g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k x hx g
        simp only [Set.mem_setOf_eq] at hx ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • x) i)) = k • (fun i => P.actQdR (g : GQ l) (x i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hx g] }
  have hmemD : ∀ c, c ∈ D ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl

  let e : V ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (n → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (n → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR n
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => b.repr v i • β := by
    intro v β
    simp [e]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) ρ g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) ρ g (v ⊗ₜ β) = ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, he_tmul, he_tmul]
      funext i
      rw [← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by rw [map_mul]; ring
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  have hmap : (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) = D.restrictScalars ℚ_[l] := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, hmemD]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← e.injective.eq_iff, he, LinearEquiv.apply_symm_apply]
  have hfr : Module.finrank ℚ_[l] ↥D = Module.finrank ℚ_[l] K.1 * Fintype.card n := by
    have h1 := hDR
    unfold Formalism.MainNotions.N.IsDR at h1
    rw [Module.finrank_eq_card_basis b, LinearEquiv.finrank_eq (e.submoduleMap (DdR (P.PD K) ρ)), hmap] at h1
    exact h1

  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    refine ⟨1, fun g => ?_⟩
    ext i; exact isEmptyElim i
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hKpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  haveI : Module.Finite ℚ_[l] ↥D := Module.finite_of_finrank_pos (by rw [hfr]; positivity)
  haveI : Module.Finite ↥K.1 ↥D := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥K.1 ↥D
  have hrank : Module.finrank ↥K.1 ↥D = Fintype.card n := by
    have := Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥D
    rw [hfr] at this
    exact Nat.eq_of_mul_eq_mul_left hKpos this
  let bK : Module.Basis n ↥K.1 ↥D :=
    (Module.finBasisOfFinrankEq ↥K.1 ↥D hrank).reindex (Fintype.equivFin n).symm
  let Q0 : Matrix n n P.R.BdR := Matrix.of fun i j => (bK j : n → P.R.BdR) i
  have hQ : ∀ g : ↥(GK K), M g * Q0.map (P.actQdR (g : GQ l)) = Q0 := by
    intro g
    ext i j
    have h := congrFun ((hmemD _).1 (bK j).2 g) i
    simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hdet : IsUnit Q0.det := by
    letI : Field P.R.BdR := (_root_.GlobalTheory.PMon.bdR_tied l P AI T).1.toField
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    obtain ⟨v, hv0, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    let S : Set (P.R.BdR →+* P.R.BdR) :=
      Set.range fun g : ↥(GK K) => ((P.actQdR (g : GQ l)) : P.R.BdR →+* P.R.BdR)
    have hstab : ∀ σ ∈ S, ∀ u ∈ LinearMap.ker (Matrix.mulVecLin Q0), (fun j => σ (u j)) ∈ LinearMap.ker (Matrix.mulVecLin Q0) := by
      rintro σ ⟨g, rfl⟩ u hu
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu ⊢
      rw [← hQ g, ← Matrix.mulVec_mulVec]
      have : (Q0.map (P.actQdR (g : GQ l)) *ᵥ fun j => (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR) (u j)) = 0 := by
        funext i
        have := congrArg (P.actQdR (g : GQ l)) (congrFun hu i)
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using this
      rw [this, Matrix.mulVec_zero]
    obtain ⟨w, hwN, hw0, hwfix⟩ :=
      exists_fixed_of_stable S (LinearMap.ker (Matrix.mulVecLin Q0)) hstab v (by simpa using hQv) hv0
    have hwK : ∀ j, ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hwfix _ ⟨g, rfl⟩ j
    choose c hc using hwK
    have hQw : Q0 *ᵥ w = 0 := by simpa using hwN
    set_option synthInstance.maxHeartbeats 100000 in
    have hsum : ∑ j, c j • bK j = 0 := by
      apply Subtype.ext
      funext i
      have := congrFun hQw i
      simp only [Matrix.mulVec, dotProduct, Q0, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Submodule.coe_zero, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => by rw [← hc j]; exact mul_comm _ _
    have hc0 := Fintype.linearIndependent_iff.mp bK.linearIndependent c hsum
    exact hw0 (funext fun j => by rw [← hc j, hc0 j, map_zero]; rfl)
  refine ⟨((Matrix.isUnit_iff_isUnit_det Q0).mpr hdet).unit, fun g => ?_⟩
  rw [IsUnit.unit_spec]
  exact hQ g

end GlobalTheory.DRMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem exists_extend_residue {O A F : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Algebra.IsIntegral O A] (hinj : Function.Injective (algebraMap O A)) [Field F] [IsAlgClosed F]
    (κ : IsLocalRing.ResidueField O →+* F) :
    ∃ g : A →+* F, g.comp (algebraMap O A) = κ.comp (IsLocalRing.residue O) := by
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (IsLocalRing.maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  letI : Field (A ⧸ Q) := Ideal.Quotient.field Q
  let j : IsLocalRing.ResidueField O →+* A ⧸ Q := Ideal.quotientMap Q (algebraMap O A) hQm.ge
  have hj : j.comp (IsLocalRing.residue O) = (Ideal.Quotient.mk Q).comp (algebraMap O A) := by
    ext x; rfl
  letI : Algebra (IsLocalRing.ResidueField O) (A ⧸ Q) := j.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) F := κ.toAlgebra
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) (A ⧸ Q) := ⟨fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
    refine ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (j.comp (IsLocalRing.residue O)) _ _ = 0
    rw [hj, ← hom_eval₂, hpa, map_zero]⟩
  let L : (A ⧸ Q) →ₐ[IsLocalRing.ResidueField O] F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  rw [RingHom.comp_assoc, ← hj, ← RingHom.comp_assoc]
  congr 1
  ext x
  exact L.commutes x

theorem exists_redVia : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k →
    ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
      InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  intro D i k _
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hφ : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  letI : Algebra (D.nd.O i) ℂ := (iotaO D.nd D.naut i).toAlgebra
  let A := integralClosure (D.nd.O i) ℂ
  have hA : Function.Injective (algebraMap (D.nd.O i) A) := fun x y h => hφ (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_extend_residue hA (D.naut.kFbar i)
  have hmem : ∀ x, D.ntypes.teichC k x ∈ A := by
    intro x
    by_cases hx : x = 0
    · rw [hx, GlobalTheory.TameLabels.teich_zero _ (D.ntypes.teichC_inj k)]; exact A.zero_mem
    · obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1
        ((D.ntypes.teichC k).isOfFinOrder (GlobalTheory.TameLabels.isOfFinOrder_of_ne_zero hx))
      exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  let t : Fb (D.host.g k) (D.host.g_prime k) →* A := (D.ntypes.teichC k).codRestrict A.toSubmonoid hmem
  have ht : ∀ x, (t x : ℂ) = D.ntypes.teichC k x := fun _ => rfl
  refine ⟨g.toMonoidHom.comp t, fun x y hx hy hcx hcy h => ?_, fun p s hp => ?_⟩
  · refine D.ntypes.teichC_inj k x y hx hy ?_
    rw [← ht, ← ht]
    congr 1
    refine GlobalTheory.TameRed.eq_of_map_eq g (M := orderOf x * orderOf y) ?_ ?_ ?_ h
    · rw [Ne, CharP.cast_eq_zero_iff _ (D.nd.l i)]
      exact (Nat.Prime.coprime_iff_not_dvd (D.nd.lPrime i).out).1 (Nat.Coprime.mul_left hcx hcy).symm
    · rw [← map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
    · rw [← map_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
  · have h1 : p.map (algebraMap (D.nd.O i) A) = (s.map fun x => X - C (t x)).prod := by
      apply Polynomial.map_injective A.val.toRingHom Subtype.val_injective
      rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
      refine hp.trans (congrArg _ (Multiset.map_congr rfl fun x _ => ?_))
      simp [ht]
    rw [← hg, ← Polynomial.map_map, h1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
    simp

end GlobalTheory.TypeLeaf
end
end

