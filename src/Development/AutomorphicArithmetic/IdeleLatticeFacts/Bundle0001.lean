module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0007
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.EqZeroOfSplitIdempotentEvalPlaceEqZero
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

theorem UpperTheory.eq_zero_of_splitIdempotent_eval_place_eq_zero :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
        IsCMExt F E σ → ∀ e, IsSplitIdemF σ e → ∀ P : HeightOneSpectrum (𝓞 E), (∀ Q, Q ≠ P → ev F E Q e = 0) →
        ∀ a : AEF F E, e * a = a → ev F E P a = 0 → a = 0 := by
  intro F E _ _ _ _ _ σ hσ e he P hP a hea haP
  obtain ⟨hee, hec, v, ε, hε, hsum⟩ := he
  obtain ⟨α, rfl, -, -⟩ := hε
  have h1 : e * algebraMap (AF F) (AEF F E) (pairA F 0 α) = e := by
    rw [← hsum, mul_add, hee, hec, add_zero]
  have h2 : a = algebraMap (AF F) (AEF F E) (pairA F 0 α) * a := by
    calc a = e * a := hea.symm
      _ = (e * algebraMap (AF F) (AEF F E) (pairA F 0 α)) * a := by rw [h1]
      _ = _ := by rw [mul_comm e, mul_assoc, hea]
  have h3 : ∀ Q, ev F E Q a = 0 := by
    intro Q
    by_cases hQ : Q = P
    · subst hQ
      exact haP
    · rw [← hea, map_mul, hP Q hQ, zero_mul]
  have h4 : finPartF F E a = 0 := by
    apply (finAdEquiv F E).injective
    rw [map_zero]
    apply RestrictedProduct.ext
    intro Q
    exact h3 Q
  let g : Af F →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F) : Af F →ₗ[F] AF F) ∘ₗ LinearMap.mulLeft F α
  have h5 : ∀ b : AEF F E, algebraMap (AF F) (AEF F E) (pairA F 0 α) * b =
      TensorProduct.map g LinearMap.id (finPartF F E b) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      show _ = TensorProduct.map g LinearMap.id ((sndA F x) ⊗ₜ[F] y)
      rw [TensorProduct.map_tmul]
      congr 1
      exact Prod.ext (zero_mul x.1) rfl
    | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), map_add (f := _)]
  rw [h2, h5, h4, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsLatticeIndexOfInjectiveEndomorphism
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

namespace UpperTheory.LocIdx

open GroundTheory.Heights₂.Heights.LatticeLemmas

section
variable {E V : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} [AddCommGroup V]
  [Module (P.adicCompletion E) V] [Module (P.adicCompletionIntegers E) V]
  [IsScalarTower (P.adicCompletionIntegers E) (P.adicCompletion E) V]

private theorem one_lt_norm (P : HeightOneSpectrum (𝓞 E)) : 1 < Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

private theorem norm_eq_zpow {x : P.adicCompletion E} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ (Valued.v x).log := by
  rw [← GroundTheory.Global.normalizedAbv_apply]
  exact GroundTheory.Global.normalizedAbv_eq_zpow P hx

private theorem exists_basis (A : Submodule (P.adicCompletionIntegers E) V) (hfg : A.FG)
    (hsp : Submodule.span (P.adicCompletion E) (A : Set V) = ⊤) :
    ∃ (m : ℕ) (c : Module.Basis (Fin m) (P.adicCompletion E) V),
      Submodule.span (P.adicCompletionIntegers E) (Set.range c) = A := by
  haveI : Module.Finite (P.adicCompletionIntegers E) A := Module.Finite.iff_fg.mpr hfg
  haveI : Module.IsTorsionFree (P.adicCompletionIntegers E) A := LocalLatticeIndex.isTorsionFree A
  haveI : Module.Free (P.adicCompletionIntegers E) A := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis (P.adicCompletionIntegers E) A
  have hli : LinearIndependent (P.adicCompletionIntegers E) (A.subtype ∘ b) :=
    b.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hliK : LinearIndependent (P.adicCompletion E) (A.subtype ∘ b) :=
    hli.localization (P.adicCompletion E) (nonZeroDivisors (P.adicCompletionIntegers E))
  have hspO : Submodule.span (P.adicCompletionIntegers E) (Set.range (A.subtype ∘ b)) = A := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span (P.adicCompletion E) (Set.range (A.subtype ∘ b)) := by
    rw [← hsp]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hspO] at hx
    exact Submodule.span_le_restrictScalars (P.adicCompletionIntegers E) (P.adicCompletion E) _ hx
  refine ⟨_, Module.Basis.mk hliK hspK, ?_⟩
  rw [Module.Basis.coe_mk]
  exact hspO

private theorem relIndex_eq_inv_norm_det_basis_change {m : ℕ} (a c : Module.Basis (Fin m) (P.adicCompletion E) V)
    (A B : Submodule (P.adicCompletionIntegers E) V)
    (ha : Submodule.span (P.adicCompletionIntegers E) (Set.range a) = A)
    (hc : Submodule.span (P.adicCompletionIntegers E) (Set.range c) = B) (hBA : B ≤ A) :
    (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ‖LinearMap.det ((a.equiv c (Equiv.refl _)).toLinearMap)‖⁻¹ := by
  have hAfg : A.FG := ha ▸ Submodule.fg_span (Set.finite_range a)
  have hAsp : Submodule.span (P.adicCompletion E) (A : Set V) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← a.span_eq]
    apply Submodule.span_mono
    rw [← ha]
    exact Submodule.subset_span
  have himg : (B : Set V) = (a.equiv c (Equiv.refl _)) '' (A : Set V) := by
    have key : (Submodule.span (P.adicCompletionIntegers E) (Set.range a)).map
        ((a.equiv c (Equiv.refl _)).toLinearMap.restrictScalars (P.adicCompletionIntegers E)) = B := by
      rw [← Submodule.span_image, ← Set.range_comp, ← hc]
      congr 2
      funext i
      exact Module.Basis.equiv_apply _ _ _ _
    rw [← key, ha, Submodule.map_coe]
    rfl
  exact LocalLatticeIndex.index_eq_det A B _ hAfg hAsp himg hBA

private theorem exists_nat_pow_eq_of_real_eq_zpow_absNorm (r : ℕ) (k : ℤ) (h : (r : ℝ) = (Ideal.absNorm P.asIdeal : ℝ) ^ k) :
    ∃ n : ℕ, r = Ideal.absNorm P.asIdeal ^ n := by
  have hN : (1 : ℝ) < Ideal.absNorm P.asIdeal := by exact_mod_cast one_lt_norm P
  have hpos : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℝ) ^ k := zpow_pos (by linarith) k
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, Nat.cast_zero] at h
      linarith
    · exact h0
  have hk : 0 ≤ k := by
    have h1 : (1 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ k := by
      rw [← h]
      exact_mod_cast hr
    exact (one_le_zpow_iff_right₀ hN).mp h1
  refine ⟨k.toNat, ?_⟩
  have h2 : (r : ℝ) = ((Ideal.absNorm P.asIdeal ^ k.toNat : ℕ) : ℝ) := by
    rw [h, Nat.cast_pow, ← zpow_natCast, Int.toNat_of_nonneg hk]
  exact_mod_cast h2

private theorem relIndex_pow (A B : Submodule (P.adicCompletionIntegers E) V) (hA : A.FG)
    (hsA : Submodule.span (P.adicCompletion E) (A : Set V) = ⊤) (hB : B.FG)
    (hsB : Submodule.span (P.adicCompletion E) (B : Set V) = ⊤) (hBA : B ≤ A) :
    ∃ n : ℕ, B.toAddSubgroup.relIndex A.toAddSubgroup = Ideal.absNorm P.asIdeal ^ n := by
  obtain ⟨m, a, ha⟩ := exists_basis A hA hsA
  obtain ⟨m', c, hc⟩ := exists_basis B hB hsB
  have hm : m' = m := by
    have h1 := Module.finrank_eq_card_basis a
    have h2 := Module.finrank_eq_card_basis c
    simp only [Fintype.card_fin] at h1 h2
    omega
  subst hm
  have h := relIndex_eq_inv_norm_det_basis_change a c A B ha hc hBA
  have hdet : LinearMap.det ((a.equiv c (Equiv.refl _)).toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  rw [norm_eq_zpow hdet, ← _root_.zpow_neg] at h
  exact exists_nat_pow_eq_of_real_eq_zpow_absNorm _ _ h

private theorem main (L : Submodule (P.adicCompletionIntegers E) V)
    (T : V →ₗ[P.adicCompletion E] V) (hfg : L.FG)
    (hsp : Submodule.span (P.adicCompletion E) (L : Set V) = ⊤) (hinj : Function.Injective T) :
    ∃ i j : ℕ, idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) =
        Ideal.absNorm P.asIdeal ^ i ∧
      idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L =
        Ideal.absNorm P.asIdeal ^ j ∧
      Valued.v (LinearMap.det T) = WithZero.exp ((i : ℤ) - j) := by
  obtain ⟨m, a, ha⟩ := exists_basis L hfg hsp
  haveI : FiniteDimensional (P.adicCompletion E) V := Module.Finite.of_basis a
  let Te : V ≃ₗ[(P.adicCompletion E)] V := LinearEquiv.ofInjectiveEndo T hinj
  have hTe : (Te : V →ₗ[(P.adicCompletion E)] V) = T := LinearMap.ext fun x => rfl
  let t := a.map Te
  set TL := L.map (T.restrictScalars (P.adicCompletionIntegers E)) with hTLdef
  have ht : Submodule.span (P.adicCompletionIntegers E) (Set.range t) = TL := by
    rw [hTLdef, ← ha, Submodule.map_span, ← Set.range_comp]
    congr 2
  have hTLfg : TL.FG := hfg.map _
  have hTLsp : Submodule.span (P.adicCompletion E) (TL : Set V) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← t.span_eq]
    apply Submodule.span_mono
    rw [← ht]
    exact Submodule.subset_span
  set M := L ⊓ TL with hMdef
  have hMle1 : M ≤ L := inf_le_left
  have hMle2 : M ≤ TL := inf_le_right
  have hMfg : M.FG := by
    haveI : IsNoetherian (P.adicCompletionIntegers E) L := isNoetherian_of_fg_of_noetherian L hfg
    have hM : M = (TL.comap L.subtype).map L.subtype := by
      rw [Submodule.map_comap_subtype]
    rw [hM]
    exact (IsNoetherian.noetherian _).map _
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (P.adicCompletionIntegers E))
    (Finset.univ : Finset (Fin m × Fin m)) (fun ij => t.repr (a ij.1) ij.2)
  have hai : ∀ i, a i ∈ L := by
    intro i
    rw [← ha]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbai : ∀ i, (b : (P.adicCompletionIntegers E)) • a i ∈ TL := by
    intro i
    rw [← ht]
    rw [← t.sum_repr (a i), Finset.smul_sum]
    apply Submodule.sum_mem
    intro j _
    obtain ⟨y, hy⟩ := hb (i, j) (Finset.mem_univ _)
    rw [← smul_assoc]
    simp only at hy
    rw [← hy, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hbM : ∀ i, (b : (P.adicCompletionIntegers E)) • a i ∈ M := fun i => ⟨L.smul_mem _ (hai i), hbai i⟩
  have hbne : algebraMap (P.adicCompletionIntegers E) (P.adicCompletion E) (b : (P.adicCompletionIntegers E)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hMsp : Submodule.span (P.adicCompletion E) (M : Set V) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← a.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : a i = (algebraMap (P.adicCompletionIntegers E) (P.adicCompletion E) (b : (P.adicCompletionIntegers E)))⁻¹ • ((b : (P.adicCompletionIntegers E)) • a i) := by
      rw [← algebraMap_smul (P.adicCompletion E) (b : (P.adicCompletionIntegers E)) (a i), smul_smul, inv_mul_cancel₀ hbne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hbM i))
  obtain ⟨m', c, hc⟩ := exists_basis M hMfg hMsp
  have hm : m' = m := by
    have h1 := Module.finrank_eq_card_basis a
    have h2 := Module.finrank_eq_card_basis c
    simp only [Fintype.card_fin] at h1 h2
    omega
  subst hm
  have h1 := relIndex_eq_inv_norm_det_basis_change a c L M ha hc hMle1
  have h2 := relIndex_eq_inv_norm_det_basis_change t c TL M ht hc hMle2
  have e1 : idx L TL = M.toAddSubgroup.relIndex TL.toAddSubgroup := by
    unfold idx
    rw [hMdef]
    exact (AddSubgroup.inf_relIndex_right L.toAddSubgroup TL.toAddSubgroup).symm
  have e2 : idx TL L = M.toAddSubgroup.relIndex L.toAddSubgroup := by
    unfold idx
    rw [hMdef]
    exact (AddSubgroup.inf_relIndex_left L.toAddSubgroup TL.toAddSubgroup).symm
  obtain ⟨i, hi⟩ := relIndex_pow TL M hTLfg hTLsp hMfg hMsp hMle2
  obtain ⟨j, hj⟩ := relIndex_pow L M hfg hsp hMfg hMsp hMle1
  refine ⟨i, j, by rw [e1]; exact hi, by rw [e2]; exact hj, ?_⟩
  have hcomp : ((t.equiv c (Equiv.refl _)).toLinearMap).comp T =
      (a.equiv c (Equiv.refl _)).toLinearMap := by
    apply a.ext
    intro k
    have hk : T (a k) = t k := by
      show T (a k) = (a.map Te) k
      rw [Module.Basis.map_apply]
      rfl
    show (t.equiv c (Equiv.refl _)) (T (a k)) = (a.equiv c (Equiv.refl _)) (a k)
    rw [hk]
    simp
  have hdT : LinearMap.det T ≠ 0 := by
    rw [← hTe]
    exact (LinearEquiv.isUnit_det' Te).ne_zero
  have hd2 : LinearMap.det ((t.equiv c (Equiv.refl _)).toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have hN : (1 : ℝ) < Ideal.absNorm P.asIdeal := by exact_mod_cast one_lt_norm P
  have hnorm : ‖LinearMap.det T‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ ((i : ℤ) - j) := by
    have n1 : ‖LinearMap.det ((a.equiv c (Equiv.refl _)).toLinearMap)‖ =
        ‖LinearMap.det ((t.equiv c (Equiv.refl _)).toLinearMap)‖ * ‖LinearMap.det T‖ := by
      rw [← hcomp, LinearMap.det_comp, norm_mul]
    rw [hj] at h1
    rw [hi] at h2
    push_cast at h1 h2
    have p2 : ‖LinearMap.det ((t.equiv c (Equiv.refl _)).toLinearMap)‖ ≠ 0 := norm_ne_zero_iff.mpr hd2
    rw [zpow_sub₀ (by positivity), zpow_natCast, zpow_natCast, h1, h2, n1]
    field_simp
  rw [norm_eq_zpow hdT] at hnorm
  have hlog := zpow_right_injective₀ (by linarith : (0 : ℝ) < Ideal.absNorm P.asIdeal) (ne_of_gt hN) hnorm
  rw [← hlog, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hdT)]

end
end UpperTheory.LocIdx

theorem UpperTheory.exists_lattice_index_of_injective_endomorphism :
    ∀ {E V : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) [AddCommGroup V]
        [Module (P.adicCompletion E) V] [Module (P.adicCompletionIntegers E) V]
        [IsScalarTower (P.adicCompletionIntegers E) (P.adicCompletion E) V]
        (L : Submodule (P.adicCompletionIntegers E) V) (T : V →ₗ[P.adicCompletion E] V),
        L.FG → Submodule.span (P.adicCompletion E) (L : Set V) = ⊤ → Function.Injective T →
        ∃ i j : ℕ, idx L (L.map (T.restrictScalars (P.adicCompletionIntegers E))) = Ideal.absNorm P.asIdeal ^ i ∧
          idx (L.map (T.restrictScalars (P.adicCompletionIntegers E))) L = Ideal.absNorm P.asIdeal ^ j ∧
          Valued.v (LinearMap.det T) = WithZero.exp ((i : ℤ) - j) := by
  intro E V _ _ P _ _ _ _ L T hfg hsp hinj
  exact UpperTheory.LocIdx.main L T hfg hsp hinj
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsLinearMapDetMulMulEqPow
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

theorem UpperTheory.exists_linearMap_det_mul_mul_eq_pow :
    ∀ {K : Type} [Field K] {m n : ℕ} (H : Matrix (Fin m) (Fin m) K) (G : Matrix (Fin n) (Fin n) K),
        ∃ T : Matrix (Fin m) (Fin n) K →ₗ[K] Matrix (Fin m) (Fin n) K, (∀ u, T u = H * u * G) ∧
          LinearMap.det T = H.det ^ n * G.det ^ m := by
  intro K _ m n H G
  let T : Matrix (Fin m) (Fin n) K →ₗ[K] Matrix (Fin m) (Fin n) K :=
    { toFun := fun u => H * u * G
      map_add' := by
        intro u v
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c u
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨T, fun u => rfl, ?_⟩
  have hrepr : ∀ (M : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n),
      (Matrix.stdBasis K (Fin m) (Fin n)).repr M (i, j) = M i j := by
    intro M i j
    simp [Matrix.stdBasis]
  have hmat : LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) T
      = H ⊗ₖ Gᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, hrepr]
    simp [T, Matrix.kroneckerMap_apply, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_ite_eq', Finset.sum_ite_eq, ite_mul]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), hmat, Matrix.det_kronecker,
    Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.IdeleLatticeFacts.ExistsSignHeckeCharAtNonfixedPlace
section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem exists_unit {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ u : (FiniteAdeleRing (𝓞 E) E)ˣ, Valued.v ((u : FiniteAdeleRing (𝓞 E) E) P) = WithZero.exp (-1 : ℤ) ∧
      ∀ Q, Q ≠ P → (u : FiniteAdeleRing (𝓞 E) E) Q = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E P
  have hv : Valued.v (algebraMap E (P.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P π).trans hπ
  have h0 : algebraMap E (P.adicCompletion E) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let x : (P.adicCompletion E)ˣ := Units.mk0 _ h0
  refine ⟨Units.map (RingHom.snd _ _).toMonoidHom (Neutral.B1.localIdele E P x), ?_, fun Q hQ => ?_⟩
  · show Valued.v (((Neutral.B1.localIdele E P x : _) : AdeleRing (𝓞 E) E).2 P) = _
    rw [Neutral.B1.localIdele_snd_self]
    exact hv
  · exact (Neutral.B1.localIdele_isSupportedAt E P x).2 Q hQ

private theorem fin_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Af F ⊗[F] E) : finPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

private theorem inf_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (y : Af F ⊗[F] E) : infPartF F E (PositivityTheory.ThKW.LatB.liftF F E y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a t => exact TensorProduct.zero_tmul _ _
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

private theorem exists_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) :
    ∃ z : (AEF F E)ˣ, wv F E P z = WithZero.exp (-1 : ℤ) ∧ ∀ Q, Q ≠ P → wv F E Q z = 1 := by
  obtain ⟨u, hu1, hu2⟩ := exists_unit P
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (u : FiniteAdeleRing (𝓞 E) E)
  obtain ⟨b, hb⟩ := (finAdEquiv F E).surjective ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E)
  have hab : a * b = 1 := (finAdEquiv F E).injective (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  have key : (PositivityTheory.ThKW.LatB.liftF F E a + (1 - finIdem F E)) * (PositivityTheory.ThKW.LatB.liftF F E b + (1 - finIdem F E)) = 1 := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · simp only [map_sub, map_mul, map_add (f := _), map_one, inf_lift, infPartF_finIdem, zero_add, sub_zero, mul_one, sub_self, map_zero]
    · simp only [map_sub, map_mul, map_add (f := _), map_one, fin_lift, PositivityTheory.ThKW.TauSpanIdentities.finPartF_finIdem, sub_self, add_zero, hab, map_zero]
  let z : (AEF F E)ˣ := ⟨_, _, key, by rw [mul_comm]; exact key⟩
  have hev : ∀ Q, ev F E Q (z : AEF F E) = (u : FiniteAdeleRing (𝓞 E) E) Q := by
    intro Q
    have h1 : finPartF F E (z : AEF F E) = a := by
      show finPartF F E (PositivityTheory.ThKW.LatB.liftF F E a + (1 - finIdem F E)) = a
      rw [map_add (f := _), map_sub, map_one, fin_lift, PositivityTheory.ThKW.TauSpanIdentities.finPartF_finIdem, sub_self, add_zero]
    show evalV E Q (finAdEquiv F E (finPartF F E (z : AEF F E))) = _
    rw [h1, ha]
    rfl
  refine ⟨z, ?_, fun Q hQ => ?_⟩
  · rw [wv_apply, hev, hu1]
  · rw [wv_apply, hev, hu2 Q hQ, map_one]

theorem UpperTheory.exists_sign_heckeChar_at_nonfixed_place :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (lam : ℕ →* ℂ)
        (κ : (AEF F E)ˣ →* Circle), IsKap σ lam κ → ∀ P : HeightOneSpectrum (𝓞 E), ¬ Fx σ P →
        ∃ s : Circle, s * s = 1 ∧ lam (Ideal.absNorm P.asIdeal) = (s : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ∧
          ∀ (x : (AEF F E)ˣ) (m : ℤ), (∀ Q, Q ≠ P → wv F E Q x = 1) → wv F E P x = WithZero.exp m → κ x = s ^ m := by
  intro F E _ _ _ _ _ σ lam κ hκ P hP
  obtain ⟨z, hz1, hz2⟩ := exists_idele F E P
  refine ⟨κ z, hκ.sq z, hκ.gen P hP z hz1 hz2, fun x m hx1 hx2 => ?_⟩
  have hpow : ∀ Q, wv F E Q (z ^ m) = wv F E Q z ^ m := fun Q =>
    map_zpow' (wv F E Q) (fun y => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])) z m
  have h1 : κ (x * z ^ m) = 1 := by
    refine hκ.ker _ fun Q _ => ?_
    by_cases hQ : Q = P
    · subst hQ
      rw [map_mul, hpow, hx2, hz1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [map_mul, hpow, hx1 Q hQ, hz2 Q hQ, _root_.one_zpow, one_mul]
  rw [map_mul, map_zpow] at h1
  have h2 : κ z ^ m * κ z ^ m = 1 := by
    rw [← mul_zpow, hκ.sq z, _root_.one_zpow]
  exact mul_right_cancel (h1.trans h2.symm)
end

