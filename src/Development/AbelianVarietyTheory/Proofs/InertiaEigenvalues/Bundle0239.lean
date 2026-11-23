module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescent
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamDescent

theorem finrank_fixed {R G M K L : Type} [Field R] [Group G] [AddCommGroup M] [Module R M]
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (A : G →* Module.End R M) (m : L →+* Module.End R M) (ε : G →* (L ≃ₐ[K] L))
    (hs : Function.Surjective ε) (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (D D' : Submodule R M) (hD : ∀ x, x ∈ D ↔ ∀ g, A g x = x)
    (hD' : ∀ x, x ∈ D' ↔ ∀ g, ε g = 1 → A g x = x) :
    Module.finrank R D' = Module.finrank K L * Module.finrank R D := by
  classical
  have hc : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hc).symm
  let μ : Module.Basis (L ≃ₐ[K] L) K L := b.traceDual
  let Pm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ i => σ (b i)
  let Qm : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun j σ => σ (μ j)
  have hQP : Qm * Pm = 1 := by
    ext j i
    simp only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, ← map_mul]
    rw [← trace_eq_sum_automorphisms, Module.Basis.trace_traceDual_mul, Matrix.one_apply]
    by_cases h : j = i
    · simp [h]
    · simp [h, Ne.symm h]
  have hPQ : Pm * Qm = 1 := mul_eq_one_comm.1 hQP
  have h1 : ∀ j i, ∑ σ : L ≃ₐ[K] L, σ (μ j) * σ (b i) = if j = i then 1 else 0 := fun j i => by
    have := congrFun (congrFun hQP j) i
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply] using this
  have h2 : ∀ σ : L ≃ₐ[K] L, ∑ i, b i * σ (μ i) = if 1 = σ then 1 else 0 := fun σ => by
    have := congrFun (congrFun hPQ 1) σ
    simpa only [Matrix.mul_apply, Pm, Qm, Matrix.of_apply, Matrix.one_apply,
      AlgEquiv.one_apply] using this
  choose s hs' using hs
  have hm : ∀ a, ∀ x ∈ D', m a x ∈ D' := fun a x hx => by
    rw [hD'] at hx ⊢
    intro g hg
    rw [hε, hg, hx g hg, AlgEquiv.one_apply]
  have hDD : D ≤ D' := fun x hx => (hD' x).2 fun g _ => (hD x).1 hx g
  have hA : ∀ x ∈ D', ∀ g g', ε g = ε g' → A g x = A g' x := fun x hx g g' h => by
    have := (hD' x).1 hx (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel])
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  let Φ₀ : ((L ≃ₐ[K] L) → D) →ₗ[R] M :=
    ∑ i, (m (b i)) ∘ₗ D.subtype ∘ₗ LinearMap.proj i
  have hΦ : ∀ x, Φ₀ x = ∑ i, m (b i) (x i) := fun x => by
    simp [Φ₀]
  have hinj : Function.Injective Φ₀ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h3 : ∀ σ : L ≃ₐ[K] L, ∑ i, m (σ (b i)) (x i) = 0 := fun σ => by
      have := congrArg (A (s σ)) hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΦ, map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hε, hs', (hD _).1 (x i).2]
    funext j
    apply Subtype.ext
    have h4 : ∑ σ : L ≃ₐ[K] L, m (σ (μ j)) (∑ i, m (σ (b i)) (x i)) = 0 := by
      simp only [h3, map_zero, Finset.sum_const_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ← Module.End.mul_apply, ← map_mul m] at h4
    rw [Finset.sum_comm] at h4
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← LinearMap.sum_apply, ← map_sum m, h1] at h4
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Ne.symm hi]) (by simp)] at h4
    simpa using h4
  have hr : LinearMap.range Φ₀ = D' := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hΦ]
      exact D'.sum_mem fun i _ => hm _ _ (hDD (x i).2)
    · intro x hx
      refine ⟨fun i => ⟨∑ σ, A (s σ) (m (μ i) x), (hD _).2 fun g => ?_⟩, ?_⟩
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (ε g))
          (fun σ => A (s σ) (m (μ i) x))]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Module.End.mul_apply, ← map_mul]
        exact hA _ (hm _ _ hx) _ _ (by simp [hs'])
      · rw [hΦ]
        have hmm : ∀ a a' y, m a (m a' y) = m (a * a') y := fun a a' y => by
          rw [map_mul, Module.End.mul_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hε, hs', map_sum, hmm]
        rw [Finset.sum_comm]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← LinearMap.sum_apply, ← map_sum m, h2]
        rw [Finset.sum_eq_single 1 (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
        simpa using (hD' x).1 hx _ (hs' 1)
  rw [← hr, LinearMap.finrank_range_of_inj hinj]
  by_cases hf : Module.Finite R D
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]
  · rw [Module.finrank_of_not_finite hf, mul_zero, Module.finrank_of_not_finite]
    intro h
    exact hf (Module.Finite.of_surjective
      (LinearMap.proj (R := R) (φ := fun _ : L ≃ₐ[K] L => D) (1 : L ≃ₐ[K] L))
      (fun y => ⟨fun _ => y, rfl⟩))


open GlobalTheory.JumpDescent TensorProduct in
theorem isDR_of_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l)
    (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) →
    ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  intro l _ P K K' LL hle h hst V _ _ _ _ ρ hρ
  unfold IsDR at hρ ⊢
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  let L : IntermediateField ↥K.1 (Om l) := IntermediateField.extendScalars h
  haveI : FiniteDimensional ℚ_[l] ↥L := K'.2
  haveI : FiniteDimensional ↥K.1 ↥L := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  haveI : Normal ↥K.1 (Om l) := Normal.tower_top_of_normal ℚ_[l] _ _
  let e : ↥(GK K) ≃* (Om l ≃ₐ[↥K.1] Om l) := IntermediateField.fixingSubgroupEquiv K.1
  have he : ∀ (g : ↥(GK K)) (x : Om l), e g x = (g : GQ l) x := fun _ _ => rfl
  haveI : Normal ↥K.1 ↥L := IntermediateField.normal_iff_forall_map_le'.2 fun σ => by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective σ
    exact hst g.1 g.2 x hx
  haveI : IsGalois ↥K.1 ↥L := {}
  let ε : ↥(GK K) →* (↥L ≃ₐ[↥K.1] ↥L) := (AlgEquiv.restrictNormalHom ↥L).comp e.toMonoidHom
  have hεa : ∀ (g : ↥(GK K)) (x : ↥L), ((ε g x : ↥L) : Om l) = (g : GQ l) x := fun g x =>
    AlgEquiv.restrictNormalHom_apply L (e g) x
  let A : ↥(GK K) →* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := actVdR (P.PD K) ρ
      map_one' := by ext v b; simp [actVdR_tmul]
      map_mul' := fun g g' => by ext v b; simp [actVdR_tmul] }
  let m : ↥L →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun c => mulOm P (c : Om l)
      map_one' := by ext v b; simp [mulOm_tmul]
      map_mul' := fun g g' => by ext v b; simp [mulOm_tmul, mul_assoc]
      map_zero' := by ext v b; simp [mulOm_tmul]
      map_add' := fun g g' => by ext v b; simp [mulOm_tmul, add_mul, tmul_add] }
  have key := finrank_fixed A m ε
    ((AlgEquiv.restrictNormalHom_surjective (F := ↥K.1) (K₁ := ↥L) (Om l)).comp e.surjective)
    (fun g c x => by
      change actVdR (P.PD K) ρ g (mulOm (LL := ↥LL.1) P (c : Om l) x) =
        mulOm (LL := ↥LL.1) P ((ε g c : ↥L) : Om l) (actVdR (P.PD K) ρ g x)
      rw [hεa]
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.actQdR_Om]
      | add y z hy hz => simp only [map_add (f := _), hy, hz])
    (DdR (P.PD K) ρ) (DdR (P.PD K') (ρ.comp (Subgroup.inclusion hle)))
    (fun x => mem_DdR P K ρ x)
    (fun x => by
      rw [mem_DdR]
      constructor
      · intro hx g hg
        have hg' : g.1 ∈ GK K' := fun a => by
          have := hεa g ⟨a.1, a.2⟩
          rw [hg] at this
          exact this.symm
        have := hx ⟨g.1, hg'⟩
        rw [actVdR_comp P h] at this
        exact this
      · intro hx g
        rw [actVdR_comp P h]
        apply hx
        ext a
        rw [hεa]
        exact g.2 ⟨a.1, a.2⟩)
  have hfin : Module.finrank ℚ_[l] ↥K'.1 = Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥K.1 ↥L :=
    (Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥L).symm
  have hpos : 0 < Module.finrank ↥K.1 ↥L := Module.finrank_pos
  rw [key, hfin] at hρ
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hρ]
  ring

end GlobalTheory.DeRhamDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthKerMatActKmodEqAddValDet
section
namespace GlobalTheory

open Formalism.MainNotions.BlochKatoReduction Formalism.BasicNotions

theorem matAct_comp_linear {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (f : M →ₗ[R] N)
    (v : Fin n → M) : matAct (M := N) A (fun i => f (v i)) = fun i => f (matAct (M := M) A v i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [matAct, map_sum, map_smul]

theorem matAct_self_apply {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) : matAct (M := R) A v = A.mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

private theorem matAct_fractionRing {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (v : Fin n → FractionRing O) :
    matAct (M := FractionRing O) A v = (A.map (algebraMap O (FractionRing O))).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem matAct_fraction_bijective {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Function.Bijective (matAct (M := FractionRing O) A) := by
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = algebraMap O (FractionRing O) A.det := by
    rw [hB, RingHom.map_det]; rfl
  have hU : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr h
  have hf : ⇑(matAct (M := FractionRing O) A) = B.mulVec := funext (matAct_fractionRing A)
  rw [hf]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

theorem nonempty_coker_equiv_ker_matAct {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Nonempty (((Fin n → O) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[O]
      LinearMap.ker (matAct (M := KmodO O) A)) := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let e : (Fin n → FractionRing O) ≃ₗ[O] (Fin n → FractionRing O) :=
    LinearEquiv.ofBijective (matAct (M := FractionRing O) A) (matAct_fraction_bijective A h)
  have he : ∀ x, e x = matAct (M := FractionRing O) A x := fun x => rfl
  have hAι : ∀ y, matAct (M := FractionRing O) A (ι y) = ι (A.mulVec y) := by
    intro y
    have key := matAct_comp_linear A (Algebra.linearMap O (FractionRing O)) y
    rw [matAct_self_apply] at key
    exact key
  have hAπ : ∀ x, matAct (M := KmodO O) A (π x) = π (matAct (M := FractionRing O) A x) :=
    fun x => matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ x
  have hπι : ∀ y, π (ι y) = 0 := by
    intro y
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y i, rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    funext i
    exact IsFractionRing.injective O (FractionRing O) (congrFun hab i)
  have hlift : ∀ x, π x = 0 → ∃ y, ι y = x := by
    intro x hx
    have hmem : ∀ i, ∃ a : O, algebraMap O (FractionRing O) a = x i := by
      intro i
      obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx i)
      exact ⟨a, ha⟩
    choose y hy using hmem
    exact ⟨y, funext hy⟩
  let φ0 : (Fin n → O) →ₗ[O] (Fin n → KmodO O) := π ∘ₗ e.symm.toLinearMap ∘ₗ ι
  have hφ0 : ∀ y, φ0 y ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro y
    rw [LinearMap.mem_ker]
    show matAct (M := KmodO O) A (π (e.symm (ι y))) = 0
    rw [hAπ, ← he, e.apply_symm_apply, hπι]
  let φ := φ0.codRestrict _ hφ0
  have hφ : ∀ y, (φ y : Fin n → KmodO O) = π (e.symm (ι y)) := fun y => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hpre : ∀ i, ∃ k : FractionRing O, Submodule.Quotient.mk k = x i :=
      fun i => Submodule.Quotient.mk_surjective _ (x i)
    choose k hk using hpre
    have hπk : π k = x := funext hk
    obtain ⟨y, hy⟩ := hlift (matAct (M := FractionRing O) A k) (by
      rw [← hAπ, hπk]
      exact hx)
    refine ⟨y, Subtype.ext ?_⟩
    rw [hφ, hy, ← he, e.symm_apply_apply, hπk]
  have hkerφ : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      rw [hφ, Matrix.mulVecLin_apply, ← hAι, ← he, e.symm_apply_apply, hπι]
      rfl
    · intro hy
      have h0 : π (e.symm (ι y)) = 0 := by
        rw [← hφ, hy]
        rfl
      obtain ⟨z, hz⟩ := hlift _ h0
      refine ⟨z, hιinj ?_⟩
      rw [Matrix.mulVecLin_apply, ← hAι, hz, ← he, e.apply_symm_apply]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerφ).trans (φ.quotKerEquivOfSurjective hsurj)⟩

theorem length_ker_matAct_eq_top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (h : A.det = 0) :
    Module.length O (LinearMap.ker (matAct (M := KmodO O) A)) = ⊤ := by
  classical
  by_contra hne
  have hfl := Module.length_ne_top_iff.mp hne
  have : IsNoetherian O (LinearMap.ker (matAct (M := KmodO O) A)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = 0 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨v, hv0, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hh
    exact hv0 (funext fun i => by
      by_contra hi
      exact hh ⟨i, hi⟩)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let g0 : FractionRing O →ₗ[O] (Fin n → KmodO O) :=
    π ∘ₗ LinearMap.pi (fun i => LinearMap.mulRight O (v i))
  have hg0 : ∀ t, g0 t = π (t • v) := fun t => rfl
  have hg0mem : ∀ t, g0 t ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro t
    rw [LinearMap.mem_ker, hg0]
    refine (matAct_comp_linear A
      (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (t • v)).trans ?_
    rw [matAct_fractionRing, ← hB, Matrix.mulVec_smul, hBv, smul_zero]
    funext i
    simp
  let g := g0.codRestrict _ hg0mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  have hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • LinearMap.range g := by
    rintro _ ⟨t, rfl⟩
    have ht : t = ϖ • (t / algebraMap O (FractionRing O) ϖ) := by
      rw [Algebra.smul_def]
      field_simp
    rw [ht, map_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) ⟨_, rfl⟩
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O)
    (LinearMap.range g) (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  set t := (algebraMap O (FractionRing O) ϖ * v i0)⁻¹ with ht
  have hgt : g t = 0 := by
    have hm : g t ∈ LinearMap.range g := ⟨t, rfl⟩
    rw [hbot] at hm
    exact (Submodule.mem_bot O).mp hm
  have hcomp : π (t • v) i0 = 0 := by
    rw [← hg0]
    exact congrFun (congrArg Subtype.val hgt) i0
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hcomp
  have ha' : algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) ϖ = 1 := by
    have h1 : algebraMap O (FractionRing O) a = t * v i0 := ha
    rw [h1, ht]
    field_simp
  rw [← map_mul, ← map_one (algebraMap O (FractionRing O))] at ha'
  have hmul : a * ϖ = 1 := IsFractionRing.injective O (FractionRing O) ha'
  have hunit : IsUnit ϖ := ⟨⟨ϖ, a, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩
  exact hϖ.not_isUnit hunit

theorem length_ker_matAct_kmod_eq_addVal_det :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : ℕ)
      (Φ : Matrix (Fin a) (Fin a) O),
      Module.length O (LinearMap.ker (Formalism.MainNotions.BlochKatoReduction.matAct (M := Formalism.BasicNotions.KmodO O) Φ)) =
        IsDiscreteValuationRing.addVal O Φ.det := by
  intro O _ _ _ a Φ
  by_cases h : Φ.det = 0
  · rw [length_ker_matAct_eq_top Φ h, h, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨e⟩ := nonempty_coker_equiv_ker_matAct Φ h
    rw [← e.length_eq]
    exact RelativeLengthSpanDet.length_coker Φ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundary
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.TopSteps

theorem mem_cob_of_repr_mem_herrB : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k)
    (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  intro k G _ _ l n _ _ _ R F A z b g hR hB
  obtain ⟨E, a, p, e, ε, hE, ha, hp, hinj, hex, hpe, hρe, hε⟩ := hR
  unfold GlobalTheory.Models.herrB at hB
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hB

  have hbx : ∀ i, b i = (F.D A).φ i (x (i - 1)) - x i := fun i => by
    have h := congrArg (fun q => q.1 i) hx
    simp at h
    exact h.symm
  have hgx : ∀ i, g i = (F.D A).γ i (x i) - x i := fun i => by
    have h := congrArg (fun q => q.2 i) hx
    simp at h
    exact h.symm
  have hA : F.Obj A := F.obj_sub A E a ha hinj hE
  have h1 : F.Obj (GlobalTheory.Models.chr (1 : G →* kˣ)) := F.obj_one

  set η : ZMod n → Vc k E.m := fun i => ε i - F.map A E a i (x i) with hη
  have hηφ : ∀ i, (F.D E).φ i (η (i - 1)) = η i := by
    intro i
    have h2 := (hε i).2.1
    rw [hbx i, map_sub, F.map_φ A E a hA hE ha] at h2
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2.symm
  have hηγ : ∀ i, (F.D E).γ i (η i) = η i := by
    intro i
    have h3 := (hε i).2.2
    rw [hgx i, map_sub, F.map_γ A E a hA hE ha] at h3
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h3.symm
  obtain ⟨f, hf, hfη⟩ := F.fix E hE η hηφ hηγ

  have hmap0 : ∀ i y, F.map A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 i y = 0 := by
    intro i y
    have h := F.map_smul A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 0 hA h1 (fun _ _ => by simp) i y
    simpa using h
  have hpa : p ∘ₗ a = 0 := LinearMap.ext fun y => hex.apply_apply_eq_zero y
  have hpa_map : ∀ i y, F.map E (GlobalTheory.Models.chr (1 : G →* kˣ)) p i (F.map A E a i y) = 0 := by
    intro i y
    have h := F.map_comp A E (GlobalTheory.Models.chr (1 : G →* kˣ)) a p hA hE h1 ha hp i
    rw [hpa] at h
    have h' := LinearMap.congr_fun h y
    simpa [hmap0] using h'.symm

  set one : Fin 1 → k := fun _ => 1 with hone
  set c : k := p (f one) 0 with hc
  have hqc : ∀ v : Fin 1 → k, p (f v) = c • v := by
    intro v
    have hv : v = v 0 • one := funext fun j => by
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [hone]
    rw [hv, map_smul, map_smul]
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hc, hone, mul_comm]
  have hq : p ∘ₗ f = c • LinearMap.id := LinearMap.ext fun v => by simp [hqc]
  have hidH : GlobalTheory.Models.IsHom (GlobalTheory.Models.chr (1 : G →* kˣ)) (GlobalTheory.Models.chr (1 : G →* kˣ)) LinearMap.id :=
    fun _ _ => rfl

  have hcu : c • F.unit 0 = F.unit 0 := by
    have hcomp := F.map_comp _ E _ f p h1 hE h1 hf hp 0
    have hval := LinearMap.congr_fun hcomp (F.unit 0)
    rw [LinearMap.comp_apply, hfη 0, hη, map_sub, (hε 0).1, hpa_map, sub_zero, hq,
      F.map_smul _ _ _ c h1 h1 hidH, F.map_id _ h1] at hval
    simpa using hval
  have hc1 : c = 1 := by
    by_contra hne
    have hu : (c - 1) • F.unit 0 = 0 := by rw [sub_smul, one_smul, hcu, sub_self]
    apply F.unit_ne 0
    have h := inv_smul_smul₀ (sub_ne_zero.mpr hne) (F.unit 0)
    rw [hu, smul_zero] at h
    exact h.symm

  have hpw : p (f one) = one := by rw [hqc, hc1, one_smul]
  have hρ1 : ∀ σ (v : Fin 1 → k), (GlobalTheory.Models.chr (1 : G →* kˣ)).ρ σ v = v := fun σ v => by
    change ((1 : G →* kˣ) σ : k) • LinearMap.id v = v
    simp
  have hw : ∀ σ, E.ρ σ (f one) = f one := fun σ => by
    rw [← hf σ one, hρ1]

  have hker : p (e - f one) = 0 := by rw [map_sub, hpe, hpw, sub_self]
  obtain ⟨y, hy⟩ := (hex (e - f one)).1 hker
  have hkey : ∀ σ, A.ρ σ y = y + z σ := fun σ => by
    apply hinj
    rw [ha σ y, hy, map_sub, hρe σ, hw σ, map_add (f := _), hy]
    abel
  unfold GlobalTheory.Models.cob
  refine LinearMap.mem_range.mpr ⟨y, funext fun σ => ?_⟩
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hkey σ]
  abel

end GlobalTheory.TopSteps
end

