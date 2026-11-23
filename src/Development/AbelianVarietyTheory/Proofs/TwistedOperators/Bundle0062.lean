module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientCompactOfBoundedMatrices
section
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS.CptQuot

theorem continuous_adj {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ) (J : Matrix n n A) :
    Continuous (adj σ J) := by
  unfold adj
  have hc : Continuous (fun l : Matrix n n A => cT σ l) := by
    unfold Formalism.UG.cT
    exact (continuous_id.matrix_map hσ).matrix_transpose
  exact (continuous_const.matrix_mul hc).matrix_mul continuous_const

theorem exists_isCompact {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (hσ : Continuous σ)
    {J : Matrix n n A} (hJ : IsUnit J.det) (γ : GL n A) {D : Set (Matrix n n A)}
    (hD : IsCompact D) :
    ∃ K : Set (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)), IsCompact K ∧
      ∀ g : (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)),
        ((g : GL n A) : Matrix n n A) ∈ D → g ∈ K := by
  have hca := continuous_adj σ hσ J
  let C : Set (Matrix n n A) := D ∩ {M | M * adj σ J M = 1 ∧ adj σ J M * M = 1 ∧
    M * (γ : Matrix n n A) = (γ : Matrix n n A) * M}
  have hCc : IsCompact C := by
    refine hD.inter_right ?_
    exact (isClosed_eq (continuous_id.matrix_mul hca) continuous_const).inter
      ((isClosed_eq (hca.matrix_mul continuous_id) continuous_const).inter
        (isClosed_eq (continuous_id.matrix_mul continuous_const)
          (continuous_const.matrix_mul continuous_id)))
  let u : C → GL n A := fun M => ⟨M.1, adj σ J M.1, M.2.2.1, M.2.2.2.1⟩
  have hu : ∀ M : C, u M ∈ (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := by
    intro M
    refine Subgroup.mem_inf.2 ⟨(mem_UJ_iff_adj_mul σ hJ (u M)).2 M.2.2.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact M.2.2.2.2.symm
  let f : C → (UJ σ J ⊓ Subgroup.centralizer {γ} : Subgroup (GL n A)) := fun M => ⟨u M, hu M⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, hca.comp continuous_subtype_val⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  refine ⟨Set.range f, isCompact_range hf, ?_⟩
  intro g hg
  have hg' := Subgroup.mem_inf.1 g.2
  have h1 := (mem_UJ_iff_mul_adj σ hJ (g : GL n A)).1 hg'.1
  have h2 := (mem_UJ_iff_adj_mul σ hJ (g : GL n A)).1 hg'.1
  have h3 : ((g : GL n A) : Matrix n n A) * γ = γ * (g : GL n A) := by
    have hc := congrArg Units.val (Subgroup.mem_centralizer_iff.1 hg'.2 γ (Set.mem_singleton γ))
    rw [Units.val_mul, Units.val_mul] at hc
    exact hc.symm
  refine ⟨⟨_, hg, h1, h2, h3⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

theorem compactOfMatBounded (hL : TensorLattice) : CompactOfMatBounded := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hM
  have := quad_finite hreg.quad
  obtain ⟨hTR, -, hT2, -⟩ := hL F E
  obtain ⟨D, hD, hDg⟩ := hM
  let : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  have : IsTopologicalRing (E ⊗[F] AdeleRing (𝓞 F) F) := hTR
  have : T2Space (E ⊗[F] AdeleRing (𝓞 F) F) := hT2
  have hD' : IsCompact D := hD
  have hσ' : Continuous (sigR σ (AdeleRing (𝓞 F) F)) := continuous_sigR σ (AdeleRing (𝓞 F) F)
  have hJ' : IsUnit (J.map (inclE (F := F) (AdeleRing (𝓞 F) F))).det :=
    isUnit_det_map (inclE (F := F) (AdeleRing (𝓞 F) F)) hreg.nondeg
  have key : ∃ K : Set (centPts σ J γ (AdeleRing (𝓞 F) F)), IsCompact K ∧
      ∀ g : centPts σ J γ (AdeleRing (𝓞 F) F),
        ((g : GL n (E ⊗[F] AdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] AdeleRing (𝓞 F) F)) ∈ D →
          g ∈ K :=
    exists_isCompact (sigR σ (AdeleRing (𝓞 F) F)) hσ' hJ'
      (bc (inclE (F := F) (AdeleRing (𝓞 F) F)) γ) hD'
  obtain ⟨K, hK, hKD⟩ := key
  have hδc : ∀ δ ∈ centRat σ J γ,
      bc (inclE (F := F) (AdeleRing (𝓞 F) F)) δ ∈ centPts σ J γ (AdeleRing (𝓞 F) F) := by
    intro δ hδ
    have hδ' := Subgroup.mem_inf.1 (show δ ∈ UJ (σ : E →+* E) J ⊓ Subgroup.centralizer {γ} from hδ)
    have hadj := (mem_UJ_iff_adj_mul (σ : E →+* E) hreg.nondeg δ).1 hδ'.1
    have hcomm := Subgroup.mem_centralizer_iff.1 hδ'.2 γ (Set.mem_singleton γ)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show _ ∈ UJ (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
      rw [mem_UJ_iff_adj_mul _ hJ']
      show adj (sigR σ (AdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (AdeleRing (𝓞 F) F)))
          ((δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F))) *
          (δ : Matrix n n E).map (inclE (F := F) (AdeleRing (𝓞 F) F)) = 1
      rw [adj_map (σ : E →+* E) (sigR σ (AdeleRing (𝓞 F) F)) (inclE (F := F) (AdeleRing (𝓞 F) F))
        (fun x => inclE_conj σ (AdeleRing (𝓞 F) F) x) hreg.nondeg, ← Matrix.map_mul, hadj,
        Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul, hcomm]
  refine ⟨?_⟩
  have himg : (QuotientGroup.mk '' K : Set (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
      ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
        (centPts σ J γ (AdeleRing (𝓞 F) F)))) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨δ, hδ, hgδ⟩ := hDg g g.2
    refine ⟨g * ⟨_, hδc δ hδ⟩, hKD _ hgδ, ?_⟩
    exact QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ, hδ, rfl⟩))
  rw [← himg]
  exact hK.image QuotientGroup.continuous_mk

end GlobalTheory.RegSS.CptQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicQuotientNotCompactOfSplitIdempotent
section
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem bddAbove_of_compact_quotient {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G)
    [CompactSpace (G ⧸ H)] (f : G →* ℝ) (hf : Continuous f) (hH : ∀ h ∈ H, f h = 1) :
    ∃ C : ℝ, ∀ g, f g ≤ C := by
  let φ : G ⧸ H → ℝ := Quotient.lift f fun a b hab => by
    have h := hH _ (QuotientGroup.leftRel_apply.1 hab)
    rw [← mul_one (f a), ← h, ← map_mul, mul_inv_cancel_left]
  have hφ : Continuous φ := hf.quotient_lift _
  obtain ⟨C, hC⟩ := (isCompact_range hφ).bddAbove
  exact ⟨C, fun g => hC ⟨(g : G ⧸ H), rfl⟩⟩

theorem exists_one_lt_ideleNorm (F : Type) [Field F] [NumberField F] :
    ∃ t : Idele F, 1 < ideleNorm t := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let P : HeightOneSpectrum (𝓞 F) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformiser P
  have h1 : ‖(ϖ : P.adicCompletion F)‖ = (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp
  refine ⟨(localIdele P ϖ)⁻¹, ?_⟩
  rw [map_inv, UnitaryHeckeChar.ideleNorm_localIdele, h1, inv_inv]
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P

theorem commute_map_of_mem_centPts {F E : Type} [Field F] [CommRing E] [Algebra F E]
    {n : Type} [Fintype n] [DecidableEq n] {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E}
    (R : Type) [CommRing R] [Algebra F R] {ε : Matrix n n E} (hε : ε ∈ genAlg (γ : Matrix n n E))
    {g : GL n (E ⊗[F] R)} (hg : g ∈ centPts σ J γ R) :
    (g : Matrix n n (E ⊗[F] R)) * ε.map (inclE (F := F) R) = ε.map (inclE (F := F) R) * g := by
  have h : (g : Matrix n n (E ⊗[F] R)) * (γ : Matrix n n E).map (inclE (F := F) R) =
      (γ : Matrix n n E).map (inclE (F := F) R) * g :=
    congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.1 hg.2)
  refine commute_of_mem_genAlg h ?_
  induction hε using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]; exact Algebra.self_mem_adjoin_singleton _ _
  | algebraMap r =>
    have : (algebraMap E (Matrix n n E) r).map (inclE (F := F) R) =
        algebraMap (E ⊗[F] R) _ (inclE (F := F) R r) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _)]; exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [Matrix.map_mul]; exact mul_mem hx hy

theorem notCompactOfIdempotent_of (hD : IdempotentDet) : NotCompactOfIdempotent := by
  intro F E _ _ _ _ n _ _ σ J γ hreg ε hε hε0 hεε ht hc
  haveI := quad_finite hreg.quad
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  obtain ⟨d, χ, hd, hχ, h1, hmul, hrat, hval⟩ := hD F E n ε hε0 hεε (AdeleRing (𝓞 F) F)
  let χ₀ : centPts σ J γ (AdeleRing (𝓞 F) F) →* AdeleRing (𝓞 F) F :=
    { toFun := fun g => χ (g.1 : Matrix n n _)
      map_one' := h1
      map_mul' := fun g h => hmul _ _ (commute_map_of_mem_centPts _ hε h.2) }
  have hχ₀ : Continuous χ₀ := hχ.comp (Units.continuous_val.comp continuous_subtype_val)
  have hχi : Continuous fun g => χ₀ g⁻¹ :=
    hχ.comp (Units.continuous_coe_inv.comp continuous_subtype_val)
  have hχ₁ : Continuous χ₀.toHomUnits := Units.continuous_iff.2 ⟨hχ₀, hχi⟩
  haveI : CompactSpace (centPts σ J γ (AdeleRing (𝓞 F) F) ⧸
    ((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) := hc
  obtain ⟨C, hC⟩ := bddAbove_of_compact_quotient
    (((centRat σ J γ).map (bc (inclE (F := F) (AdeleRing (𝓞 F) F)))).subgroupOf
      (centPts σ J γ (AdeleRing (𝓞 F) F))) (ideleNorm.comp χ₀.toHomUnits)
    (continuous_ideleNorm.comp hχ₁) (by
      rintro g ⟨δ, -, hδ⟩
      obtain ⟨c, hc⟩ := hrat δ
      have e : ((χ₀.toHomUnits g : Idele F) : AdeleRing (𝓞 F) F) = algebraMap F _ c := by
        rw [← hc]
        change χ (g.1 : Matrix n n _) = _
        rw [show g.1 = _ from hδ.symm]
        rfl
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at e
        haveI : Nontrivial (AdeleRing (𝓞 F) F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
        exact Units.ne_zero _ e
      have e' : χ₀.toHomUnits g = principalIdele F (Units.mk0 c hc0) := Units.ext e
      rw [MonoidHom.comp_apply, e', ideleNorm_principalIdele])
  obtain ⟨t, ht1⟩ := exists_one_lt_ideleNorm F
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (one_lt_pow₀ ht1 hd.ne')
  obtain ⟨g, hg, hgt⟩ := ht (t ^ m)
  have e : χ₀.toHomUnits ⟨g, hg⟩ = (t ^ m) ^ d := Units.ext (hval _ _ hgt)
  have := hC ⟨g, hg⟩
  rw [MonoidHom.comp_apply, e, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul] at this
  exact absurd hm (not_lt.2 this)

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactors
section
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem unitBounded_of_split (hL : TensorLattice) {F B : Type} [Field F] [NumberField F]
    [CommRing B] [Algebra F B] [Module.Finite F B] (τ : B →ₐ[F] B) {k : ℕ} (C : Fin k → Type)
    [∀ i, CommRing (C i)] [∀ i, Algebra F (C i)] (ρ : ∀ i, C i →ₐ[F] C i)
    (π : ∀ i, B →ₐ[F] C i) (s : ∀ i, C i →ₗ[F] B)
    (hsum : ∀ x, ∑ i, s i (π i x) = x)
    (hmul : ∀ i x y, s i (π i x * y) = x * s i y)
    (hps : ∀ (b : ∀ i, C i) j, π j (∑ i, s i (b i)) = b j)
    (hcomm : ∀ i x, π i (τ x) = ρ i (π i x))
    (h : ∀ i, UnitBounded F (C i) (ρ i)) : UnitBounded F B τ := by
  classical
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  letI (i : Fin k) : TopologicalSpace (C i ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := C i) (AdeleRing (𝓞 F) F)
  haveI := (hL F B).1
  choose D hD hDu using h
  let p (i : Fin k) : B ⊗[F] AdeleRing (𝓞 F) F →ₐ[F] C i ⊗[F] AdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.map (π i) (AlgHom.id F _)
  let Φ : (∀ i, C i ⊗[F] AdeleRing (𝓞 F) F) → B ⊗[F] AdeleRing (𝓞 F) F :=
    fun x => ∑ i, LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i) (x i)
  have hΦ : Continuous Φ :=
    continuous_finsetSum _ fun i _ =>
      (continuous_rTensor (AdeleRing (𝓞 F) F) (s i)).comp (continuous_apply i)
  have hp : ∀ i u, p i (sigR τ _ u) = sigR (ρ i) _ (p i u) := by
    intro i u
    induction u with
    | tmul a b => simp [p, sigR, hcomm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  have hm : ∀ i u (y : C i), LinearMap.rTensor (AdeleRing (𝓞 F) F) (s i)
      (p i u * inclE (F := F) _ y) = u * inclE (F := F) _ (s i y) := by
    intro i u y
    induction u with
    | tmul a b => simp [p, inclE, hmul]
    | add a b ha hb => rw [map_add (f := _), add_mul, map_add (f := _), add_mul, ha, hb]
  refine ⟨Φ '' Set.pi Set.univ D, (isCompact_univ_pi hD).image hΦ, fun u hu => ?_⟩
  have hpu : ∀ i, p i u * sigR (ρ i) _ (p i u) = 1 := fun i => by
    rw [← hp, ← map_mul, hu, map_one]
  choose β hβ hβD using fun i => hDu i (p i u) (hpu i)
  choose γ hγ using fun i => (hβ i).exists_right_inv
  refine ⟨∑ i, s i (β i), IsUnit.of_mul_eq_one (∑ i, s i (γ i)) ?_,
    fun i => p i u * inclE (F := F) _ (β i), fun i _ => hβD i, ?_⟩
  · rw [Finset.mul_sum]
    simp only [← hmul, hps, hγ]
    simpa using hsum 1
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [Φ, hm, map_sum, Finset.mul_sum]

theorem productUnitBounded (hL : TensorLattice) : ProductUnitBounded := by
  classical
  intro F E _ _ _ _ _ σ P _ _ _ k K _ _ ⟨e⟩ h
  let q (i : Fin k) : P →ₐ[F] K i := (Pi.evalAlgHom F K i).comp (e : P →ₐ[F] ∀ i, K i)
  let t (i : Fin k) : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  have hq : ∀ i x, q i x = e x i := fun _ _ => rfl
  have ht : ∀ i x, t i x = e.symm (Pi.single i x) := fun _ _ => rfl
  have h1 : ∀ x, ∑ i, t i (q i x) = x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, ht, ← map_sum, Finset.univ_sum_single, AlgEquiv.symm_apply_apply]
  have h2 : ∀ i x y, t i (q i x * y) = x * t i y := fun i x y => by
    apply e.injective
    simp only [hq, ht, map_mul, AlgEquiv.apply_symm_apply]
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  refine unitBounded_of_split hL (tConj P σ) (fun i => K i ⊗[F] E) (fun i => tConj (K i) σ)
    (fun i => Algebra.TensorProduct.map (q i) (AlgHom.id F E))
    (fun i => LinearMap.rTensor E (t i)) ?_ ?_ ?_ ?_ h
  · intro x
    induction x with
    | tmul a b => simp [← TensorProduct.sum_tmul, h1]
    | add a b ha hb => simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]
  · intro i x y
    induction x with
    | add a b ha hb => simp only [map_add (f := _), add_mul, ha, hb]
    | tmul a b =>
      induction y with
      | add c d hc hd => simp only [map_add (f := _), mul_add, hc, hd]
      | tmul c d => simp [h2]
  · intro b j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single j]
    · generalize b j = y
      induction y with
      | add c d hc hd => simp only [map_add (f := _), hc, hd]
      | tmul c d => simp [hq, ht]
    · intro i _ hi
      generalize b i = y
      induction y with
      | add c d hc hd => simp only [map_add (f := _), hc, hd, add_zero]
      | tmul c d => simp [hq, ht, hi.symm]
    · simp
  · intro i x
    induction x with
    | tmul a b => simp [tConj]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentraliserPointsBoundedOfNormOneBounded
section
noncomputable section

open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.MatBd

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

theorem assoc_sigR (P : Type) [CommRing P] [Algebra F P] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] (x : (P ⊗[F] E) ⊗[F] R) :
    Algebra.TensorProduct.assoc F F F P E R (sigR (tConj P σ) R x) =
      tConj3 P σ R (Algebra.TensorProduct.assoc F F F P E R x) := by
  induction x with
  | tmul a r =>
    induction a with
    | tmul p e => simp [sigR, tConj, tConj3]
    | add a b ha hb => rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

def entry (σ : E →ₐ[F] E) (J γ : Matrix n n E) (i j : n) : plusAlg σ J γ ⊗[F] E →ₗ[F] E where
  toFun x := (plusTensor σ J γ x : Matrix n n E) i j
  map_add' a b := by rw [map_add (f := _)]; rfl
  map_smul' c a := by rw [map_smul]; rfl

theorem toMat_assoc_apply (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (x : (plusAlg σ J γ ⊗[F] E) ⊗[F] R) (i j : n) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R x) i j =
      LinearMap.rTensor R (entry σ J γ i j) x := by
  induction x with
  | tmul a r =>
    induction a with
    | tmul p e =>
      have h : (plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) =
          e • ((p : genAlg γ) : Matrix n n E) := by
        rw [plusTensor, Algebra.TensorProduct.productMap_apply_tmul, mul_comm]
        exact (Algebra.smul_def e ((p : genAlg γ) : Matrix n n E)).symm
      rw [Algebra.TensorProduct.assoc_tmul, LinearMap.rTensor_tmul]
      change (((p : genAlg γ) : Matrix n n E).map (inclE (F := F) R) *
        algebraMap (E ⊗[F] R) (Matrix n n (E ⊗[F] R)) (e ⊗ₜ r)) i j =
        ((plusTensor σ J γ (p ⊗ₜ e) : Matrix n n E) i j) ⊗ₜ r
      rw [h, ← Algebra.commutes, ← Algebra.smul_def]
      simp [inclE]
    | add a b ha hb =>
      rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), Matrix.add_apply, ha, hb]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), Matrix.add_apply, ha, hb]

theorem toMat_assoc_inclE (σ : E →ₐ[F] E) (J γ : Matrix n n E) (R : Type) [CommRing R]
    [Algebra F R] (β : plusAlg σ J γ ⊗[F] E) :
    toMat σ J γ R (Algebra.TensorProduct.assoc F F F (plusAlg σ J γ) E R (inclE (F := F) R β)) =
      (plusTensor σ J γ β : Matrix n n E).map (inclE (F := F) R) := by
  ext i j
  rw [toMat_assoc_apply]
  rfl

theorem exists_centRat {σ : E →ₐ[F] E} {J : Matrix n n E} {γ : GL n E} (h : IsRegular σ J γ)
    (β : plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (hβ : β * tConj _ σ β = 1) :
    ∃ δ ∈ centRat σ J γ, (δ : Matrix n n E) = plusTensor σ J (γ : Matrix n n E) β := by
  have h1 : (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) *
      adj (σ : E →+* E) J (plusTensor σ J (γ : Matrix n n E) β : Matrix n n E) = 1 := by
    rw [← plusTensor_tConj h, ← Subalgebra.coe_mul, ← map_mul, hβ, map_one]
    rfl
  refine ⟨⟨_, _, h1, mul_eq_one_comm.1 h1⟩, ⟨(mem_UJ_iff_mul_adj _ h.nondeg _).2 h1, ?_⟩, rfl⟩
  refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_)
  exact (commute_of_mem_genAlg rfl (plusTensor σ J (γ : Matrix n n E) β).2).symm

theorem matOfNormBounded : MatOfNormBounded := by
  intro F E _ _ _ _ n _ _ σ J γ h _ _ hP hN
  obtain ⟨D, hD, hu⟩ := hN
  letI : TopologicalSpace (E ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := E) (AdeleRing (𝓞 F) F)
  letI : TopologicalSpace ((plusAlg σ J (γ : Matrix n n E) ⊗[F] E) ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := plusAlg σ J (γ : Matrix n n E) ⊗[F] E) (AdeleRing (𝓞 F) F)
  let a := Algebra.TensorProduct.assoc F F F (plusAlg σ J (γ : Matrix n n E)) E (AdeleRing (𝓞 F) F)
  have hc : Continuous fun x => toMat σ J (γ : Matrix n n E) (AdeleRing (𝓞 F) F) (a x) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [a, toMat_assoc_apply]
    exact continuous_rTensor _ _
  refine ⟨_, hD.image hc, fun g hg => ?_⟩
  obtain ⟨u, hu1, hug⟩ := ((hP (AdeleRing (𝓞 F) F)).2.2 g).1 hg
  obtain ⟨x, hx⟩ := a.surjective u
  obtain ⟨β, hβ, hxβ⟩ := hu x (a.injective (by
    rw [map_mul, map_one, assoc_sigR]
    change a x * tConj3 _ σ _ (a x) = 1
    rw [hx]
    exact hu1))
  obtain ⟨δ, hδ, hδβ⟩ := exists_centRat h β hβ
  refine ⟨δ, hδ, _, hxβ, ?_⟩
  beta_reduce
  rw [map_mul, map_mul, hx, hug, toMat_assoc_inclE, hδβ]

end GlobalTheory.RegSS.MatBd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharLocalValueDivUniformiserPow
section
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.HeckeLocDec

theorem localIdele_unitPart_mem (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (x : (w.adicCompletion L)ˣ) (a : ℤ) (ha : Valued.v (x : w.adicCompletion L) = WithZero.exp (-a)) :
    localIdele L w (x * (atFin w (unif w)) ^ (-a)) ∈ PI.AlgValsFin.W.UFin L := by
  refine ⟨?_, fun w' => ?_⟩
  · funext v
    exact (localIdele_isSupportedAt L w _).1 v
  · by_cases h : w' = w
    · subst h
      rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_self]
      have h1 : Valued.v ((atFin w' (unif w') : (w'.adicCompletion L)ˣ) : w'.adicCompletion L) =
          WithZero.exp (-1) := unif_spec w'
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h1, ha,
        ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    · rw [← PI.AlgValsFin.W.evF_val, PI.AlgValsFin.W.evF_localIdele_ne w' w h]
      simp

theorem loc_div_val_pow (L : Type) [Field L] [NumberField L] (χ : HChar L) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ),
      ∃ a : ℤ, ((χ.loc w x / χ.val w ^ a : ℂˣ) : ℂ) ^ N = 1 := by
  obtain ⟨N, hN, hT⟩ := PI.AlgValsFin.W.torsUnits L χ
  refine ⟨N, hN, fun w x => ?_⟩
  have hx0 : Valued.v (x : w.adicCompletion L) ≠ 0 := by simp
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v (x : w.adicCompletion L) = WithZero.exp (-a) :=
    ⟨-WithZero.log (Valued.v (x : w.adicCompletion L)), by rw [neg_neg, WithZero.exp_log hx0]⟩
  refine ⟨a, ?_⟩
  have hmem := localIdele_unitPart_mem L w x a ha
  have h := hT _ hmem
  have e : χ.loc w x / χ.val w ^ a = χ.1 (localIdele L w (x * (atFin w (unif w)) ^ (-a))) := by
    show χ.loc w x / χ.loc w (atFin w (unif w)) ^ a = χ.loc w (x * (atFin w (unif w)) ^ (-a))
    rw [map_mul, map_zpow, zpow_neg, div_eq_mul_inv]
  rw [e, ← Units.val_pow_eq_pow_val, h, Units.val_one]

end GlobalTheory.HeckeLocDec
end
end

