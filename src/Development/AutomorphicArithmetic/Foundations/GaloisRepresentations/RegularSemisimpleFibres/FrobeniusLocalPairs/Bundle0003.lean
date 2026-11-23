module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CptCpt
section
noncomputable section

open ValuativeRel Matrix

namespace UpperTheory.Gal.InertialTypesAlt.L

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isOpen_ball (c : (ValueGroupWithZero k)ˣ) :
    IsOpen {y : k | valuation k y ≤ (c : ValueGroupWithZero k)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨c, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_setOf_eq] at hz hx ⊢
  exact le_trans (Valuation.map_add _ _ _) (max_le hx (le_of_lt hz))

private theorem isIntegral_of_cpt {n : ℕ} (g : GL (Fin n) k)
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) k)))) :
    IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) := by
  have hcont : ∀ i j : Fin n, Continuous (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) :=
    fun i j => Units.continuous_val.matrix_elem i j
  set S := ⋃ (i : Fin n) (j : Fin n), (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) ''
    closure (Subgroup.zpowers g : Set (GL (Fin n) k)) with hS
  have hSc : IsCompact S := isCompact_iUnion (fun i => isCompact_iUnion (fun j => hg.image (hcont i j)))
  obtain ⟨c, hc⟩ : ∃ c : (ValueGroupWithZero k)ˣ, S ⊆ {y | valuation k y ≤ (c : ValueGroupWithZero k)} := by
    apply hSc.elim_directed_cover (fun c : (ValueGroupWithZero k)ˣ => {y | valuation k y ≤ (c : ValueGroupWithZero k)})
    · exact fun c => isOpen_ball c
    · intro y _
      rw [Set.mem_iUnion]
      by_cases hy : valuation k y = 0
      · exact ⟨1, by simp [hy]⟩
      · exact ⟨Units.mk0 _ hy, by simp only [Set.mem_setOf_eq, Units.val_mk0, le_refl]⟩
    · intro a b
      rcases le_total (a : ValueGroupWithZero k) b with h | h
      · exact ⟨b, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _), fun y hy => hy⟩
      · exact ⟨a, fun y hy => hy, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _)⟩
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  apply GlobalTheory.isIntegral_matrix_of_pow_bounded (g : Matrix (Fin n) (Fin n) k) a ha0
  intro m i j
  have hmem : ((g ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ S := by
    rw [hS, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨j, g ^ m, subset_closure (Subgroup.npow_mem_zpowers g m), rfl⟩
  have hle : valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ (c : ValueGroupWithZero k) := by
    have h1 := hc hmem
    rw [Units.val_pow_eq_pow_val] at h1
    exact h1
  refine ⟨⟨a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j, ?_⟩, rfl⟩
  show valuation k (a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ 1
  rw [map_mul, ha]
  calc ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j)
      ≤ ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * c := by gcongr
    _ = 1 := Units.inv_mul c

private theorem bounded_adjoin {n : ℕ} (N : Matrix (Fin n) (Fin n) k) (hs : N.charpoly.Separable) :
    ∃ c : ValueGroupWithZero k, ∀ g ∈ Algebra.adjoin k {N}, IsIntegral 𝒪[k] g →
      ∀ i j, valuation k (g i j) ≤ c := by
  have hI := Valuation.integer.integers (valuation k)
  exact GlobalTheory.LocBounded.bounded_of_isIntegral_general (valuation k) (fun y => y.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
    (fun x hx => hI.isIntegral_iff_v_le_one.mp hx) N hs

private theorem isCompact_entries (n : ℕ) (c : ValueGroupWithZero k) :
    IsCompact {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
      {x : k | valuation k x ≤ c}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k c
  have e : {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} =
      (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ c}) := by
    ext M
    exact ⟨fun hM i _ j _ => hM i j, fun hM i j => hM i trivial j trivial⟩
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.L

private theorem isIntegral_mul_of_mem_adjoin_singleton {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (A x y : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Algebra.adjoin k {A}) (hy : y ∈ Algebra.adjoin k {A})
    (hxi : IsIntegral 𝒪[k] x) (hyi : IsIntegral 𝒪[k] y) : IsIntegral 𝒪[k] (x * y) := by
  letI : CommRing (Algebra.adjoin k {A}) := by
    open scoped IsMulCommutative in
      exact inferInstance
  let f : Algebra.adjoin k {A} →ₐ[𝒪[k]] Matrix (Fin n) (Fin n) k :=
    (Algebra.adjoin k {A}).val.restrictScalars 𝒪[k]
  have hinj : Function.Injective f := Subtype.val_injective
  have h1 : IsIntegral 𝒪[k] (⟨x, hx⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hxi
  have h2 : IsIntegral 𝒪[k] (⟨y, hy⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hyi
  exact (isIntegral_algHom_iff f hinj).mpr (h1.mul h2)

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.cptCpt :
    UpperTheory.Gal.InertialTypesAlt.L.CptCpt := by
  intro k _ _ _ _ n A T hA hT hcomm
  obtain ⟨-, -, hT2, -, hprop⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_holds k n
  haveI := hT2
  obtain ⟨c, hc⟩ := bounded_adjoin (A : Matrix (Fin n) (Fin n) k) hA
  have hΩ := isCompact_entries (k := k) n c
  have hC := hprop _ _ hΩ hΩ
  let K0 : Subgroup (GL (Fin n) k) :=
    { carrier := {g | (g : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)}
      mul_mem' := by
        rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_mul]
          exact Subalgebra.mul_mem _ hg1 hh1
        · rw [Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hg1 hh1 hg2 hh2
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact Subalgebra.mul_mem _ hh3 hg3
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hh3 hg3 hh4 hg4
      one_mem' := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_one]
          exact Subalgebra.one_mem _
        · rw [Units.val_one]
          exact isIntegral_one
        · rw [inv_one, Units.val_one]
          exact Subalgebra.one_mem _
        · rw [inv_one, Units.val_one]
          exact isIntegral_one
      inv_mem' := by
        rintro g ⟨hg1, hg2, hg3, hg4⟩
        refine ⟨hg3, hg4, ?_, ?_⟩
        · rw [inv_inv]
          exact hg1
        · rw [inv_inv]
          exact hg2 }
  have hsub : (K0 : Set (GL (Fin n) k)) ⊆
      {g | (g : Matrix (Fin n) (Fin n) k) ∈ {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈
          {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c}} := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨hc _ hg1 hg2, hc _ hg3 hg4⟩
  have hK1 : IsCompact (K0.topologicalClosure : Set (GL (Fin n) k)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  have hgen : ∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) k))) → t ∈ K0 := by
    intro t ht hcpt
    have hcA : ∀ s ∈ T, (s : Matrix (Fin n) (Fin n) k) * A = A * s := by
      intro s hs
      rw [← Units.val_mul, ← Units.val_mul, (hcomm s hs).eq]
    have hcpt' : IsCompact (closure (Subgroup.zpowers t⁻¹ : Set (GL (Fin n) k))) := by
      rw [Subgroup.zpowers_inv]
      exact hcpt
    exact ⟨GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t ht), isIntegral_of_cpt t hcpt,
      GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t⁻¹ (T.inv_mem ht)), isIntegral_of_cpt t⁻¹ hcpt'⟩
  have hle : GlobalTheory.BCT.cptPart T ≤ T ⊓ K0.topologicalClosure := by
    unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hcpt⟩
    exact ⟨ht, Subgroup.le_topologicalClosure K0 (hgen t ht hcpt)⟩
  have hge : T ⊓ K0.topologicalClosure ≤ GlobalTheory.BCT.cptPart T := GlobalTheory.LocFin.inf_le_cptPart T _ hK1
  rw [le_antisymm hle hge, Subgroup.coe_inf]
  exact hK1.inter_left hT
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbSum
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem continuous_of_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (F : G → ℂ) (h : ∀ u ∈ U, ∀ x, F (x * u) = F x) :
    Continuous F := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hev : F =ᶠ[nhds x] fun _ => F x := by
    have hop : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (U : Set G)) :=
      hU.preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y => x⁻¹ * y) ⁻¹' (U : Set G) := by
      simp [U.one_mem]
    filter_upwards [hop.mem_nhds hx] with y hy
    have h1 := h (x⁻¹ * y) hy x
    simpa using h1
  exact continuousAt_const.congr hev.symm

private theorem cptPart_le {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) :
    GlobalTheory.BCT.cptPart T ≤ T :=
  (Subgroup.closure_le _).2 fun _ ht => ht.1

theorem orbSum : OrbSum := by
  unfold OrbSum
  intro G _ _ _ _ _ _ _ _ μ hμ K hKo hKc hK1 θ hθ δ T hT hcomm hC ν hν U f hU hf hcm
  subst hT
  obtain ⟨hUo, hUK, hUθ⟩ := hU
  obtain ⟨hfc, hfi⟩ := hf
  set F : G → ℂ := fun x => f (x⁻¹ * δ * θ x) with hF
  have hTcl : IsClosed (GlobalTheory.BCT.twCent θ δ : Set G) := by
    show IsClosed {g : G | g * δ = δ * θ g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul hθ)
  have hFU : ∀ u ∈ U, ∀ x : G, F (x * u) = F x := by
    intro u hu x
    show f ((x * u)⁻¹ * δ * θ (x * u)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    have h1 : θ u ∈ U := hUθ u hu
    have hu' : u⁻¹ ∈ U := U.inv_mem hu
    calc f (u⁻¹ * x⁻¹ * δ * (θ x * θ u)) = f (u⁻¹ * (x⁻¹ * δ * θ x) * θ u) := by
          simp only [mul_assoc]
      _ = f (u⁻¹ * (x⁻¹ * δ * θ x)) := (hfi _ h1 _).2
      _ = f (x⁻¹ * δ * θ x) := (hfi _ hu' _).1
  have hFT : ∀ t ∈ GlobalTheory.BCT.twCent θ δ, ∀ x : G, F (t * x) = F x := by
    intro t ht x
    have h : t * δ = δ * θ t := ht
    have h2 : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← h, inv_mul_cancel_left]
    show f ((t * x)⁻¹ * δ * θ (t * x)) = f (x⁻¹ * δ * θ x)
    rw [_root_.mul_inv_rev, map_mul]
    calc f (x⁻¹ * t⁻¹ * δ * (θ t * θ x)) = f (x⁻¹ * (t⁻¹ * δ * θ t) * θ x) := by
          simp only [mul_assoc]
      _ = f (x⁻¹ * δ * θ x) := by rw [h2]
  have hFc : Continuous F := continuous_of_rightInv U hUo F hFU
  obtain ⟨_, hsum⟩ := sumCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT hcm
  have hmapK : ∀ q x : G, x ∈ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K ↔
      q⁻¹ * x * q ∈ K := by
    intro q x
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro hx
      exact ⟨q⁻¹ * x * q, hx, by simp [mul_assoc]⟩
  have hset : ∀ q : G, {t : GlobalTheory.BCT.twCent θ δ | q⁻¹ * (t : G) * q ∈ K} =
      {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    ext t
    simp only [Set.mem_setOf_eq, Subgroup.mem_inf, hmapK, SetLike.coe_mem, true_and]
  have hopen : ∀ q : G, IsOpen {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K} := by
    intro q
    rw [← hset q]
    exact hKo.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  have hvol : ∀ q : G, _ := fun q => volIdx G (GlobalTheory.BCT.twCent θ δ) (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ))
    (GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj q)) K) hTcl ν hν
    (cptPart_le _) hC
    (GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc q)) (hopen q)
  have hCfin : ν {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ ⊤ :=
    ((hTcl.isClosedEmbedding_subtypeVal).isCompact_preimage hC).measure_lt_top.ne
  have hCne : ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} ≠ 0 := by
    have h1 := (hvol 1).1
    have hsub : {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (1 : G))) K} ⊆
        {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)} :=
      fun t ht => GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj K hKc 1) ht
    have h2 := measureReal_mono hsub hCfin
    intro h0
    exact h1 (le_antisymm (h0 ▸ h2) measureReal_nonneg)
  refine ⟨hCne, ?_⟩
  rw [hsum]
  unfold GlobalTheory.BCT.twOrb
  rw [mul_finsum]
  refine finsum_congr fun q => ?_
  obtain ⟨hH0, hCeq⟩ := hvol (Quotient.out q)
  have hidx : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℝ) ≠ 0 := fun h0 => hCne (by rw [hCeq, h0, zero_mul])
  rw [oneCoset G μ hμ K hKo hKc hK1 _ hTcl hcomm ν hν F hFc hFT (Quotient.out q)]
  rw [← avgInt G μ hμ K hKo hKc hK1 U hUo F hFU (Quotient.out q)]
  rw [hset, hCeq]
  rw [show (fun y : K => F (Quotient.out q * ↑y)) =
    fun k : K => f ((Quotient.out q * ↑k)⁻¹ * δ * θ (Quotient.out q * ↑k)) from rfl]
  have hidxC : ((GlobalTheory.BCT.twCent θ δ ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K).relIndex
      (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hHC : ((ν.real {t : GlobalTheory.BCT.twCent θ δ | (t : G) ∈ GlobalTheory.BCT.twCent θ δ ⊓
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj (Quotient.out q))) K} : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hH0
  push_cast
  field_simp

end UpperTheory.Gal.InertialTypesAlt.L
end
end

