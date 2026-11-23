module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosetsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleRepresentatives_finite_level_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  first | exact @GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | exact GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | (intros; apply GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardQuadricSubSqLe
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.QuadricCount

lemma sum_dot {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (w : ι → k) :
    ∑ x : ι → k, ψ (x ⬝ᵥ w) = if w = 0 then ((Fintype.card k : ℂ) ^ Fintype.card ι) else 0 := by
  split_ifs with hw
  · subst hw; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hi' : w i ≠ 0 := hi
    have h1 : ∃ a : k, ψ (a * w i) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have := AddChar.sum_mulShift (w i) hψ
      simp [hcon, hi'] at this
    obtain ⟨a, ha⟩ := h1
    have h2 : ∑ x : ι → k, ψ (x ⬝ᵥ w) = ψ (a * w i) * ∑ x : ι → k, ψ (x ⬝ᵥ w) := by
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp (Equiv.addLeft (Pi.single i a : ι → k))]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [add_dotProduct, AddChar.map_add_eq_mul]
    have h3 : (1 - ψ (a * w i)) * ∑ x : ι → k, ψ (x ⬝ᵥ w) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h).symm ha
    · exact h

lemma gauss_normSq {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (S : Matrix ι ι k) (h2 : (2 : k) ≠ 0) (hS : S.IsSymm)
    (hd : S.det ≠ 0) (t : k) (ht : t ≠ 0) :
    ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))‖ ^ 2 = (Fintype.card k : ℝ) ^ Fintype.card ι := by
  have hsym : ∀ x z : ι → k, z ⬝ᵥ S.mulVec x = x ⬝ᵥ S.mulVec z := by
    intro x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq, dotProduct_comm]
  have key : (starRingEnd ℂ) (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)))
      = (Fintype.card k : ℂ) ^ Fintype.card ι := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    have e1 : ∀ x : ι → k, (starRingEnd ℂ) (ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ y : ι → k, ψ (t * (y ⬝ᵥ S.mulVec y)))
        = ∑ z : ι → k, ψ (t * (z ⬝ᵥ S.mulVec z)) * ψ (x ⬝ᵥ ((2 * t) • S.mulVec z)) := by
      intro x
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft x)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [Equiv.coe_addLeft, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hsym x z]
      ring
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_dot ψ hψ]
    rw [Finset.sum_eq_single (0 : ι → k)]
    · simp
    · intro z _ hz
      rw [if_neg, mul_zero]
      intro h
      rcases smul_eq_zero.mp h with h | h
      · exact mul_ne_zero h2 ht h
      · exact hz (Matrix.eq_zero_of_mulVec_eq_zero hd h)
    · simp
  rw [Complex.conj_mul'] at key
  exact_mod_cast key

theorem card_quadric_sub_sq_le : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (S : Matrix ι ι k) (β : k), (2 : k) ≠ 0 → S.IsSymm → S.det ≠ 0 → (((Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card : ℝ) - (Fintype.card k : ℝ) ^ (Fintype.card ι - 1)) ^ 2 ≤ (Fintype.card k : ℝ) ^ Fintype.card ι := by
  intro k _ _ _ ι _ _ _ S β h2 hS hd
  set ψ := AddChar.FiniteField.primitiveChar_to_Complex k
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k
  set N := (Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card with hN
  set q := Fintype.card k with hq
  set m := Fintype.card ι with hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hm0 : m = (m - 1) + 1 := by have : 0 < m := Fintype.card_pos; omega
  have e1 : ∑ x : ι → k, ∑ t : k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) * N := by
    simp_rw [AddChar.sum_mulShift _ hψ, sub_eq_zero]
    push_cast
    rw [← Finset.sum_filter]
    simp [hN, hq, mul_comm]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))] at e1
  have e2 : ∑ x : ι → k, ψ (0 * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) ^ m := by
    simp [hq, hm]
  rw [e2] at e1
  set r : ℝ := Real.sqrt ((q : ℝ) ^ m) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (q : ℝ) ^ m := Real.sq_sqrt (by positivity)
  have e3 : ∀ t ∈ Finset.univ.erase (0 : k), ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β))‖ ≤ r := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have : ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = ψ (-(t * β)) * ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this, norm_mul, AddChar.norm_apply, one_mul, hr, ← gauss_normSq ψ hψ S h2 hS hd t ht0, Real.sqrt_sq (norm_nonneg _)]
  have e4 : ‖(q : ℂ) * N - (q : ℂ) ^ m‖ ≤ q * r := by
    rw [← e1, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ e3).trans ?_)
    rw [nsmul_eq_mul]
    gcongr
    exact Finset.card_le_univ _
  have e5 : (q : ℂ) * N - (q : ℂ) ^ m = (((q : ℝ) * ((N : ℝ) - (q : ℝ) ^ (m - 1)) : ℝ) : ℂ) := by
    conv_lhs => rw [hm0]
    push_cast
    ring
  rw [e5, Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0] at e4
  have e6 := le_of_mul_le_mul_left e4 hq0
  rw [← hr2, ← sq_abs]
  gcongr

end GlobalTheory.QuadricCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct Topology

namespace GlobalTheory.Mem.Vol.StabGroup

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  haveI : ContinuousSMul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    have : (fun c : Fin m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add (f := _)]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E =>
      y p.1 * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) := by
  have : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  have ho : IsOpen {z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E | ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), z = N • y} :=
    (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E n L hL).1 N hN
  have hfz : (L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
    have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact (Module.Finite.iff_fg (N := L.restrictScalars ℤ)).mp (inferInstanceAs (Module.Finite ℤ L))
  obtain ⟨s, hs⟩ := hfz
  have hev : ∀ᶠ m : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) in 𝓝 1, ∀ x ∈ s,
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    rw [Filter.eventually_all_finset]
    intro x _
    have hc : Continuous fun m : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) =>
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x :=
      (continuous_id.matrix_mulVec continuous_const).sub continuous_const
    exact (ho.preimage hc).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hev fun m hm => ?_
  have hsm : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), a • y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
    intro a ha y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), x, hx, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have hadd : ∀ z w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E,
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y) →
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec w - w = N • y) →
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec (z + w) - (z + w) = N • y := by
    rintro z w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [smul_add, ← h, ← h', Matrix.mulVec_add]; abel⟩
  have hx : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hm x hx
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := funext fun i => TensorProduct.tmul_zero _ _
      exact ⟨0, zero_mem _, by simp [this]⟩
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y :=
        funext fun i => TensorProduct.tmul_add _ _ _
      rw [this]; exact hadd _ _ hx hy
    | smul c x _ hx =>
      obtain ⟨y, hy, h⟩ := hx
      have : GlobalTheory.AdLat.fv F (c • x) = c • GlobalTheory.AdLat.fv F x :=
        funext fun i => map_zsmul (TensorProduct.mk F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E 1) c (x i)
      refine ⟨c • y, zsmul_mem hy c, ?_⟩
      rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hxL, rfl⟩ := hz
    obtain ⟨y, hy, h⟩ := hx x (by rw [hs]; exact hxL)
    have : (fun i => a ⊗ₜ[F] x i) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp [GlobalTheory.AdLat.fv, TensorProduct.smul_tmul']
    refine ⟨a • y, hsm a ha y hy, ?_⟩
    rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add z w _ _ hz hw => exact hadd z w hz hw
  | neg z _ hz =>
    obtain ⟨y, hy, h⟩ := hz
    exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, Matrix.mulVec_neg]; abel⟩

noncomputable def stabGrp (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) :
    Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) where
  carrier := {h | StabHat F L (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J h).1}
  one_mem' := fun y => by
    change _ ↔ (1 : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)).mulVec y ∈ _
    rw [Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    change _ ↔ ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J a).1 * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J b).1).mulVec y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    change _ ↔ ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J a)⁻¹).1.mulVec y ∈ _
    rw [ha (((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J a)⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]

theorem exists_compact_open_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J h : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J)) ∧ IsCompact (K : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J)) := by
  intro F E _ _ _ _ _ σ M J L hfg hsp
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  haveI : T2Space (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  haveI : T2Space (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : IsTopologicalGroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J))
  have hcl : IsClosed (HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J : Set (GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  have hc : Continuous fun h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J => (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hopen : IsOpen (stabGrp F σ J (L : Set (Fin M → E)) : Set (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J)) := by
    have hn := congr_mem_nhds F E M L hfg hsp 1 one_pos
    have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds hn
    have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
      (by rw [Function.comp_apply, inv_one]; exact hn)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro k ⟨hk1, hk2⟩ y
    constructor
    · intro hy
      obtain ⟨w, hw, h⟩ := hk1 y hy
      rw [eq_add_of_sub_eq h]
      exact add_mem (nsmul_mem hw 1) hy
    · intro hy
      obtain ⟨w, hw, h⟩ := hk2 _ hy
      have hk : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J k⁻¹).1 * (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J k).1 = 1 :=
        (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J k).inv_mul
      rw [Function.comp_apply, Matrix.mulVec_mulVec, hk, Matrix.one_mulVec] at h
      rw [eq_add_of_sub_eq h]
      exact add_mem (nsmul_mem hw 1) hy
  refine ⟨stabGrp F σ J (L : Set (Fin M → E)), fun h => Iff.rfl, hopen, ?_⟩
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries F E L hfg hsp
  let S : Set (Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))).comp
    hcl.isClosedEmbedding_subtypeVal
  have hK : IsCompact (X := HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J) _ :=
    hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) fun h hh => ?_
  have hi := (stabGrp F σ J (L : Set (Fin M → E))).inv_mem hh
  exact ⟨fun i _ j _ => hCe _ (fun y hy => (hh y).1 hy) i j,
    (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J h⁻¹).1, fun i _ j _ => hCe _ (fun y hy => (hi y).1 hy) i j, rfl⟩

end GlobalTheory.Mem.Vol.StabGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousDistribHaarCharUnits
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Filter
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeEx

theorem continuous_distribHaarChar_units (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] :
    Continuous (fun u : Rˣ => distribHaarChar R u) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hup : ∀ c : ℝ≥0, 1 < c → ∃ V ∈ 𝓝 (1 : R), ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u < c := by
    intro c hc
    have hlt : μ K < (c : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < _ := (ENNReal.mul_lt_mul_iff_left h0 ht).2 (by exact_mod_cast hc)
    obtain ⟨U, hKU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hKc hUo hKU
    refine ⟨V, hV, fun u hu => ?_⟩
    have h1 : μ (u • K) ≤ μ U := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u K] at h1
    have h3 := (ENNReal.mul_lt_mul_iff_left h0 ht).1 (h1.trans_lt hU)
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  rw [ContinuousAt, map_one, tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      exact Eventually.of_forall fun u => distribHaarChar_pos
    have hap : 0 < a := pos_iff_ne_zero.2 ha0
    obtain ⟨V, hV, h⟩ := hup a⁻¹ ((one_lt_inv₀ hap).2 ha)
    have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
      Units.continuous_coe_inv.continuousAt.eventually
        (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
    filter_upwards [e2] with u hu
    have := h _ hu
    rw [map_inv] at this
    exact (inv_lt_inv₀ distribHaarChar_pos hap).1 this
  · intro c hc
    obtain ⟨V, hV, h⟩ := hup c hc
    have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
      Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
    filter_upwards [e1] with u hu using h u hu

theorem modu_units (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [LocallyCompactSpace S] (u : Sˣ) : modu S (u : S) = distribHaarChar S u := by
  simp [modu]

theorem modu_basic : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], (∀ u : S, IsUnit u → 0 < modu S u ∧ ∀ ν : Measure S, ν.IsAddHaarMeasure → ν = modu S u • ν.map (fun z => u * z)) ∧ (∀ u w : S, IsUnit u → IsUnit w → modu S (u * w) = modu S u * modu S w) ∧ modu S 1 = 1 ∧ (IsOpenUnits S → ContinuousOn (modu S) {u | IsUnit u}) := by
  intro S _ _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    rw [modu_units]
    refine ⟨distribHaarChar_pos, fun ν hν => ?_⟩
    ext s hs
    have e : (fun z : S => (u : S) * z) ⁻¹' s = u⁻¹ • s := by
      ext z
      rw [Set.mem_inv_smul_set_iff]; rfl
    rw [Measure.smul_apply, Measure.map_apply (measurable_const_mul _) hs, e, ENNReal.smul_def,
      smul_eq_mul, distribHaarChar_mul, smul_inv_smul]
  · rintro _ _ ⟨u, rfl⟩ ⟨w, rfl⟩
    rw [← Units.val_mul, modu_units, modu_units, modu_units, map_mul]
  · rw [← Units.val_one, modu_units, map_one]
  · intro hS
    rintro _ ⟨u, rfl⟩
    have hoe : IsOpenEmbedding (Units.val : Sˣ → S) := IsOpenUnits.isOpenEmbedding_unitsVal
    refine ContinuousAt.continuousWithinAt ?_
    rw [← hoe.continuousAt_iff]
    have : modu S ∘ Units.val = fun u : Sˣ => distribHaarChar S u := funext (modu_units S)
    rw [this]
    exact (continuous_distribHaarChar_units S).continuousAt

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousUnitaryTwoStepVectorAndTranslatePair
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem continuous_pairOf_joint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (B : Matrix (Fin (M + 1)) (Fin M) E), Continuous fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × HA R σ J × (Fin 1 → Fin M → R ⊗[F] E) => pairOf R σ J B p.1 p.2.1 p.2.2 := by
  intro F E _ _ _ _ _ σ R _ _ _ _ M J B
  refine continuous_pi (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
  · exact (continuous_apply (0 : Fin 1)).comp continuous_fst
  · exact ((continuous_mat R σ J).comp (continuous_fst.comp continuous_snd)).matrix_mulVec
      (continuous_const.matrix_mulVec
        ((continuous_apply 0).comp (continuous_snd.comp continuous_snd)))

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairingStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) → ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M', IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.detSpan_conj_mul_mem_range | exact GlobalTheory.detSpan_conj_mul_mem_range | (intros; apply GlobalTheory.detSpan_conj_mul_mem_range <;> assumption)
end

