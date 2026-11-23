module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberField
section
open NumberField IsDedekindDomain

namespace GlobalTheory

private theorem exp_neg_le_of_natAbs_log_le {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) {n : ℕ}
    (h : (WithZero.log x).natAbs ≤ n) : WithZero.exp (-(n : ℤ)) ≤ x := by
  rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
  omega

theorem exists_approx_finite_places :
    ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)),
      Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 →
      ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
        Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  intro F _ _ ι _ w hw y c hc
  classical
  have hb : ∀ i, ∃ b : F, Valued.v (algebraMap F ((w i).adicCompletion F) b - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
    intro i
    let c' : (w i).adicCompletion F := algebraMap F ((w i).adicCompletion F) c⁻¹
    have hcc : c' * algebraMap F ((w i).adicCompletion F) c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    have ho : IsOpen ((fun z => (z - y i) * c') ⁻¹'
        ((Valued.v : Valuation ((w i).adicCompletion F) (WithZero (Multiplicative ℤ))).integer : Set ((w i).adicCompletion F))) :=
      (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
    obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w i)).exists_mem_open ho ⟨y i, by
      simp only [Set.mem_preimage, sub_self, zero_mul, SetLike.mem_coe]
      exact zero_mem _⟩
    refine ⟨b, ?_⟩
    have h1 : Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') ≤ 1 :=
      (Valuation.mem_integer_iff _ _).1 hb
    calc Valued.v (algebraMap F ((w i).adicCompletion F) b - y i)
        = Valued.v ((algebraMap F ((w i).adicCompletion F) b - y i) * c') *
            Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
          rw [← map_mul, mul_assoc, hcc, mul_one]
      _ ≤ 1 * Valued.v (algebraMap F ((w i).adicCompletion F) c) := by gcongr
      _ = _ := one_mul _
  choose b hbv using hb
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 F))
    (Finset.univ : Finset ι) b
  have hd' : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (d : 𝓞 F) • b i :=
    fun i => hd i (Finset.mem_univ i)
  choose r hr using hd'
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have ht : algebraMap (𝓞 F) F d * c ≠ 0 := mul_ne_zero hd0 hc
  obtain ⟨s0, hs0⟩ := exists_forall_sub_mem_ideal (s := Finset.univ) (fun i => (w i).asIdeal)
    (fun i => (WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs)
    (fun i _ => (w i).prime) (fun i _ j _ hij h => hij (hw (HeightOneSpectrum.ext h)))
    (fun i => r i.1)
  refine ⟨algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d, fun i => ?_⟩
  have hloc : (w i).valuation F (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i) ≤
      (w i).valuation F c := by
    have e1 : algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d - b i =
        algebraMap (𝓞 F) F (s0 - r i) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hr i, Algebra.smul_def]
      field_simp
    have e2 : c = algebraMap (𝓞 F) F d * c / algebraMap (𝓞 F) F d := by
      field_simp
    have hint : (w i).intValuation (s0 - r i) ≤ WithZero.exp
        (-((WithZero.log ((w i).valuation F (algebraMap (𝓞 F) F d * c))).natAbs : ℤ)) :=
      ((w i).intValuation_le_pow_iff_mem _ _).2 (hs0 i (Finset.mem_univ i))
    have hv : (w i).valuation F (algebraMap (𝓞 F) F (s0 - r i)) ≤
        (w i).valuation F (algebraMap (𝓞 F) F d * c) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hint.trans (exp_neg_le_of_natAbs_log_le ((Valuation.ne_zero_iff _).2 ht) le_rfl)
    rw [e1]
    conv_rhs => rw [e2]
    rw [map_div₀, map_div₀, div_eq_mul_inv, div_eq_mul_inv]
    gcongr
  have e3 : ∀ x : F, Valued.v (algebraMap F ((w i).adicCompletion F) x) = (w i).valuation F x :=
    fun x => (w i).valuedAdicCompletion_eq_valuation' x
  calc Valued.v (algebraMap F ((w i).adicCompletion F)
        (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) - y i)
      = Valued.v ((algebraMap F ((w i).adicCompletion F)
          (algebraMap (𝓞 F) F s0 / algebraMap (𝓞 F) F d) -
            algebraMap F ((w i).adicCompletion F) (b i)) +
          (algebraMap F ((w i).adicCompletion F) (b i) - y i)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ ≤ _ := max_le (by rw [← map_sub, e3, e3]; exact hloc) (hbv i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInFiniteDomainTraceMem
section
open TensorProduct

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_basis_in_finite_domain_trace_mem (T C F K : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C]
    [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K]
    [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) F K),
      (∀ (i : Fin n), ∃ (c : C), (algebraMap C K : C → K) c = (b : Fin n → K) i) ∧
        ∀ (i j : Fin n), ∃ (t : T), (algebraMap T F : T → F) t =
          (Algebra.trace F K : K → F) ((b : Fin n → K) i * (b : Fin n → K) j) := by
  classical
  have hint : ∀ c : C, IsIntegral T (algebraMap C K c) := fun c =>
    (Algebra.IsIntegral.isIntegral c).map (IsScalarTower.toAlgHom T C K)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := T) (M := C)
  have hM0 : ∀ c : C,
      algebraMap C K c ∈ Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) := by
    intro c
    have hc : c ∈ Submodule.span T (s : Set C) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul t x _ hx =>
      have : algebraMap C K (t • x) = algebraMap T F t • algebraMap C K x := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply T C K, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply T F K]
      rw [this]
      exact Submodule.smul_mem _ _ hx
  let M0 : Submonoid K := MonoidHom.mrange (algebraMap C K).toMonoidHom
  have hA0 : Algebra.adjoin F (M0 : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective C z
    have ha : algebraMap C K a ∈ Algebra.adjoin F (M0 : Set K) :=
      Algebra.subset_adjoin (MonoidHom.mem_mrange.2 ⟨a, rfl⟩)
    have hd' : algebraMap C K d ∈ Algebra.adjoin F (M0 : Set K) :=
      Algebra.subset_adjoin (MonoidHom.mem_mrange.2 ⟨d, rfl⟩)
    have hinv : (algebraMap C K d)⁻¹ ∈ Algebra.adjoin F (M0 : Set K) :=
      Subalgebra.inv_mem_of_algebraic _ (x := ⟨_, hd'⟩) (hint d).tower_top.isAlgebraic
    rw [div_eq_mul_inv]
    exact Subalgebra.mul_mem _ ha hinv
  have hspan : Submodule.span F (M0 : Set K) = ⊤ := by
    have h := Algebra.adjoin_eq_span F (M0 : Set K)
    rw [Submonoid.closure_eq, hA0, Algebra.top_toSubmodule] at h
    exact h.symm
  have htop : Submodule.span F ((s.image (algebraMap C K) : Finset K) : Set K) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_le.2 fun x hx => by
      obtain ⟨c, rfl⟩ := MonoidHom.mem_mrange.1 hx
      exact hM0 c
  haveI : FiniteDimensional F K := ⟨⟨s.image (algebraMap C K), htop⟩⟩
  obtain ⟨B, hBsub, hBspan, hBli⟩ :=
    exists_linearIndependent F ((s.image (algebraMap C K) : Finset K) : Set K)
  have hBfin : B.Finite := (Finset.finite_toSet _).subset hBsub
  haveI := hBfin.fintype
  let b0 : Module.Basis B F K := Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan, htop])
  let b := b0.reindex (Fintype.equivFin B)
  have hbC : ∀ i, ∃ c : C, algebraMap C K c = b i := by
    intro i
    have hmem : b i ∈ B := by simp [b, b0]
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 (hBsub hmem)
    exact ⟨c, hc⟩
  refine ⟨Fintype.card B, b, hbC, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := hbC i
  obtain ⟨c', hc'⟩ := hbC j
  have hI : IsIntegral T (b i * b j) := by
    rw [← hc, ← hc', ← map_mul]
    exact hint _
  exact IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace hI)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstSubstitutionOfHolomorphicFamilies
section
open Filter Topology

namespace GlobalTheory

theorem countable_eq_of_differentiableOn_of_ne {g : ℕ} {U : Set ℂ} {f f' : ℂ → Fin g → ℂ}
    (hU : IsOpen U) (hc : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (hf' : DifferentiableOn ℂ f' U) (hne : ¬ Set.EqOn f f' U) :
    {w | w ∈ U ∧ f w = f' w}.Countable := by
  set T := {w | w ∈ U ∧ f w = f' w} with hT
  have key : ∀ x ∈ T, ({x} : Set ℂ) ∈ 𝓝[T] x := by
    intro x hx
    have h1 : ¬ ∃ᶠ z in 𝓝[≠] x, f z = f' z := fun h =>
      hne ((hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq
        (hf'.analyticOnNhd hU) hc hx.1 h)
    rw [Filter.not_frequently, eventually_nhdsWithin_iff] at h1
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [h1] with z hz hzT
    by_contra hzx
    exact hz hzx hzT.2
  obtain ⟨t, -, ht, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin key
  refine ht.mono fun x hx => ?_
  have := hcov hx
  simpa using this

theorem exists_const_substitution_of_holomorphic_families :
    ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  intro L D _ g act U s s' hU hc hne hs hs' h
  by_contra hcon
  push_neg at hcon
  choose w hw a ha using hcon
  have hcount : ∀ δ, {z | z ∈ U ∧ s' z (a δ) = s z (act δ (a δ))}.Countable := fun δ =>
    countable_eq_of_differentiableOn_of_ne hU hc (hs' (a δ)) (hs (act δ (a δ)))
      (fun hE => ha δ (hE (hw δ)))
  have hUc : U.Countable := by
    refine (Set.countable_iUnion hcount).mono fun z hz => ?_
    obtain ⟨δ, hδ⟩ := h z hz
    exact Set.mem_iUnion.2 ⟨δ, hz, hδ _⟩
  have hd : Dense Uᶜ := hUc.dense_compl ℝ
  obtain ⟨x, hx1, hx2⟩ := hd.inter_open_nonempty U hU hne
  exact hx2 hx1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDetNeZeroFirstCol
section
namespace GlobalTheory.FirstColumnConjugation

open Matrix

theorem exists_det_ne_zero_first_col {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ ∀ k, P k 0 = v k := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hv
  let u : Fin (n + 1) → ℂ := v - Pi.single k₀ (1 : ℂ)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    1 + replicateCol Unit u * replicateRow Unit (Pi.single k₀ (1 : ℂ))
  have hQdet : Q.det = v k₀ := by
    simp only [Q]
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [u]
  have hQcol : ∀ k, Q k k₀ = v k := by
    intro k
    simp only [Q, u]
    by_cases h : k = k₀ <;> simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, h]
  refine ⟨Q.submatrix id (Equiv.swap 0 k₀), ?_, fun k => ?_⟩
  · rw [det_permute', hQdet]
    exact mul_ne_zero (by simp) hk₀
  · simp [hQcol]

theorem exists_conj_first_col_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      Matrix.det P ≠ 0 ∧ (∀ a : Fin n, B (Fin.succ a) 0 = 0) ∧ A * P = P * B := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at h
  obtain ⟨P, hP, hPv⟩ := exists_det_ne_zero_first_col v hv.2
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hP)
  refine ⟨P, P⁻¹ * A * P, hP, fun a => ?_, ?_⟩
  · have hPe : P *ᵥ Pi.single 0 1 = v := by
      ext k
      rw [mulVec_single_one]
      exact hPv k
    have hcol : (P⁻¹ * A * P) *ᵥ Pi.single 0 1 = μ • Pi.single 0 1 := by
      rw [← mulVec_mulVec, hPe, ← mulVec_mulVec, hAv, mulVec_smul, ← hPe, mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), one_mulVec]
    have h := congrFun hcol (Fin.succ a)
    rw [mulVec_single_one] at h
    simpa [Pi.single_apply, Fin.succ_ne_zero] using h
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hu),
      Matrix.one_mul]

end GlobalTheory.FirstColumnConjugation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDotProductMulVecEqOfLinearIndependent
section
open Matrix

namespace GlobalTheory

theorem exists_dotProduct_mulVec_eq_of_linearIndependent :
    ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 →
      LinearIndependent ℚ ε → ∀ t : Fin k → ℚ,
      ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  intro r k Mq ε hM hε t
  have hU : IsUnit Mq := (Matrix.isUnit_iff_isUnit_det Mq).2 (Ne.isUnit hM)
  have hinj : Function.Injective Mq.mulVecLin := Matrix.mulVec_injective_iff_isUnit.2 hU
  have hli : LinearIndependent ℚ (fun i => Mq *ᵥ ε i) :=
    hε.map' Mq.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  let U : Matrix (Fin k) (Fin r) ℚ := Matrix.of fun i => Mq *ᵥ ε i
  have hrow : LinearIndependent ℚ U.row := hli
  have hrank : U.rank = Fintype.card (Fin k) := hrow.rank_matrix
  have htop : LinearMap.range U.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hrank
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop t
  refine ⟨x, fun i => ?_⟩
  rw [dotProduct_comm, ← hx]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinBasisCoeffsEmbeddingsEval
section
open NumberField

namespace GlobalTheory

theorem embeddings_eval_onto (L : Type) [Field L] [NumberField L] (K : Type) [Field K] [CharZero K]
    (z : (L →+* K) → K) :
    ∃ y : Fin (Module.finrank ℚ L) → K, ∀ σ : L →+* K,
      ∑ i, σ (Module.finBasis ℚ L i) * y i = z σ := by
  classical
  set b := Module.finBasis ℚ L
  let M : Matrix (L →+* K) (Fin (Module.finrank ℚ L)) K := Matrix.of fun σ i => σ (b i)

  have hD : LinearIndependent K (fun σ : L →+* K => (σ : L → K)) := by
    have h := linearIndependent_monoidHom L K
    have hinj : Function.Injective (fun σ : L →+* K => (σ.toMonoidHom : L →* K)) := by
      intro σ τ h'
      ext x
      exact DFunLike.congr_fun h' x
    exact h.comp _ hinj
  have hrow : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff] at hD ⊢
    intro g hg
    apply hD g
    have hb : ∀ i, ∑ σ, g σ * σ (b i) = 0 := by
      intro i
      have := congr_fun hg i
      simpa [M, Matrix.row, Finset.sum_apply] using this
    funext x
    rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_sum]
    have : ∀ σ : L →+* K, ∀ i, σ (b.repr x i • b i) = (b.repr x i : K) * σ (b i) := by
      intro σ i
      rw [Algebra.smul_def, map_mul]
      simp
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h2 : ∑ σ : L →+* K, g σ * ((b.repr x i : K) * σ (b i)) =
        (b.repr x i : K) * ∑ σ : L →+* K, g σ * σ (b i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [h2, hb i, mul_zero]
  have hrank : M.rank = Fintype.card (L →+* K) := hrow.rank_matrix
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]
  have hz : z ∈ LinearMap.range M.mulVecLin := by rw [htop]; trivial
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, fun σ => ?_⟩
  have := congr_fun hy σ
  simpa [M, Matrix.mulVec, dotProduct] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionCapitulationComplex
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_pow_eq_span_singleton_of_fg (E : Type) [Field E] [NumberField E]
    (I : Submodule (𝓞 E) E) (hI : I.FG) :
    ∃ n : ℕ, ∃ β : E, I ^ (n + 1) = Submodule.span (𝓞 E) {β} := by
  classical
  by_cases h0 : I = ⊥
  · exact ⟨0, 0, by simp [h0]⟩
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  have hF : F ≠ 0 := by
    intro h
    apply h0
    have := congrArg (fun G : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (G : Submodule (𝓞 E) E)) h
    simpa [F] using this
  let u := Units.mk0 F hF
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card (ClassGroup (𝓞 E)) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h1 : ClassGroup.mk E (u ^ (n + 1)) = 1 := by
    rw [map_pow, ← hn, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨β, hβ⟩ := h1
  refine ⟨n, β, ?_⟩
  rw [← hβ, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

theorem span_image_eq_span_root {E M : Type} [Field E] [Field M] (ψ : E →+* M)
    (I : Submodule (𝓞 E) E) (n : ℕ) (β : E) (hβ : I ^ (n + 1) = Submodule.span (𝓞 E) {β})
    (γ : M) (hγ : γ ^ (n + 1) = ψ β) :
    Submodule.span (𝓞 M) (ψ '' I) = Submodule.span (𝓞 M) {γ} := by
  set J := Submodule.span (𝓞 M) (ψ '' I) with hJ
  have hint : ∀ c : 𝓞 E, IsIntegral ℤ (ψ c) := fun c =>
    map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe c)
  have hle : J ≤ Submodule.span (𝓞 M) {γ} := by
    rw [hJ, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxn : x ^ (n + 1) ∈ Submodule.span (𝓞 E) {β} := hβ ▸ Submodule.pow_mem_pow I hx (n + 1)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxn
    have hc' : ψ x ^ (n + 1) = ψ c * γ ^ (n + 1) := by
      rw [hγ, ← map_pow, ← hc, ← map_mul]; rfl
    by_cases hγ0 : γ = 0
    · have : ψ x = 0 := by
        rw [hγ0] at hc'
        simpa using hc'
      rw [this]; exact Submodule.zero_mem _
    · have hi : IsIntegral ℤ (ψ x / γ) := by
        apply IsIntegral.of_pow (Nat.succ_pos n)
        rw [div_pow, hc', mul_div_assoc, div_self (pow_ne_zero _ hγ0), mul_one]
        exact hint c
      refine Submodule.mem_span_singleton.mpr ⟨⟨ψ x / γ, hi⟩, ?_⟩
      change (ψ x / γ) * γ = ψ x
      exact div_mul_cancel₀ _ hγ0
  have hpow : ∀ k : ℕ, ∀ y ∈ I ^ k, ψ y ∈ J ^ k := by
    intro k
    induction k with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy ⊢
      obtain ⟨c, rfl⟩ := hy
      exact ⟨⟨ψ c, hint c⟩, rfl⟩
    | succ k ih =>
      intro y hy
      rw [pow_succ] at hy ⊢
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Submodule.mul_mem_mul (ih a ha) (Submodule.subset_span ⟨b, hb, rfl⟩)
      · intro a b ha hb
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
  refine le_antisymm hle ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  by_cases hγ0 : γ = 0
  · rw [hγ0]; exact Submodule.zero_mem _
  have h1 : γ ^ (n + 1) ∈ J ^ (n + 1) := by
    rw [hγ]; apply hpow; rw [hβ]; exact Submodule.mem_span_singleton_self β
  have h2 : J ^ (n + 1) ≤ J * Submodule.span (𝓞 M) {γ ^ n} := by
    rw [pow_succ']
    refine mul_le_mul_right ?_ _
    rw [← Set.singleton_pow, ← Submodule.span_pow]
    exact pow_le_pow_left' hle n
  obtain ⟨z, hz, hz'⟩ := Submodule.mem_mul_span_singleton.mp (h2 h1)
  rw [pow_succ'] at hz'
  have : z = γ := mul_right_cancel₀ (pow_ne_zero n hγ0) hz'
  exact this ▸ hz

theorem exists_finite_extension_capitulation :
    ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (ι : Type) [Finite ι] (I : ι → Submodule (𝓞 E) E), (∀ τ, (I τ).FG) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ x, φ x ∈ M) ∧ ∀ τ, ∃ s : M, Submodule.span (𝓞 M) {y : M | ∃ x ∈ I τ, (y : ℂ) = φ x} = Submodule.span (𝓞 M) {s} := by
  intro E _ _ φ ι _ I hI
  choose n β hβ using fun τ => exists_pow_eq_span_singleton_of_fg E (I τ) (hI τ)
  choose γ hγ using fun τ => IsAlgClosed.exists_pow_nat_eq (φ (β τ)) (Nat.succ_pos (n τ))
  let φ' : E →ₐ[ℚ] ℂ := φ.toRatAlgHom
  let K : IntermediateField ℚ ℂ := φ'.fieldRange
  haveI hK : FiniteDimensional ℚ K :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField φ').toLinearEquiv
  haveI : Finite (Set.range γ) := Set.finite_range γ
  haveI hL : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range γ)) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨τ, rfl⟩
    apply IsIntegral.of_pow (Nat.succ_pos (n τ))
    rw [hγ]
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (β τ)).map φ'
  let M : IntermediateField ℚ ℂ := K ⊔ IntermediateField.adjoin ℚ (Set.range γ)
  have hM : ∀ x, φ x ∈ M := fun x => (le_sup_left : K ≤ M) ⟨x, rfl⟩
  refine ⟨M, IntermediateField.finiteDimensional_sup _ _, hM, fun τ => ?_⟩
  have hγM : γ τ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.subset_adjoin ℚ _ ⟨τ, rfl⟩)
  let ψ : E →+* M := φ.codRestrict M.toSubfield hM
  refine ⟨⟨γ τ, hγM⟩, ?_⟩
  rw [← span_image_eq_span_root ψ (I τ) (n τ) (β τ) (hβ τ) ⟨γ τ, hγM⟩ (Subtype.ext (hγ τ))]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext h.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory
end

