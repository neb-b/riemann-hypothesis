module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OEvBasis
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem genIdx {W : Type} [AddCommGroup W] [Module (Fv F v) W] {ι : Type} [Fintype ι] (M : AddSubgroup W)
    (b : ι → W) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ M ↔ ∃ c : ι → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (smulSub ϖ M).relIndex M = (Ideal.absNorm v.asIdeal) ^ (Fintype.card ι) := by
  classical
  let φ : (ι → v.adicCompletionIntegers F) →+ M :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have hsm : ∀ d : ι → v.adicCompletionIntegers F,
      ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
    intro d
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have key : ((smulSub ϖ M).addSubgroupOf M).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · intro hc i _
      obtain ⟨z, hz, hze⟩ := (mem_smulSub ϖ M _).1 hc
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        rw [← hsm, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine (mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      rw [hsm]
      show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]

theorem oEv_basis : ∃ β : Fin (Module.finrank F E) → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin (Module.finrank F E) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • β i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (b_fg v)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0) := by
    have hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c e =>
      have hal : IsAlgebraic ℤ e := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)
      obtain ⟨m, hm0, hI⟩ := hal.exists_integral_multiple
      have hmF : (m : Fv F v) ≠ 0 := by
        rw [← map_intCast (algebraMap F (Fv F v))]
        exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)
      have e2 : inclR (F := F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      have e3 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
        simp [inclR, TensorProduct.smul_tmul']
      have e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by
        show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)
        rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]
      rw [e1]
      exact Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_baseChange]
  refine ⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩
  · exact hli.comp _ (Fin.cast_injective _)
  · rw [show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk.symm i), ?_⟩
      exact (Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk i), ?_⟩
      exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)

end PI.OmLocU.SdB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QInertHolds
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sig_ne (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hs
  obtain ⟨-, htc, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  have hr : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h4 τ x
    rw [hs, AlgHom.id_apply] at this
    rw [starRingEnd_apply]; exact this.symm
  exact InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 hr)

theorem fix_range (h : IsCMExt F E σ) {y : E} (hy : σ y = y) : ∃ c : F, algebraMap F E c = y := by
  by_contra hne
  push Not at hne
  have li : LinearIndependent F ![(1 : E), y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hne (-(t⁻¹ * s))
      have hy' : y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [hy', eq_neg_of_add_eq_zero_right hst, smul_neg, smul_smul, Algebra.algebraMap_eq_smul_one, neg_smul]
  have hsp := li.span_eq_top_of_card_eq_finrank' (by simpa using h.2.2.1.symm)
  apply sig_ne σ h
  have hl : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hsp fun i => ?_
    fin_cases i
    · simp
    · simpa using hy
  exact AlgHom.ext fun x => LinearMap.congr_fun hl x

theorem fix_int (h : IsCMExt F E σ) (y : 𝓞 E) (hy : sigO σ y = y) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = y := by
  have hy' : σ (y : E) = y := by rw [← sigO_coe, hy]
  obtain ⟨c, hc⟩ := fix_range σ h hy'
  have hint : IsIntegral ℤ c := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := E) , hc]
    exact y.isIntegral_coe
  refine ⟨⟨c, (mem_integralClosure_iff ℤ F).2 hint⟩, RingOfIntegers.ext ?_⟩
  exact hc

theorem qInert_holds : QInert σ J ψ v := by
  intro hstd hun hp hid
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : (IE (E := E) v).IsMaximal := hp.isMaximal (IE_ne_bot v)
  letI : Field (QE (E := E) v) := Ideal.Quotient.field _
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finite_res v
  have hfr : Module.finrank (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) = 2 := by
    rw [Ideal.finrank_quotient_map (p := v.asIdeal) (K := F) (L := E)]
    exact hstd.1.2.2.1
  have hsig : ∀ x : QE (E := E) v, sigQ σ v x = x := fun x => by rw [hid]; rfl

  have hmem : ∀ x : QE (E := E) v, (∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x + x) ∧
      ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
      rw [← sigQ_mk]; exact hsig _
    have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ hstd.1 _)
    obtain ⟨a, ha⟩ := fix_int σ hstd.1 (y + sigO σ y) (by rw [map_add (f := _), hss, add_comm])
    obtain ⟨b, hb⟩ := fix_int σ hstd.1 (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
    refine ⟨⟨Ideal.Quotient.mk _ a, ?_⟩, ⟨Ideal.Quotient.mk _ b, ?_⟩⟩
    · rw [Ideal.Quotient.algebraMap_quotient_map_quotient, ha, map_add (f := _), hs]
    · rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) := Module.finite_of_finrank_pos (by omega)
  haveI : Finite (QE (E := E) v) := Module.finite_of_finite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  letI := Fintype.ofFinite (QE (E := E) v)
  have hc : Fintype.card (QE (E := E) v) = Fintype.card (𝓞 F ⧸ v.asIdeal) ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := QE (E := E) v), hfr]
  have h1 : 1 < Fintype.card (𝓞 F ⧸ v.asIdeal) := Fintype.one_lt_card
  have hle : Fintype.card (QE (E := E) v) ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := by
    by_cases h2 : (2 : QE (E := E) v) = 0
    · refine Fintype.card_le_of_injective (fun x => (hmem x).2.choose) fun x y hxy => ?_
      have hx : algebraMap _ _ (hmem x).2.choose = x * x := (hmem x).2.choose_spec
      have hy : algebraMap _ _ (hmem y).2.choose = y * y := (hmem y).2.choose_spec
      have hxy2 : (hmem x).2.choose = (hmem y).2.choose := hxy
      have hxy' : x * x = y * y := by rw [← hx, ← hy, hxy2]
      have h0 : (x - y) * (x - y) = 0 := by
        have : (x - y) * (x - y) = x * x + y * y - 2 * (x * y) := by ring
        rw [this, h2, zero_mul, sub_zero, hxy', ← two_mul, h2, zero_mul]
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h0)
    · refine Fintype.card_le_of_injective (fun x => (hmem x).1.choose) fun x y hxy => ?_
      have hx : algebraMap _ _ (hmem x).1.choose = x + x := (hmem x).1.choose_spec
      have hy : algebraMap _ _ (hmem y).1.choose = y + y := (hmem y).1.choose_spec
      have hxy2 : (hmem x).1.choose = (hmem y).1.choose := hxy
      have hxy' : x + x = y + y := by rw [← hx, ← hy, hxy2]
      rw [← two_mul, ← two_mul] at hxy'
      exact mul_left_cancel₀ h2 hxy'
  rw [hc] at hle
  nlinarith

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrPerfOfRes
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sig_nt (hcm : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  obtain ⟨-, htc, -, hst⟩ := hcm
  have hne : Nonempty (E →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := hne
  have hc := htc.isComplex (NumberField.InfinitePlace.mk φ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
  by_contra h
  push_neg at h
  apply hc
  ext x
  simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hx := hst φ x
  rw [h x] at hx
  rw [starRingEnd_apply]
  exact hx.symm

private theorem sc_of_isUnif_of_mem_integers {ϖ r : Fv F v} (hϖ : IsUnif v ϖ)
    (hr : r ∈ v.adicCompletionIntegers F) (hn : sc (E := E) v r ∉ PO (E := E) v ϖ) :
    r ≠ 0 ∧ r⁻¹ ∈ v.adicCompletionIntegers F := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hn ⟨0, Orb.oev_zero v, by simp [sc]⟩
  refine ⟨hr0, ?_⟩
  have hv0 : Valued.v r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0)]
  by_contra hlt
  push_neg at hlt
  apply hn
  have hle : Valued.v r ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    rw [WithZero.le_ofAdd_iff hv0]
    rw [← WithZero.coe_one, ← ofAdd_zero, WithZero.lt_ofAdd_iff hv0] at hlt
    omega
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    unfold IsUnif at hϖ
    simp at hϖ
  refine ⟨sc v (r * ϖ⁻¹), NormOneUnitFixedPoints.sc_mem v ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    unfold IsUnif at hϖ
    rw [hϖ]
    rw [mul_inv_le_iff₀ (zero_lt_iff.mpr (by simp)), one_mul]
    exact hle
  · rw [NormOneUnitFixedPoints.sc_mul_sc, mul_comm r, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]

theorem mem_of_theta (hcm : IsCMExt F E σ) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (θ : Fv F v ⊗[F] E)
    (hθ : θ ∈ OEv (E := E) v) (hnd : (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) ∉ PO (E := E) v ϖ)
    (z : Fv F v ⊗[F] E)
    (hz : ∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) :
    z ∈ OEv (E := E) v := by
  have hσσ := b_sig_sig σ hcm
  have htr := trace_v v σ hσσ (sig_nt σ hcm) hcm.2.2.1
  have hsθ := UnN.sigR_mem σ v hθ
  have hδ : θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ ∈ OEv (E := E) v := by
    rw [sub_eq_add_neg]
    exact Orb.oev_add v hθ (Orb.oev_neg v hsθ)
  have hfix : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ ((θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ))
      = (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) := by
    rw [map_mul, map_sub, sigR_sigR v σ hσσ θ]
    ring
  obtain ⟨r, hr, hreq⟩ := NormOneUnitFixedPoints.fix_int_sc σ v hcm (b_mul_mem v hδ hδ) hfix
  obtain ⟨hr0, hrinv⟩ := sc_of_isUnif_of_mem_integers v hϖ hr (hreq ▸ hnd)
  have ha := hz 1 (b_one_mem v)
  rw [one_mul] at ha
  have hb := hz θ hθ
  have key : (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * z
      = algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (θ * z))
        - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ * algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) := by
    rw [htr, htr, map_mul]
    ring
  have hy : (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * z ∈ OEv (E := E) v := by
    rw [key, sub_eq_add_neg]
    refine Orb.oev_add v ?_ (Orb.oev_neg v (b_mul_mem v hsθ ?_))
    · rw [← b_sc_eq]
      exact b_sc_mem v hb
    · rw [← b_sc_eq]
      exact b_sc_mem v ha
  have hz' : z = sc v r⁻¹ * ((θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * ((θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ) * z)) := by
    rw [← mul_assoc (θ - Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ θ), hreq, ← mul_assoc, NormOneUnitFixedPoints.sc_mul_sc,
      inv_mul_cancel₀ hr0, NormOneUnitFixedPoints.sc_one, one_mul]
  rw [hz']
  exact b_mul_mem v (b_sc_mem v hrinv) (b_mul_mem v hδ hy)

private theorem exists_isUnif' : ∃ ϖ : Fv F v, IsUnif v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : Fv F v), ?_⟩
  unfold IsUnif
  rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  rfl

theorem trPerf_of_res (hR : Red.ResAlg σ J ψ v) : TrPerf σ J ψ v := by
  intro hstd hun z hz
  have hcm : IsCMExt F E σ := hstd.1
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif' v
  obtain ⟨θ, hθ, hnd⟩ := NormOneUnitFixedPoints.exists_theta σ J ψ v hR hstd hun hϖ
  exact mem_of_theta σ v hcm hϖ θ hθ hnd z hz

end PI.OmLocU.SdB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitaryOrbitCounting
section
noncomputable section

namespace PI.OmLocU.UnitaryOrbitCounting

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem orbAll_of_res (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.OrbAll σ J ψ v Λ a Y :=
  PI.OmLocU.Orb.orbAll_of_norm σ J ψ v Λ a Y (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN

theorem countU_of_res' (a : ℕ) (Y : TupV (E := E) v n a) (hRes : PI.OmLocU.Red.ResAlg σ J ψ v)
    (hUN : PI.OmLocU.Orb.UnitNorm σ J ψ v Λ) : PI.OmLocU.CountU σ J ψ v Λ a Y :=
  PI.OmLocU.Red.countU_of_res σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hRes) hUN hRes a Y

end PI.OmLocU.UnitaryOrbitCounting
end
end

