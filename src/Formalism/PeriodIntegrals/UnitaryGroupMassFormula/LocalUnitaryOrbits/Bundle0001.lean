module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omAt_compl_zero {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    omAt σ J ψ v T {X | gramR (Fv F v) σ J X = T}ᶜ = 0 := by
  unfold omAt
  split_ifs with hT
  · unfold omFam
    split_ifs with hf
    · have h1 := (hf.choose_spec).1 ⟨T, hT⟩
      refine measure_mono_null (fun X hX => ?_) h1
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hX
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, not_and]
      intro h; exact absurd h hX
    · simp
  · simp

theorem smul_mem_LamT {a : ℕ} (k : HA (Fv F v) σ J) (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (Y : TupV (E := E) v n a) (hY : Y ∈ LamT v Λ a) : k • Y ∈ LamT v Λ a := by
  intro i
  exact (hk (Y i)).1 (hY i)

theorem qv_pos : 0 < qv v := by
  unfold qv
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem absV_dV_pos : 0 < absV v (dV v) := by
  have hd : dV v ≠ 0 := by
    unfold dV; split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  unfold absV
  rw [dite_eq_right (by simpa using hd)]
  exact zpow_pos (qv_pos v) _

theorem omLocU_of (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  intro hS hL hSD hUn ha hP hdet
  have hG : GoodY σ J ψ v Λ a Y := ⟨hS, hL, hSD, hUn, ha, hP, hdet⟩
  obtain ⟨ϖ, hϖ⟩ := hU
  obtain ⟨hW, hH⟩ := hSd hS
  set T := gramR (Fv F v) σ J Y with hTdef
  set ω := omAt σ J ψ v T with hω
  set O := {X | ∃ k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v, X = k • Y} with hO

  have hYL : Y ∈ LamT v Λ a := hP.1
  have hsub : O ⊆ LamT v Λ a := by
    rintro X ⟨k, hk, rfl⟩; exact smul_mem_LamT σ J v Λ k hk Y hYL
  have hsup : LamT v Λ a ⊆ O ∪ {X | gramR (Fv F v) σ J X = T}ᶜ := by
    intro X hX
    by_cases hg : gramR (Fv F v) σ J X = T
    · exact Or.inl (h1 hG X hX hg)
    · exact Or.inr hg
  have hEq : ω O = ω (LamT v Λ a) := by
    apply le_antisymm (measure_mono hsub)
    calc ω (LamT v Λ a) ≤ ω (O ∪ {X | gramR (Fv F v) σ J X = T}ᶜ) := measure_mono hsup
      _ ≤ ω O + ω {X | gramR (Fv F v) σ J X = T}ᶜ := measure_union_le _ _
      _ = ω O := by rw [omAt_compl_zero σ J ψ v T, add_zero]
  show ω O = _
  rw [hEq, hω, h2 hG (hOm hS).1 ϖ hϖ, h3 hG hW ϖ hϖ, h4 hS hL hSD hUn hW, h5 hS hUn hH ϖ hϖ]
  have hq := qv_pos v
  have hd := absV_dV_pos v
  rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg hd.le _), ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  have e : absV v (dV v) ^ ((n : ℝ) * a - (a : ℝ) ^ 2 / 2) =
      absV v (dV v) ^ ((n : ℝ) * a) / absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := Real.rpow_sub hd _ _
  rw [e]
  unfold prodEta
  have : (0 : ℝ) < qv v ^ (-((a : ℤ) ^ 2)) := zpow_pos hq _
  have : (0 : ℝ) < absV v (dV v) ^ ((a : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hd _
  field_simp

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_eq_add (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let τ : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hinv) (AlgHom.ext hinv)
  have hτ : τ ≠ 1 := by
    intro h
    obtain ⟨x0, hx0⟩ := hnt
    apply hx0
    have := congrArg (fun f : E ≃ₐ[F] E => f x0) h
    simpa [τ] using this
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hfin ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair hτ.symm
    rw [← h2]
    exact Finset.card_le_univ _
  have : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hfin])
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair hτ.symm, hcard])).symm
  rw [hu, Finset.sum_pair hτ.symm]
  rfl

variable (v : HeightOneSpectrum (𝓞 F))

theorem trace_inclR (x : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      algebraMap F (Fv F v) (Algebra.trace F E x) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      (Algebra.lmul F E x).baseChange (Fv F v) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a e
    simp [inclR]
  rw [Algebra.trace_apply, e, LinearMap.trace_baseChange]
  rfl

theorem trace_v (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (hnt : ∃ x, σ x ≠ x)
    (hfin : Module.finrank F E = 2) (w : Fv F v ⊗[F] E) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w) =
      w + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w := by
  induction w using TensorProduct.inductionOn with
  | tmul c e =>
    have e1 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
      simp [inclR, TensorProduct.smul_tmul']
    have hL : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c ⊗ₜ[F] e) =
        algebraMap F (Fv F v) (Algebra.trace F E e) * c := by
      rw [e1, map_smul, trace_inclR, smul_eq_mul, mul_comm]
    rw [hL, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      ← Algebra.smul_def, TensorProduct.smul_tmul]
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rw [← TensorProduct.tmul_add, ← trace_eq_add σ hinv hnt hfin e, Algebra.algebraMap_eq_smul_one]
  | add w1 w2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _)]; abel

theorem sigR_sigR (σ : E →ₐ[F] E) (hinv : ∀ y, σ (σ y) = y) (w : Fv F v ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul c e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hinv]
  | add w1 w2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2]

theorem b_inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem b_smul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v :=
  Submodule.smul_mem (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem b_one_mem : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using b_inclR_mem (E := E) v 1

theorem b_sc_eq (c : Fv F v) : sc (E := E) v c = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := rfl

theorem b_sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  rw [b_sc_eq, Algebra.algebraMap_eq_smul_one]
  exact b_smul_mem v hc (b_one_mem v)

theorem b_mul_mem {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b, -, rfl⟩ := hb
      have := b_inclR_mem (E := E) v (a * b)
      simpa using this
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y1 y2 _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

theorem b_trace_mem {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x ∈ v.adicCompletionIntegers F := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨a, -, rfl⟩ := ha
    rw [trace_inclR]
    have hint : IsIntegral ℤ (Algebra.trace F E (a : E)) := Algebra.isIntegral_trace a.2
    exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨_, hint⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x1 x2 _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | smul c x _ h =>
    have e : c • x = (c : Fv F v) • x := rfl
    rw [e, map_smul, smul_eq_mul]
    exact (v.adicCompletionIntegers F).mul_mem _ _ c.2 h

theorem b_lat_smul {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {o : Fv F v ⊗[F] E} (ho : o ∈ OEv (E := E) v)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v (L : Set (Fin n → E))) :
    o • x ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
  unfold OEv at ho
  rw [SetLike.mem_coe] at ho
  induction ho using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨e, -, rfl⟩ := hy
    unfold latLoc at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, hl, rfl⟩ := hz
      have hel : e • l ∈ L := L.smul_mem e hl
      have eq : inclR (F := F) (Fv F v) (e : E) • ratV (F := F) (Fv F v) l =
          ratV (F := F) (Fv F v) (e • l) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, ratV]
        rw [← map_mul]
        rfl
      rw [eq]
      exact Submodule.subset_span ⟨_, hel, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add z w _ _ hz hw =>
      rw [smul_add]
      exact Submodule.add_mem _ hz hw
    | smul r z _ hz =>
      rw [smul_comm]
      exact Submodule.smul_mem _ r hz
  | zero =>
    rw [zero_smul]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [add_smul]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [smul_assoc]
    exact Submodule.smul_mem _ r hy

theorem b_sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h4⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h4, h4, star_star]

theorem b_sig_nt (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hn
  push Not at hn
  have hs : σ = AlgHom.id F E := AlgHom.ext hn
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

end Gen

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def TrPerf : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ z : Fv F v ⊗[F] E,
    (∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) →
    z ∈ OEv (E := E) v

end Steps

end PI.OmLocU.SdB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct

theorem unifEx_holds {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    UnifEx v := by
  refine ⟨PI.VolStabSW.unifV v, ?_⟩
  unfold IsUnif
  rw [PI.VolStabSW.unifV_val]
  rfl

theorem unif_spec {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : Fv F v)
    (hϖ : IsUnif v ϖ) : ϖ ≠ 0 ∧ Tendsto (fun k : ℕ => ϖ ^ k) atTop (𝓝 0) ∧
      ϖ ∈ v.adicCompletionIntegers F := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h1 : Valued.v ϖ < 1 := by
    rw [hv]
    decide
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖ϖ‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

section Sub

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem oEv_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.add_mem _ hx hy

theorem oEv_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  unfold OEv
  exact Submodule.zero_mem _

theorem oEv_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.neg_mem _ hx

def lamS (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun hx hy i => (latLoc (E := E) v Λ).add_mem (hx i) (hy i)
  zero_mem' := fun _ => (latLoc (E := E) v Λ).zero_mem
  neg_mem' := fun hx i => (latLoc (E := E) v Λ).neg_mem (hx i)

def hermOE (a : ℕ) : AddSubgroup (HermR (Fv F v) σ a) where
  carrier := {S | ∀ i j, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v}
  add_mem' := by
    intro x y hx hy i j
    exact oEv_add v (hx i j) (hy i j)
  zero_mem' := fun _ _ => oEv_zero v
  neg_mem' := by
    intro x hx i j
    exact oEv_neg v (hx i j)

def lamN (ϖ : Fv F v) (a k : ℕ) : AddSubgroup (TupV (E := E) v n a) :=
  PI.VolStabSW.smulSub (ϖ ^ (k + 1)) (lamS v Λ a)

def hN (ϖ : Fv F v) (a k : ℕ) : AddSubgroup (HermR (Fv F v) σ a) :=
  PI.VolStabSW.smulSub (ϖ ^ (k + 1)) (hermOE σ v a)

def FibU' (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) →
    (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) → (∃ fib, IsOm σ J ψ v a fib) →
    ∀ ϖ : Fv F v, IsUnif v ϖ →
    omAt σ J ψ v (gramR (Fv F v) σ J Y) (LamT v Λ a) =
      dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ)

def LamOC (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsOpen (LamT v Λ a) ∧ IsCompact (LamT v Λ a)

def HermOC (a : ℕ) : Prop :=
  IsOpen (hermOE σ v a : Set (HermR (Fv F v) σ a)) ∧ IsCompact (hermOE σ v a : Set (HermR (Fv F v) σ a))

def FibHens (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j),
    ∀ y ∈ LamT v Λ a, PI.VolStabSW.gramH (Fv F v) σ hσ J hJ y -
        PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y ∈ hN σ v ϖ a 0 →
      ∃ D : TupV (E := E) v n a →+ HermR (Fv F v) σ a,
        (∀ k, (lamN v Λ ϖ a k).map D = hN σ v ϖ a k) ∧
        ∀ k, ∀ Z ∈ lamN v Λ ϖ a 0, ∀ W ∈ lamN v Λ ϖ a k,
          PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z + W) -
            PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈ hN σ v ϖ a (k + 1)

end Sub

end PI.OmLocU
end
end

