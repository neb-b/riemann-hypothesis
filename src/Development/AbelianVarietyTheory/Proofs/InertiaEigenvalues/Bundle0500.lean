module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0122
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceRankRPartEqTraceBaseChangeTriple
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TripleTrace

open GlobalTheory.BlockComplement

theorem continuous_twO (D : D7) (a : D.nd.Loc) : Continuous (D.ntw.twist₂ a) := by
  have hl := GlobalTheory.TwistedSelmerCompare.natCast_mem_maximalIdeal (l := D.nd.l a) (D.nd.O a)
  have hl0 : ((D.nd.l a : ℕ) : D.ntw.O0 (D.ntw.twOf a)) ≠ 0 := by
    intro h0
    have := congrArg ((iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) h0
    rw [map_natCast, map_zero] at this
    exact (D.nd.lPrime a).out.ne_zero (by exact_mod_cast this)
  have hp : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsPrime := Ideal.comap_isPrime _ _
  have hm : ((IsLocalRing.maximalIdeal (D.nd.O a)).comap (D.ntw.twist₂ a)).IsMaximal := hp.isMaximal fun h => by
    apply hl0
    rw [← Ideal.mem_bot, ← h, Ideal.mem_comap, map_natCast]
    exact hl
  have he := IsLocalRing.eq_maximalIdeal hm
  refine continuous_of_continuousAt_zero (D.ntw.twist₂ a) ?_
  rw [ContinuousAt, map_zero,
    (D.ntw.twistBaseCoefficientRing_isAdic _).hasBasis_nhds_zero.tendsto_iff (D.nd.O_adic a).hasBasis_nhds_zero]
  refine fun n _ => ⟨n, trivial, fun x hx => ?_⟩
  rw [← he] at hx
  exact Ideal.le_comap_pow _ n hx

theorem trace_of_block {K : Type} [Field K] {n a t : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (M' : Matrix (Fin a) (Fin a) K) (c : Fin t → K) (e : (Fin n → K) ≃ₗ[K] ((Fin a → K) × (Fin t → K)))
    (h : ∀ u, e (M.mulVec u) = (M'.mulVec (e u).1, fun j => c j * (e u).2 j)) :
    M.trace = M'.trace + ∑ j, c j := by
  have e1 : e.conj (Matrix.toLin' M) =
      LinearMap.prodMap (Matrix.toLin' M') (Matrix.toLin' (Matrix.diagonal c)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, rfl⟩ := e.surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply, h]
    refine Prod.ext rfl ?_
    funext j
    simp [Matrix.mulVec_diagonal]
  rw [← Matrix.trace_toLin'_eq, ← LinearMap.trace_conj' _ e, e1, LinearMap.trace_prodMap',
    Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq, Matrix.trace_diagonal]

theorem trace_eq : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (a : D.nd.Loc) (π : D.nd.X a) (ρ : Formalism.MainNotions.N.GE D.nd →* GL (Fin D.R.r) (D.nd.O a)) (s : D.ntw.Sig (D.ntw.twOf a)) (Sg : List (Part D.naut.CG)), GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D a π ρ → HasParamX D.nd D.naut a π Sg → GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsTriple D a s Sg → ∀ g, ((ρ g : GL (Fin D.R.r) (D.nd.O a)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)).trace = D.ntw.twist₂ a ((D.ntw.rhoS _ s g : GL (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 (D.ntw.twOf a))).trace := by
  rintro hC D i π ρ s Sg ⟨hρ, r₀, ⟨-, -, hr3⟩, e, he⟩ ⟨P, hP, -, -, -, hB4, -⟩ ⟨-, -, -, hT⟩ g
  have hι := GlobalTheory.CoeffEmbedding.continuous_iotaOQ _ _ _ D.nd D.naut i
  have hinj : Function.Injective (iotaOQ D.nd D.naut i) :=
    (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  apply hinj
  revert g
  rw [← funext_iff]
  refine AE.eq_of_continuous hC (hι.comp hρ.matrix_trace)
    (hι.comp ((continuous_twO D i).comp (D.ntw.rhoS_cont _ s).matrix_trace)) ?_
  filter_upwards [hT, ae_chiBar D.naut i, ae_epsBar D.naut i, eventually_out i,
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut (Sg ++ [muPart D.nd D.naut i]) D.naut.etaTinv),
    isoLoc_sum (A := D.naut) (twistIso D.nd D.naut Sg D.naut.etaTinv)]
    with w h1 h2 h3 h4 h5 h8 hw B σ hB hσ
  apply (D.naut.iotaQC i).injective
  have hq := normV_ne_zero w
  have h6 := D.naut.pt_loc i P π hP w (h4 hw)
  rw [← hr3 w (h4 hw) B σ hB hσ, ← hB4 w hw] at h6
  have h9 := map_trace_eq_sum _ _ _ h6
  have h10 := map_trace_eq_sum _ _ _ (h1 (h4 hw) B σ hB hσ)
  rw [D.naut.frobEig_tw _ _ h5.1, Multiset.sum_map_mul_right, Multiset.map_id', h5.2] at h9
  rw [D.naut.frobEig_tw _ _ h8.1, Multiset.sum_map_mul_right, Multiset.map_id', h8.2] at h10
  have h7 : ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) =
      sumPart D.naut ⟨1, muEta D.naut i, D.R.t⟩ w *
        ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) := by
    rw [sumPart, ← List.sum_map_mul_right, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [chiBar_succ c.1 c.2, map_mul, map_zpow₀, h2 hw B σ hB hσ, h3 hw B σ hB hσ, ← Complex.cpow_intCast,
      mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hq, ← Complex.cpow_add _ _ hq]
    congr 2
    push_cast
    ring
  have h11 := congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (trace_of_block _ _ _ e (he σ))
  have h12 : iotaO D.nd D.naut i ((r₀ σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) _).trace =
      iotaO D.nd D.naut i ((ρ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).trace +
        ∑ c : Fin D.R.t, D.naut.iotaQC i (chiBar D.naut i (c.1 + 1) σ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum] at h11
    refine Eq.trans ?_ (h11.trans ?_)
    · exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _)
    · congr 1
      exact congrArg (fun x => D.naut.iotaQC i (D.naut.iotaQ i x)) (AddMonoidHom.map_trace (toK D.nd i) _).symm
  refine Eq.trans ?_ h10.symm
  have h13 := h12.symm.trans h9
  rw [h7] at h13
  simp only [twistIso, muPart, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero, add_mul] at h13
  exact add_right_cancel h13

end GlobalTheory.TripleTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionAcrisTensorSubEventuallyLpow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.OCrCont

open Filter Topology

theorem galOCr_sub_smul_eventually {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    (r : OCr l O) (m : ℕ) :
    ∀ᶠ h in nhds (1 : GQ l), ∃ w : OCr l O, galOCr O h r - r = ((l : O) ^ m) • w := by
  induction r using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun h => ⟨0, by simp⟩
  | tmul o a =>
    filter_upwards [GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m] with h hh
    obtain ⟨c, hc⟩ := hh
    refine ⟨o ⊗ₜ c, ?_⟩
    have e1 : galOCr O h (o ⊗ₜ[ℤ_[l]] a) = o ⊗ₜ galC h a := rfl
    rw [e1, ← TensorProduct.tmul_sub, hc, TensorProduct.smul_tmul', smul_eq_mul]
    have e2 : ((l : Per.Acris l) ^ m * c) = ((l : ℤ_[l]) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e2, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, map_natCast]
  | add x y hx hy =>
    filter_upwards [hx, hy] with h ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), smul_add, ← hu, ← hv]; abel

theorem twact_sub_smul_eventually : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
    (s : G →* GQ l), Continuous s → ∀ (T : LocLat G ℚ_[l] K O),
    (∀ t ∈ T.L.T, ∀ m : ℕ, ∀ᶠ g in nhds (1 : G), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : O) ^ m) • t') →
    ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ := by
  intro l _ O K _ _ _ _ _ _ G _ _ s hs T hT β m
  have hts : Tendsto s (nhds 1) (nhds 1) := by
    simpa [map_one] using hs.tendsto (1 : G)
  induction β using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun g => ⟨0, by simp⟩
  | tmul r t =>
    filter_upwards [hts.eventually (galOCr_sub_smul_eventually r m), hT t.1 t.2 m] with g ⟨w, hw⟩ ⟨t', ht', htt⟩
    refine ⟨w ⊗ₜ T.actT g t + r ⊗ₜ ⟨t', ht'⟩, ?_⟩
    have e1 : TWact (galOCr O (s g)) T g (r ⊗ₜ[O] t) = galOCr O (s g) r ⊗ₜ T.actT g t := rfl
    have e2 : T.actT g t - t = ((l : O) ^ m) • (⟨t', ht'⟩ : ↥T.L.T) := Subtype.ext (by
      rw [Submodule.coe_sub, Submodule.coe_smul]; exact htt)
    have e3 : galOCr O (s g) r ⊗ₜ[O] T.actT g t - r ⊗ₜ[O] t
        = (galOCr O (s g) r - r) ⊗ₜ[O] T.actT g t + r ⊗ₜ[O] (T.actT g t - t) := by
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
    rw [e1, e3, hw, e2, smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add x y hx hy =>
    filter_upwards [hx, hy] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add (f := _), smul_add, ← hu, ← hv]; abel

end GlobalTheory.OCrCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem unr_of_iterate_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (h : ℕ), 0 < h →
      ∀ c : P.R.B, P.φB^[h] c = c → (∀ j < h, ev P j c ∈ Fil P 0) →
        ∃ a : ↥(MaximalUnramifiedExtension l), fr l h a = a ∧ c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a := by
  intro l _ P AI T h hh c hc hF
  obtain ⟨E, ω, hEle, hEdim, hEfix, -⟩ := _root_.GlobalTheory.PMon.UnrDeg.fixed_field_deg l h hh
  have hK0 : K0 E = E.1 := inf_eq_left.2 hEle
  have hdim : Module.finrank ℚ_[l] ↥(K0 E) = h := by rw [hK0]; exact hEdim
  have hper : Function.IsPeriodicPt (⇑P.φB) h c := hc
  have hall : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD E).Fil 0 := by
    intro j
    have hj : (⇑P.φB)^[j] c = (⇑P.φB)^[j % h] c := by
      conv_lhs => rw [← Nat.mod_add_div j h]
      rw [Function.iterate_add_apply, (hper.mul_const (j / h)).eq]
    have h1 := hF (j % h) (Nat.mod_lt _ hh)
    rw [← SetLike.mem_coe, ← P.PD_Fil _ E 0, hj]
    exact h1
  obtain ⟨a, ha⟩ := GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt l P AI T E c (by rw [hdim]; exact hc) hall
  refine ⟨⟨(a : Om l), a.2.2⟩, ?_, ?_⟩
  · exact (hEfix ⟨(a : Om l), a.2.2⟩).2 a.2.1
  · rw [ha]; rfl

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGe
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem pow_dvd_factorial_mul (l r : ℕ) (hl : 1 ≤ l) : l ^ r ∣ (l * r).factorial := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : l * (r + 1) = (l * (r + 1) - 1) + 1 := by
      have : 1 ≤ l * (r + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [h1, Nat.factorial_succ, ← h1, pow_succ, mul_comm (l ^ r) l]
    refine Nat.mul_dvd_mul (Dvd.intro (r + 1) rfl) (ih.trans (Nat.factorial_dvd_factorial ?_))
    rw [Nat.mul_succ]; omega

theorem inclS_mem_SdSet (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (x : (Wq l a)⟦X⟧) :
    inclS t K x ∈ SdSet t K e := by
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  refine ⟨fun n => ((n / e).factorial : Wq l a) * coeff n x, fun r => ?_, fun τ n => ?_⟩
  · rw [Filter.eventually_cofinite]
    refine (Set.finite_lt_nat (e * (l * r))).subset fun n hn => ?_
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_contra hlt
    apply hn
    have hle : l * r ≤ n / e := (Nat.le_div_iff_mul_le he).2 (by rw [mul_comm]; omega)
    obtain ⟨k, hk⟩ := (pow_dvd_factorial_mul l r hl1).trans (Nat.factorial_dvd_factorial hle)
    refine Dvd.dvd.mul_right ⟨(k : Wq l a), ?_⟩ _
    rw [hk]; push_cast; rfl
  · rw [inclS_apply, coeff_toAc, map_mul, map_natCast, map_mul, map_natCast]

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelIntersectionFreeOfBaseChangeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachKernel_intersection_free_of_baseChange : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → IsBaseChange W.EE ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))).subtype → FreeA W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.WachKernel.kernel_freeA | exact GlobalTheory.WachKernel.kernel_freeA | (intros; apply GlobalTheory.WachKernel.kernel_freeA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachKernelMemFrobeniusSpanAfterQPowStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachKernel_mem_frobeniusSpan_after_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∀ y ∈ (W.N T₁).comap ((W.map ι).restrictScalars (AA K LL)), ∃ k : ℕ, W.Q ^ k • y ∈ φspan W T₀ ((W.N T₁).comap ((W.map ι).restrictScalars (AA K LL))) := by
  first | exact @GlobalTheory.NL.PhiSpanKer.main | exact GlobalTheory.NL.PhiSpanKer.main | (intros; apply GlobalTheory.NL.PhiSpanKer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpansStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachSaturation_image_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  first | exact @GlobalTheory.NL.SatFree.satM_free_and_spans | exact GlobalTheory.NL.SatFree.satM_free_and_spans | (intros; apply GlobalTheory.NL.SatFree.satM_free_and_spans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassPreparationWittOfTiltFiniteField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem weierstrass_prep_not_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := by
  intro l _ a _ g hg
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l a) = Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Wq l a)) (Wq l a) := hm ▸ inferInstance
  have hg' : g.map (IsLocalRing.residue (Wq l a)) ≠ 0 := by
    intro h0
    apply hg
    apply dvd_of_map_eq_zero l a g
    ext n
    have h1 : IsLocalRing.residue (Wq l a) (coeff n g) = 0 := by
      simpa using congrArg (coeff n) h0
    rw [IsLocalRing.residue_eq_zero_iff, hm, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at h1
    simpa using h1
  obtain ⟨f, h, H⟩ := g.exists_isWeierstrassFactorization hg'
  refine ⟨f, h, H.isUnit, H.isDistinguishedAt.monic, fun i hi => ?_, ?_⟩
  · have := H.isDistinguishedAt.mem hi
    rw [hm] at this
    exact Ideal.mem_span_singleton.1 this
  · rw [H.eq_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRestrictionUnramifiedFrobeniusConjugates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem RestrScalars.fr_smul (l : ℕ) [Fact l.Prime] (m : ℕ) (a : ℚ_[l]) (x : ↥(MaximalUnramifiedExtension l)) : fr l m (a • x) = a • fr l m x := by
  show (frobUr l ^ m) (a • x) = a • (frobUr l ^ m) x
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]

theorem RestrScalars.fr_comm_pow (l : ℕ) [Fact l.Prime] (a b : ℕ) (x : ↥(MaximalUnramifiedExtension l)) : fr l a (fr l b x) = fr l b (fr l a x) := by
  show (frobUr l ^ a) ((frobUr l ^ b) x) = (frobUr l ^ b) ((frobUr l ^ a) x)
  rw [← AlgHom.mul_apply, ← AlgHom.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem weilRes_of_basis (hE : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
      E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
      (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
      (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
      (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0) : WeilRes := by
  intro l _ n _ _ K r ρ hρ
  obtain ⟨E, ω, -, -, -, hωf, hli, hsp, hdet⟩ := hE l r hρ.pos

  set v : Fin r → Om l := fun k => ((ω k : ↥(MaximalUnramifiedExtension l)) : Om l) with hvdef
  have hv : LinearIndependent ℚ_[l] v := by
    have := hli.map' ((MaximalUnramifiedExtension l).val.toLinearMap) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact this
  set S : Submodule ℚ_[l] (Om l) := Submodule.span ℚ_[l] (Set.range v)
  let bS : Module.Basis (Fin r) ℚ_[l] S := Module.Basis.span hv
  haveI : FiniteDimensional ℚ_[l] S := Module.Finite.of_basis bS
  have coe_sum : ∀ a : Fin r → ℚ_[l], (((∑ k, a k • ω k : ↥(MaximalUnramifiedExtension l))) : Om l) = ∑ k, a k • v k := by
    intro a
    simp [hvdef]
  have memS : ∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → (c : Om l) ∈ S := by
    intro c hc
    obtain ⟨a, rfl⟩ := hsp c hc
    rw [coe_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have fix : ∀ g i j k, fr l r ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k := by
    intro g i j k
    rw [map_mul, hρ.rat, hωf]

  let co : ↥(GK K) → n → n → Fin r → Fin r → ℚ_[l] := fun g i j k k' =>
    bS.repr ⟨_, memS _ (fix g i j k)⟩ k'
  have hco : ∀ g i j k, ∑ k', co g i j k k' • ω k' = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j * ω k := by
    intro g i j k
    apply Subtype.val_injective
    rw [coe_sum]
    have h := bS.sum_repr ⟨_, memS _ (fix g i j k)⟩
    have h2 := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Module.Basis.span_apply]
  let M : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ℚ_[l] := fun g =>
    Matrix.of fun x y => co g x.1 y.1 y.2 x.2

  let W : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k : Fin r => fr l m (ω k)
  let pm : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) W
  have hpdet : pm.det ≠ 0 := by
    have : pm.det = W.det ^ Fintype.card n := by
      exact (Matrix.det_kronecker (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) W).trans (by simp)
    rw [this]
    exact pow_ne_zero _ hdet
  let pU : GL (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((Matrix.isUnit_iff_isUnit_det pm).mpr (isUnit_iff_ne_zero.mpr hpdet)).unit
  have hpU : (pU : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = pm := rfl
  let D : ↥(GK K) → Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := fun g =>
    Matrix.blockDiagonal (fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
  have key : ∀ g, pm * (M g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = D g * pm := by
    intro g
    refine Matrix.ext fun x y => ?_
    obtain ⟨i, m⟩ := x
    obtain ⟨j, k⟩ := y
    simp only [pm, D, M, W, Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_ite_irrel, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Matrix.blockDiagonal_apply, Matrix.map_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_mul, ← hco g i j k, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [RestrScalars.fr_smul, Algebra.smul_def, mul_comm]
  have key' : ∀ g, (M g).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = ((pU⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix _ _ _) * D g * pm := by
    intro g
    rw [Matrix.mul_assoc, ← key g, ← Matrix.mul_assoc, ← hpU, Units.inv_mul, Matrix.one_mul]
  have hinj : Function.Injective (fun X : Matrix (n × Fin r) (n × Fin r) ℚ_[l] => X.map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) :=
    Matrix.map_injective (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).injective
  have Dmul : ∀ g h, D (g * h) = D g * D h := by
    intro g h
    simp only [D]
    rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext m
    rw [map_mul, Units.val_mul]
    exact Matrix.map_mul
  have D1 : D 1 = 1 := by
    simp only [D, map_one, Units.val_one]
    rw [← Matrix.blockDiagonal_one]
    congr 1
    funext m
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let f : ↥(GK K) →* Matrix (n × Fin r) (n × Fin r) ℚ_[l] :=
    { toFun := M
      map_one' := by
        apply hinj
        simp only
        rw [key', D1, Matrix.mul_one, ← hpU, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      map_mul' := by
        intro g h
        apply hinj
        simp only
        rw [Matrix.map_mul, key', key', key', Dmul]
        have : pm * ((pU⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix _ _ _) = 1 := by rw [← hpU, Units.mul_inv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc pm, this, Matrix.one_mul] }
  refine ⟨f.toHomUnits, pU, ?_, ?_, ?_⟩
  · intro x y
    have hc : Continuous fun g : ↥(GK K) => bS.coord x.2 ⟨_, memS _ (fix g x.1 y.1 y.2)⟩ := by
      refine (LinearMap.continuous_of_finiteDimensional (bS.coord x.2)).comp ?_
      refine Continuous.subtype_mk ?_ _
      exact (hρ.cont x.1 y.1).mul continuous_const
    simpa [f, M, co] using hc
  · intro x y
    rw [hpU]
    obtain ⟨i, m⟩ := x
    obtain ⟨j, k⟩ := y
    simp only [pm, W, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs
    · rw [RestrScalars.fr_comm_pow, hωf]
    · exact map_zero _
  · intro g
    rw [hpU]
    exact key g

theorem weilRes : WeilRes := weilRes_of_basis _root_.GlobalTheory.PMon.UnrDeg.fixed_field_deg

end GlobalTheory.PMon

end
end

