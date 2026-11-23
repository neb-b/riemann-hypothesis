module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureQuotientUnitaryJVectorStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiVNeOneOfTrace
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.StdCharTotReal

section Local

variable {F : Type} [Field F] [NumberField F]

theorem trace_int_iff (a : F) : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ r : 𝓞 F, (r : F) = a * d := by
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  have hD := FractionalIdeal.dual_ne_zero ℤ ℚ h1
  have hd : (∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k) ↔
      a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual h1]
    constructor
    · intro h x hx
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
      obtain ⟨k, hk⟩ := h b
      exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩
    · intro h r
      obtain ⟨k, hk⟩ := h (algebraMap _ F r) ((FractionalIdeal.mem_one_iff _).mpr ⟨r, rfl⟩)
      exact ⟨k, by rw [Algebra.traceForm_apply] at hk; simpa using hk.symm⟩
  rw [hd, ← inv_inv (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)),
    FractionalIdeal.mem_inv_iff (inv_ne_zero hD), ← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
  constructor
  · intro h d hd
    exact (FractionalIdeal.mem_one_iff _).mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr (h d hd)

theorem integral_iff (x : F) : (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) x v ∈ v.adicCompletionIntegers F) ↔
    ∃ r : 𝓞 F, (r : F) = x := by
  constructor
  · intro h
    have hx := (GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral F _).2 h
    rwa [GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal F),
      FractionalIdeal.mem_one_iff] at hx
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem fin_conductor (χ : Af F → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y)
    (hrat : ∀ a : F, χ (algebraMap F (Af F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (-a) : ℚ) : ℂ))) (z : Af F) :
    (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ d ∈ differentIdeal ℤ (𝓞 F), ∀ v : HeightOneSpectrum (𝓞 F), (z * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := by
  have hone : ∀ a : F, χ (algebraMap F (Af F) a) = 1 ↔ ∃ k : ℤ, Algebra.trace ℚ F a = k := by
    intro a
    rw [hrat, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero, map_neg] at hn
      have : -Algebra.trace ℚ F a = (n : ℚ) := by exact_mod_cast hn
      push_cast
      linarith
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      rw [map_neg, hk]
      push_cast
      ring
  have hO : ∀ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (Af F) (r : F) v ∈ v.adicCompletionIntegers F :=
    fun r => (integral_iff _).2 ⟨r, rfl⟩
  have hint : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ t = 1 := fun t ht =>
    GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ y = 1}) (isClosed_eq hc continuous_const)
      (fun r => (hone _).2 (by simpa using (trace_int_iff (1 : F)).2 (fun d _ => ⟨d, (one_mul _).symm⟩) r)) t ht
  obtain ⟨a, s, hs, hz⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos z
  rw [one_smul] at hz
  have hmul : ∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = χ (algebraMap F (Af F) a * t) := by
    intro t ht
    rw [hz, add_mul, hadd, hint (s * t) (fun v => mul_mem (hs v) (ht v)), mul_one]
  have h1 : (∀ t : Af F, (∀ v : HeightOneSpectrum (𝓞 F), t v ∈ v.adicCompletionIntegers F) → χ (z * t) = 1) ↔
      ∀ r : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F (a * r) = k := by
    constructor
    · intro h r
      rw [← hone, map_mul, ← hmul _ (hO r)]
      exact h _ (hO r)
    · intro h t ht
      rw [hmul t ht]
      exact GlobalTheory.IntDense.mem_of_isClosed F (C := {y | χ (algebraMap F (Af F) a * y) = 1})
        (isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const)
        (fun r => by
          show χ _ = 1
          rw [← map_mul, hone]
          exact h r) t ht
  rw [h1, trace_int_iff]
  refine forall₂_congr fun d _ => ?_
  rw [← integral_iff, hz, add_mul, map_mul]
  refine forall_congr' fun v => ?_
  have h2 : (s * algebraMap F (Af F) (d : F)) v ∈ v.adicCompletionIntegers F := mul_mem (hs v) (hO d v)
  exact ⟨fun h => add_mem h h2, fun h => (add_mem_cancel_right h2).1 h⟩

theorem single_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : singleV F v y v = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem single_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    singleV F v y w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem single_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) (t : Af F) :
    singleV F v y * t = singleV F v (y * t v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change singleV F v y w * t w = singleV F v (y * t v) w
  by_cases hw : w = v
  · subst hw; rw [single_same, single_same]
  · rw [single_ne v _ hw, single_ne v _ hw, zero_mul]

theorem psiV_ne_one_of_trace {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have key := (fin_conductor (fun y => ψ (pairA F 0 y))
    (h.1.comp (Continuous.prodMk continuous_const continuous_id))
    (fun a b => by
      rw [← AddChar.map_add_eq_mul]
      exact congrArg ψ (Prod.ext (add_zero _).symm rfl))
    (fun a => by rw [GlobalTheory.StdRat.char_fin_rat ψ h, hinf]) (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹))).1
    (fun t _ => by rw [single_mul]; exact hn _) d hd v
  have h1 : (singleV F v (z * (algebraMap F (Fv F v) (d : F))⁻¹) * algebraMap F (Af F) (d : F)) v = z := by
    rw [single_mul, single_same]
    show z * (algebraMap F (Fv F v) (d : F))⁻¹ * algebraMap F (Fv F v) (d : F) = z
    rw [inv_mul_cancel_right₀ hd1]
  rw [h1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero, WithZero.exp_le_exp] at key
  omega

theorem sum_places_eq_trace [IsTotallyReal F] (x : F) :
    (((∑ w : InfinitePlace F, (w.embedding x).re : ℝ)) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun τ => τ x) _ fun τ => rfl]
  have hr : ∀ τ : F →+* ℂ, (InfinitePlace.mk τ).embedding = τ := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  push_cast
  refine Fintype.sum_bijective (fun w : InfinitePlace F => w.embedding) ⟨fun a b hab => ?_, fun τ => ⟨_, hr τ⟩⟩ _ _
    fun w => ?_
  · rw [← InfinitePlace.mk_embedding a, ← InfinitePlace.mk_embedding b]
    exact congrArg InfinitePlace.mk hab
  · have := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
    exact Complex.conj_eq_iff_re.1 (RingHom.congr_fun this x)

end Local

theorem exists_psiV_ne_one : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) → ∀ v : HeightOneSpectrum (𝓞 F), ∃ r, psiV F ψ v r ≠ 1 := by
  intro F _ _ hF ψ hψ hinf v
  refine psiV_ne_one_of_trace hψ (fun a => ?_) v
  rw [hinf, ← sum_places_eq_trace]
  refine congrArg (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
    (Finset.sum_congr rfl fun w _ => congrArg Complex.re ?_)
  rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe]
  simp

end GlobalTheory.StdCharTotReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentFrameAdaptedAndInvMem
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NRatInv

variable {D : D7}

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {j k : ℕ} (h : j ≤ k) :
    Xflag F j ≤ Xflag F k :=
  Submodule.span_mono (Set.image_mono fun i (hi : i.1 < j) => lt_of_lt_of_le hi h)

theorem xsp_eq {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F = Xflag F D.R.rS := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x; simp

theorem mem_orth_iff {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (y : (VS D).V) :
    y ∈ orth (VS D) (Xsp F) ↔ ∀ x ∈ Xsp F, (VS D).hT x y = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem inv_mem_of_map_le (n : GV D) (W : Submodule D.host.E (VS D).V) [FiniteDimensional D.host.E W]
    (h : ∀ x ∈ W, n x ∈ W) : ∀ x ∈ W, n⁻¹ x ∈ W := by
  have hle : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) ≤ W := by
    rintro _ ⟨y, hy, rfl⟩; exact h y hy
  have heq : W.map (n : (VS D).V →ₗ[D.host.E] (VS D).V) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n W)
  intro x hx
  rw [← heq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : n⁻¹ (n y) = y := n.symm_apply_apply y
  simpa [this] using hy

end GlobalTheory.NRatInv

namespace GlobalTheory.NRatInv

variable {D : D7}

theorem xflag_fd {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (j : ℕ) :
    FiniteDimensional D.host.E (Xflag F j) :=
  FiniteDimensional.span_of_finite _ (Set.toFinite _)

theorem map_xflag {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D} (hn : n ∈ NRat F) (k : ℕ) :
    ∀ x ∈ Xflag F k, n x ∈ Xflag F k := by
  intro x hx
  cases k with
  | zero =>
    have : Xflag F 0 = ⊥ := by
      show Submodule.span _ _ = ⊥
      simp
    rw [this, Submodule.mem_bot] at hx
    subst hx; simp
  | succ j =>
    have h1 := hn.2.1 j x hx
    have h2 := xflag_mono F (Nat.le_succ j) h1
    simpa using add_mem h2 hx

theorem adapt_and_inv_mem : ∀ (D : D7) (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : GV D),
    n ∈ NRat F → Adapt n F F ∧ n⁻¹ ∈ NRat F := by
  intro D T F n hn
  obtain ⟨hiso, hfl, hor⟩ := hn
  have hn' : n ∈ NRat F := ⟨hiso, hfl, hor⟩
  refine ⟨⟨hiso, ?_⟩, ?_⟩
  · intro a
    induction a using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last D.R.rS) = F.fl.z := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [hz]
      have : F.fl.z ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff]
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact F.fl.z_orth i
        | zero => simp
        | add a b _ _ ha hb => simp [ha, hb]
        | smul c a _ ha => simp [ha]
      have := hor _ this
      simpa [xsp_eq] using this
    | cast i =>
      have he : frame F (Fin.castSucc i) = F.fl.e i := by
        simp [frame, Formalism.MainNotions.S.FlagG.fvec]
      rw [he]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
      simpa using hfl i.val _ hmem
  · refine ⟨inv_mem hiso, ?_, ?_⟩
    · intro j x hx
      haveI := xflag_fd F (j + 1)
      have hy := inv_mem_of_map_le n _ (map_xflag hn' (j + 1)) x hx
      have key := hfl j _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this
    · intro x hx
      haveI := xflag_fd F D.R.rS
      have hsp : ∀ y ∈ Xsp F, n⁻¹ y ∈ Xsp F := by
        rw [xsp_eq]; exact inv_mem_of_map_le n _ (map_xflag hn' D.R.rS)
      have hspn : ∀ y ∈ Xsp F, n y ∈ Xsp F := by
        rw [xsp_eq]; exact map_xflag hn' D.R.rS
      have hy : n⁻¹ x ∈ orth (VS D) (Xsp F) := by
        rw [mem_orth_iff] at hx ⊢
        intro e he
        have h1 : n⁻¹ (n e) = e := n.symm_apply_apply e
        have h2 := (inv_mem hiso) (n e) x
        rw [h1] at h2
        rw [h2]; exact hx _ (hspn e he)
      have key := hor _ hy
      have : n (n⁻¹ x) = x := n.apply_symm_apply x
      rw [this] at key
      have := neg_mem key
      simpa using this

end GlobalTheory.NRatInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.UnitaryVolume

theorem Jm_allPos (N : ℕ) : Formalism.REAL.Jm (allPos N) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mul_conjTranspose_self {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : uMat g * (uMat g)ᴴ = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  rw [Jm_allPos, Matrix.mul_one] at h
  exact mul_eq_one_comm.1 h

theorem row_norm {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) (i : Fin N) : ∑ k, ‖uMat g i k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (mul_conjTranspose_self g) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ k, ‖uMat g i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.mul_conj' _).symm
  exact_mod_cast h2

theorem muG_univ_lt_top (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ < ⊤ := by
  have h := Formalism.REAL.ballFinite N (allPos N) N
  have e : {g : Formalism.REAL.UJ (allPos N) | Formalism.REAL.hsG g ≤ (N : ℝ)} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    change ∑ i, ∑ k, ‖uMat g i k‖ ^ 2 ≤ (N : ℝ)
    simp [row_norm]
  rwa [e] at h

theorem muG_univ_ne_zero (N : ℕ) : Formalism.REAL.muG (allPos N) Set.univ ≠ 0 :=
  (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'

theorem gauss_inv_single {n : ℕ} (g : Formalism.REAL.UJ (allPos (n + 1))) :
    gauss ((uMat g)⁻¹ *ᵥ (Pi.single 0 1 : Fin (n + 1) → ℂ)) = Real.exp (-1) := by
  rw [Matrix.inv_eq_right_inv (mul_conjTranspose_self g), gauss]
  congr 2
  rw [← row_norm g 0]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mulVec_single_one, Matrix.conjTranspose_apply]

theorem volU_succ (n : ℕ) :
    volU (n + 1) = volU n * (2 ^ (n + 1) * Real.pi ^ (n + 1) / (n.factorial : ℝ)) := by
  have h : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ' n 1]
    simp [add_comm]
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (by omega), h]
  simp only [Nat.add_sub_cancel]
  ring

theorem volU_pos (n : ℕ) : 0 < volU n := by
  unfold volU sphV
  have := Real.pi_pos
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem volume_zero (c : ℝ) (hc : IsGauge (allPos 0) c) :
    c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal = volU 0 := by
  have h1 : (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (0 ^ 2))) 1)).toReal = 1 := by
    change (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1)).toReal = 1
    have e : Metric.ball (0 : EuclideanSpace ℝ (Fin 0)) 1 = Set.univ :=
      Set.eq_univ_of_forall fun x => by rw [Subsingleton.elim x 0]; simp
    rw [e, ← (PiLp.volume_preserving_toLp (Fin 0)).measure_preimage MeasurableSet.univ.nullMeasurableSet]
    simp [volume_pi, Measure.pi_univ]
  unfold IsGauge at hc
  rw [h1] at hc
  have h2 : Filter.Tendsto (fun _ : ℝ => c * (Formalism.REAL.muG (allPos 0) Set.univ).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have e : {g : Formalism.REAL.UJ (allPos 0) | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.univ :=
      Set.eq_univ_of_forall fun g => by
        simpa [Formalism.REAL.hs] using le_of_lt hr
    rw [e]
    simp
  rw [tendsto_const_nhds_iff.1 h2]
  simp [volU, sphV]

theorem volume_unitary : ∀ (N : ℕ) (c : ℝ), IsGauge (allPos N) c →
    c * (Formalism.REAL.muG (allPos N) Set.univ).toReal = volU N := by
  intro N
  induction N with
  | zero => exact volume_zero
  | succ n ih =>
    intro c hc
    obtain ⟨c₀, hc₀, -, hu⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique (n + 1) (allPos (n + 1))
    have hcpos : 0 < c := by rw [hu c hc]; exact hc₀
    obtain ⟨c', hc'pos, hc', -⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique n (allPos n)
    have hv := ih c' hc'
    let x₀ : Fin (n + 1) → ℂ := Pi.single 0 1
    let B : Matrix (Fin (n + 1)) (Fin n) ℂ := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix id Fin.succ
    have hq : qEps (allPos (n + 1)) x₀ = sgn ℝ true := by
      simp [qEps, sgn, allPos, x₀, Fin.sum_univ_succ]
    have hx : star x₀ ᵥ* (Formalism.REAL.Jm (allPos (n + 1)) * B) = 0 := by
      rw [Jm_allPos, Matrix.one_mul]
      funext k
      simp [Matrix.vecMul, dotProduct, x₀, B, Fin.sum_univ_succ, Matrix.one_apply, (Fin.succ_ne_zero k).symm]
    have hB : Bᴴ * Formalism.REAL.Jm (allPos (n + 1)) * B = Formalism.REAL.Jm (allPos n) := by
      rw [Jm_allPos, Jm_allPos, Matrix.mul_one]
      ext a b
      simp [Matrix.mul_apply, B, Matrix.one_apply, eq_comm]
    obtain ⟨j, -, hj⟩ := GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal (n + 1) n _ _ true x₀ B rfl
      hq hx hB
    have hV : ENNReal.ofReal c' * Formalism.REAL.muG (allPos n) Set.univ = ENNReal.ofReal (volU n) := by
      rw [← hv, ENNReal.ofReal_mul hc'pos.le, ENNReal.ofReal_toReal (muG_univ_lt_top n).ne]
    have key := _root_.GlobalTheory.GaugeQuot.gauge_quotient n _ _ true x₀ B j hq hx hB hj c c' hc hc'
      (fun _ => ENNReal.ofReal (volU n)⁻¹) measurable_const (fun g => by
        rw [lintegral_const, mul_left_comm, hV, ← ENNReal.ofReal_mul (inv_pos.2 (volU_pos n)).le,
          inv_mul_cancel₀ (volU_pos n).ne', ENNReal.ofReal_one])
    have hs : sgn ℝ true = 1 := by simp [sgn]
    simp only [x₀, gauss_inv_single, lintegral_const] at key
    rw [hs, GlobalTheory.GaussMean.Sphere.gaussDens_sphere] at key
    have k2 := congrArg ENNReal.toReal key
    have hp := volU_pos n
    have hπ := Real.pi_pos
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal (inv_pos.2 hp).le,
      ENNReal.toReal_ofReal (by positivity)] at k2
    rw [volU_succ]
    have he := Real.exp_pos (-1)
    have hf : (0 : ℝ) < n.factorial := by positivity
    field_simp at k2 ⊢
    linarith

end GlobalTheory.UnitaryVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightInvariantEqSmulLeftInvariantProbability
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem right_inv_eq_smul_left_inv :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  intro G _ _ _ K μ ν _ _ hμK hνK hμ1 hμinv hνinv
  ext A hA

  have hS : MeasurableSet {p : G × G | p.1 * p.2 ∈ A} := measurable_mul hA
  have hμae : ∀ᵐ g ∂μ, g ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνae : ∀ᵐ g ∂ν, g ∈ K := by
    rw [ae_iff]
    exact hνK
  have h1 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν Set.univ * μ A := by
    rw [Measure.prod_apply hS]
    have hc : ∀ᵐ h ∂ν, μ (Prod.mk h ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = μ A := by
      filter_upwards [hνae] with h hh
      show μ ((fun g => h * g) ⁻¹' A) = μ A
      rw [← Measure.map_apply (measurable_const_mul h) hA, hμinv h hh]
    rw [lintegral_congr_ae hc, lintegral_const, mul_comm]
  have h2 : (ν.prod μ) {p : G × G | p.1 * p.2 ∈ A} = ν A := by
    rw [Measure.prod_apply_symm hS]
    have hc : ∀ᵐ g ∂μ, ν ((fun h => (h, g)) ⁻¹' {p : G × G | p.1 * p.2 ∈ A}) = ν A := by
      filter_upwards [hμae] with g hg
      show ν ((fun h => h * g) ⁻¹' A) = ν A
      rw [← Measure.map_apply (measurable_mul_const g) hA, hνinv g hg]
    rw [lintegral_congr_ae hc, lintegral_const, hμ1, mul_one]
  rw [Measure.smul_apply, smul_eq_mul, ← h1, h2]

end GlobalTheory.IwConst
end

