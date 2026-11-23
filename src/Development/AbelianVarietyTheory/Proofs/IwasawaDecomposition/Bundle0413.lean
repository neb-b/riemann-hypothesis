module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepPointGivenReductionsCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0409
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90USurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
public import Formalism.LocalToGlobal.Columns.RecLevelTop

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepPointGivenReductionsCosetsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepPoint_given_reductions_cosets : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (p : ChPt (R := R) sel mu u j), ∃ r' : PtAt R sel mu cst u j, r'.1.1 = p ∧ bar r' = bar r ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r' = GlobalTheory.Mem.Col2.ChEx.cqOf r := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.TwLift.exists_ptAt_bar_cq_eq | exact GlobalTheory.Mem.Col2.ChEx.TwLift.exists_ptAt_bar_cq_eq | (intros; apply GlobalTheory.Mem.Col2.ChEx.TwLift.exists_ptAt_bar_cq_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnipotentTriangularOfPeriodCoordinatesEq
section
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC cc)
open scoped Matrix

namespace GlobalTheory.PeriodUnipotent

theorem eq_of_span {E : Type} [Field E] {r : ℕ} (S : Set (Fin r → E)) (hS : Submodule.span E S = ⊤) (σ : E → ℂ)
    (Φ Φ₀ : (Fin r → E) → ℂ)
    (ha : ∀ v w, Φ (v + w) = Φ v + Φ w) (ha₀ : ∀ v w, Φ₀ (v + w) = Φ₀ v + Φ₀ w)
    (hs : ∀ (c : E) v, Φ (c • v) = σ c * Φ v) (hs₀ : ∀ (c : E) v, Φ₀ (c • v) = σ c * Φ₀ v)
    (hσ : σ 0 = 0) (h : ∀ v ∈ S, Φ v = Φ₀ v) (v : Fin r → E) : Φ v = Φ₀ v :=
  tendsto_const_nhds_iff.1 (GlobalTheory.PeriodLift.tendsto_of_span (𝓕 := (⊤ : Filter Unit)) S hS σ (fun _ => Φ) Φ₀
    (fun _ => ha) ha₀ (fun _ => hs) hs₀ hσ (fun v hv => by rw [h v hv]; exact tendsto_const_nhds) v)

theorem inv_mul_apply {r p : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hc : ∀ a : Fin r, (a : ℕ) < p → ∀ k, B k a = A k a)
    (hr : ∀ a : Fin r, ¬ (a : ℕ) < p → ∀ k, B⁻¹ a k = A⁻¹ a k) (a c : Fin r) (hac : c ≤ a) :
    (A⁻¹ * B) a c = (1 : Matrix (Fin r) (Fin r) ℂ) a c := by
  by_cases h : (c : ℕ) < p
  · rw [← Matrix.nonsing_inv_mul A (Ne.isUnit hA)]
    simp only [Matrix.mul_apply, hc c h]
  · have h' : ¬ (a : ℕ) < p := by
      have : (c : ℕ) ≤ a := hac
      omega
    rw [← Matrix.nonsing_inv_mul B (Ne.isUnit hB)]
    simp only [Matrix.mul_apply, hr a h']

theorem exists_unipotent_of_pc_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x x' : Frame X.Ψ r), x ∈ X.dom → x' ∈ X.dom → (∀ v ∈ X.Λ, ∀ τ a, GlobalTheory.GenericFrames.pc X x' v τ a = GlobalTheory.GenericFrames.pc X x v τ a) → ∃ b ∈ Bor X.Ψ r, (∀ τ i, b τ i i = 1) ∧ x' = rmul x b := by
  intro E _ _ _ r X x x' hx hx' h
  have key : ∀ (τ : X.Ψ) (a c : Fin r), c ≤ a →
      ((mat x τ)⁻¹ * mat x' τ) a c = (1 : Matrix (Fin r) (Fin r) ℂ) a c := by
    intro τ
    refine inv_mul_apply (p := X.p0) _ _ (hx τ).1 (hx' τ).1 ?_ ?_
    · intro a ha k
      have := eq_of_span (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun v => hermC τ.1 X.Gm (col (mat x' τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [GlobalTheory.GenericFrames.pc, ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [GlobalTheory.PeriodLift.hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := eq_of_span (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun v => ((mat x' τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [GlobalTheory.GenericFrames.pc, ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat x' τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
    fun τ i => ?_, funext fun τ => ?_⟩
  · change ((mat x τ)⁻¹ * mat x' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit (hx τ).1)).ne_zero (hx' τ).1
  · exact (key τ a c hca.le).trans (Matrix.one_apply_ne hca.ne')
  · exact (key τ i i le_rfl).trans (Matrix.one_apply_eq i)
  · change mat x' τ = mat x τ * ((mat x τ)⁻¹ * mat x' τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit (hx τ).1)]

end GlobalTheory.PeriodUnipotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExactOfIsAdelicPointOfFramedLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem frExact_of_isPtOf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ), (∀ P : Q, conjPrime₂ P.1 ≠ P.1) → ∀ {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}, IsPtOf hc g p → g ∈ UAd hc n ∧ FrExact q g p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Θ q hQ g p hp
  have h1 : IsPtOf hc (g * 1) p := by rwa [mul_one]
  have hres : ∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 (((1 : GL (Fin n) (AfE F E))⁻¹ : GL (Fin n) (AfE F E)).1 r j))
      (if j = r then (((1 : DiaG (E := E) (ST := ST)) P : (𝓞 E ⧸ P.1.asIdeal)ˣ) : 𝓞 E ⧸ P.1.asIdeal) else 0) := by
    intro P r j _
    rw [inv_one, Units.val_one]
    by_cases h : j = r
    · subst h
      rw [Matrix.one_apply_eq, map_one, if_pos rfl]
      simpa using hasRes_coe P.1 1
    · rw [Matrix.one_apply_ne (Ne.symm h), map_zero, if_neg h]
      simpa using hasRes_coe P.1 0
  obtain ⟨hU, hd⟩ := GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul F E hc n ST SG Q g 1 p 1 h1 ⟨DecoF.base E n ∅ ∅ ∅, isPtOf_base hc, rfl⟩
    (fun w _ => map_one _) hres
  rw [DecoSet.dia_one] at hd
  refine ⟨hU, hd, fun P => Units.ext (Matrix.ext fun i j => ?_)⟩
  rw [qdf_at_val]
  show qPi q P ((g : Matrix (Fin n) (Fin n) _) i j) = q.phi P (((qGL n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [qsp_toGLm_apply]
  exact _root_.GlobalTheory.Mem.Col2.AdFirst.qPi_eq_phi_of_adAt hc n q P (hQ P) _ _ (hp.fr P i j)

end GlobalTheory.Mem.Col2.ChEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermEqExtraTied
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ExtraTie

open Formalism.L2.Herm

theorem errX_eq {D : D7} (X : FullTiedS D) (H : ColsHermS D) (hX : X.cols = H) (e : ErrX D)
    (h1 : e.piG = (H.levelZeroCompatibility D.u₀).piG) (h2 : ∀ u, e.piT u = (H.atT u).piU)
    (h3 : ∀ u v, e.vPl u v = (H.base.vT u v).1) : e = toErrXS X := by
  subst hX
  obtain ⟨piG, piG_K, piG_norm, piT, piT_K, piT_norm, piT_cong, vPl, vPl_inj, norm_mem_place_ideal⟩ := e
  have e1 : piG = (X.levelZeroCompatibility D.u₀).piG := h1
  have e2 : piT = fun u => (X.atT u).piU := funext h2
  have e3 : vPl = fun u v => (X.base.vT u v).1 := funext fun u => funext (h3 u)
  subst e1 e2 e3
  rfl

end GlobalTheory.Mem.Col2.TC.ExtraTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvReductionMulFlagTranslationMemRowLevelGroupStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q)
      (hz : RowAd.ptE X (q : Bridge.Gf X.toD7.sp.X') ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      (((Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩)⁻¹ :
        Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
        Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
          (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _))))) ∈ ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp := by
  first | exact @GlobalTheory.Mem.R3.RowDeco.inv_redG_mul_g0Hat_mem_grp | exact GlobalTheory.Mem.R3.RowDeco.inv_redG_mul_g0Hat_mem_grp | (intros; apply GlobalTheory.Mem.R3.RowDeco.inv_redG_mul_g0Hat_mem_grp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimesNotSelfConjugateDisjointTypeTwist
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
noncomputable section

namespace GlobalTheory.Mem.PrimesAtLevel

theorem not_both_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpP : (p : R) ∈ P) (hqP : (q : R) ∈ P) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  have h1 : ((a * p + b * q : ℤ) : R) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  apply (inferInstance : P.IsPrime).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

theorem primes_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT), conjPrime₂ v.1 ≠ v.1 ∧ (∀ w ∈ (B.primes X).vGs, ¬ IsOver (v.1.under (𝓞 B.host.F)) w) ∧ (∀ P ∈ I.Q a, ¬ IsOver (v.1.under (𝓞 B.host.F)) P) ∧ Disjoint (B.primes X).vGs (I.Q a) := by
  intro B X I hI l u a v
  obtain ⟨P, hP⟩ := v
  dsimp only at hP ⊢
  have hpr := l.pr
  have hpiT : (B.primes X).piT u ∈ P.asIdeal := by
    unfold Primes.vT divs at hP
    split_ifs at hP with h
    · exact h.mem_toFinset.mp hP
    · simp at hP
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hpr.piT_norm u]
    exact P.asIdeal.mul_mem_right _ hpiT
  have hTF : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap _ _) _
    rw [Ideal.mem_comap, map_natCast]
    exact hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have h2 : B.fields.conjO ((B.primes X).piT u) ∈ P.asIdeal := by
      have h3 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := by rw [hc]; exact hpiT
      exact (mem_conjP P _).mp h3
    obtain ⟨x, y, hxy⟩ := hpr.piT_cop u
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hxy]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpiT) (P.asIdeal.mul_mem_left _ h2)
  · intro w hw hov
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      rw [IsOver] at hov
      rw [hov, Ideal.mem_comap, map_natCast] at hTF
      exact hTF
    obtain ⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i := by
      classical
      rcases Finset.mem_union.mp hw with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hgw : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have hc : B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := by
        unfold Primes.vG divs at hi
        split_ifs at hi with h
        · exact h.mem_toFinset.mp hi
        · simp at hi
      rw [← hpr.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hc
    exact not_both_mem w.asIdeal (hpr.T_prime u) (hpr.g_prime i) (hpr.T_ne_g u i) hTw hgw
  · intro Q hQ hov
    obtain ⟨v, -, hsel, hgood⟩ := I.exists_of_mem_Q hQ
    have hv : v.asIdeal = (P.under (𝓞 B.host.F)).asIdeal := by
      rw [hov, ← hsel]
      exact (hI.sel_ok v).symm
    have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem, hv]
      exact hTF
    have hd : ringChar (𝓞 B.fields.F ⧸ v.asIdeal) ∣ (B.primes X).T u := (ringChar.spec _ _).mp hTv
    rcases (Nat.dvd_prime (hpr.T_prime u)).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · apply hgood.2.2
      convert hI.T_mem u using 1
      exact h1
  · exact Finset.disjoint_right.mpr (Q_notMem_of_ok hI a)

end GlobalTheory.Mem.PrimesAtLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLevelCharacterFiniteOrderStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLevelCharacter_finiteOrder : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q), ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  intro F E K _ _ _ _ _ _ _ hc n _ Q Θ hQ hΘ P
  exact GlobalTheory.Mem.Col2.ChEx.qbLoc_chr_exp hc Θ hQ hΘ P
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRowLevelOfReductionMemLevelGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco
open GlobalTheory.Mem.R3.RowAd

theorem reindex_symm_reindex {κ : Type} [CommRing κ] {a b : ℕ} (e : Fin a ≃ Fin b) (y : GL (Fin a) κ) :
    Units.map (Matrix.reindexAlgEquiv κ κ e.symm).toMonoidHom (Units.map (Matrix.reindexAlgEquiv κ κ e).toMonoidHom y) = y := by
  apply Units.ext
  ext i j
  simp

theorem of_reindex_mem_HK {κ : Type} [CommRing κ] {a n r t m : ℕ} (h : a = n) (hn : n = r + m * t) (hra : r ≤ a)
    (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.HK n κ r (List.replicate m t)) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧ Formalism.L2.DIV.upperLeftBlock hra y = 1 := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  obtain ⟨hUT, h1⟩ := Formalism.L2.Col.mem_HK.1 hy
  have hb : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := by
    intro i j hij
    refine hUT (show Formalism.L2.Col.coarse r (List.replicate m t) j.val < Formalism.L2.Col.coarse r (List.replicate m t) i.val from ?_)
    rw [coarse_eq_blkOf hn, coarse_eq_blkOf hn]
    exact hij
  refine ⟨hb, ?_⟩
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix hra (Formalism.L2.DIV.blockTri_blkOf_le r t hb), Units.val_one]
  ext i j
  rw [Matrix.submatrix_apply, h1 _ _ i.2 j.2]
  simp [Matrix.one_apply, Fin.ext_iff]

theorem of_reindex_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : Units.map (Matrix.reindexAlgEquiv κ κ (finCongr h)).toMonoidHom y ∈ Formalism.L2.Col.blockUT n κ r [b]) :
    y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  subst h
  rw [reindex_finCongr_rfl] at hy
  intro i j hij
  refine hy (show Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val from ?_)
  rw [coarseBlockIndex_eq_twoBlock hn, coarseBlockIndex_eq_twoBlock hn]
  exact hij

theorem redG_ptE_of (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) {U : Set I.ι}
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hL : LevOf X I U L) (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X')
    (hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX)
    (hz : ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅)
    (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) :
    Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ w =
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) :=
  redAt_reindex (finCongr (rank_X' X)) L.βX hL.beta.2 _ hSt (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz) w.1


set_option maxHeartbeats 1000000 in
theorem mem_J_of_redG_mem_grp : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') (hz : RowAd.ptE X h ∈ Formalism.L2.Col.J0 X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅),
      Formalism.L2.Col.redG X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ⟨_, hz⟩ ∈
        ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp →
      h ∈ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J := by
  intro X px I U L hI hL t h hz hred
  have hβ : L.βX = 1 := hL.beta.2
  have hSt : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈ Formalism.L2.DIV.St L.βX := by
    have h1 := reindex_mem_St_one (finCongr (rank_X' X)).symm (Formalism.L2.Col.congruence_subgroup_le_stabilizer _ _ _ hz)
    have e2 : Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7)
        (finCongr (rank_X' X)).symm).toMonoidHom (ptE X h) = Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) :=
      reindex_symm_reindex _ _
    rw [hβ]
    exact e2 ▸ h1
  have hUA : Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    obtain ⟨g, hg⟩ := h.2
    rw [← hg]
    exact GlobalTheory.LevSplit.finE_mem_UA X.toD7.sp.X' g
  have hw : ∀ w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Units.map (Matrix.reindexAlgEquiv (Formalism.L2.DIV.kP w.1) (Formalism.L2.DIV.kP w.1) (finCongr (rank_X' X))).toMonoidHom
        (Formalism.L2.DIV.redFn L.βX w.1 (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) ∈
        (Formalism.L2.Col.rowTyKK I.Ch I.sel t.1 w).H := fun w => by
    rw [← redG_ptE_of X I L hL t h hSt hz w]
    exact hred w (Set.mem_univ _)
  have hG : ∀ PP ∈ (L.datXt t).Pg,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
                Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (L.datXt t).r (L.datXt t).t) ∧
        Formalism.L2.DIV.upperLeftBlock (L.datXt t).hr
          (Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _))) = 1 := by
    intro PP hPP
    have hP : PP ∈ (X.B.primes px).vGs := by
      have hP' : PP ∈ L.Pg := hPP
      rw [hL.Pg] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_left _ hP⟩
    rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
    exact of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm
  have hQ : ∀ PP ∈ (L.datXt t).Q,
      Formalism.L2.DIV.redFn L.βX PP (Formalism.UG.bc (swapAE X.toD7) ((h : Bridge.Gf X.toD7.sp.X') : GL _ _)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (L.datXt t).r) := by
    intro PP hPP
    have hq : PP ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
      have hP' : PP ∈ L.Q t := hPP
      have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr _ _ _) := by
        simp only [ColIn.Q, tup_ixOf]
      rw [hL.Q t, e] at hP'
      exact hP'
    have hm := hw ⟨PP, by classical exact Finset.mem_union_right _ hq⟩
    by_cases hP : PP ∈ (X.B.primes px).vGs
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ hP] at hm
      exact Formalism.L2.DIV.blockTri_blkOf_le _ _
        (of_reindex_mem_HK (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) (L.datXt t).hr _ hm).1
    · rw [Formalism.L2.Col.rowTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ _ hP] at hm
      exact of_reindex_mem_HQ (rank_X' X) (Formalism.L2.Col.rank_X'_eq X.B.R) _ hm
  exact ⟨Formalism.L2.DIV.mem_parLev.2 ⟨hUA, hSt, fun PP hP => (hG PP hP).1, hQ⟩,
    Subgroup.mem_bot.2 (funext fun PP => (hG PP.1 PP.2).2)⟩

end GlobalTheory.Mem.R3.RowDeco
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

namespace GlobalTheory.Mem.Col2.FullDt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def detU : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* U1 (host_cmData R H).sig :=
  (Matrix.GeneralLinearGroup.det.comp (Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)).subtype).codRestrict _ fun x =>
    Units.ext (DetLift.det_mul_conj_det _ _ x.2)

def u1Dt (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) →* DtQ H SQ :=
  (normOneIdeleToFinerDeterminantClass H SQ (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
    (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).comp (detU H)

theorem normOneFiniteAdeleDetClass_of_isDetLift (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) (a : GlobalTheory.Mem.Chr.Ideles H.E)
    (ha : IsDetLift (host_cmData R H) x.1 a) : u1Dt H SQ x = QuotientGroup.mk a := by
  have e : detU H x = ⟨h90 (host_cmData R H).sig (finAf H.F H.E a), by
      rw [ha]; exact (detU H x).2⟩ := Subtype.ext ha.symm
  show normOneIdeleToFinerDeterminantClass H SQ _ _ _ _ _ (detU H x) = _
  rw [e]
  exact normOneIdeleToFinerDeterminantClass_eq_mk H SQ _ _ _ _ _ _ _ _ (afIso_finAf H.F H.E a).symm

theorem exists_lift (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)) : ∃ a : GlobalTheory.Mem.Chr.Ideles H.E, IsDetLift (host_cmData R H) x.1 a :=
  DetLift.exists_isDetLift R H 1 x.1 x.2

theorem exists_of_idele (a : GlobalTheory.Mem.Chr.Ideles H.E) : ∃ x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H), IsDetLift (host_cmData R H) x.1 a := by
  have hu : h90 (host_cmData R H).sig (finAf H.F H.E a) ∈ U1 (host_cmData R H).sig :=
    (DetClass.exists_detClass R H (host_cmData R H).sig (fun x => bridge_star_holds R H x) (afIso H.F H.E)
      (afIso_tmul_one H.F H.E) (mem_rInt_iff H.F H.E)).1.le ⟨_, rfl⟩
  refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 1) (h90 (host_cmData R H).sig (finAf H.F H.E a)), ?_⟩, ?_⟩
  · show Formalism.UG.cT _ _ * _ * _ = _
    have hz := congrArg Units.val (show (h90 (host_cmData R H).sig (finAf H.F H.E a)) * conjId (host_cmData R H).sig (h90 (host_cmData R H).sig (finAf H.F H.E a)) = 1 from hu)
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Formalism.UG.cT, Matrix.mul_apply]
    exact (mul_comm _ _).trans hz
  · exact Units.ext (by simp)

theorem normOneFiniteAdeleDetClass_surjective (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) : Function.Surjective (u1Dt H SQ) := fun t => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, hx⟩ := exists_of_idele H a
  exact ⟨x, normOneFiniteAdeleDetClass_of_isDetLift H SQ x a hx⟩

end GlobalTheory.Mem.Col2.FullDt

end
end

