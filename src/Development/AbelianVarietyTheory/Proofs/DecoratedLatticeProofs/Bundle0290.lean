module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.VacRead

variable {D : D7}

theorem eq_of_comp {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (w w' : Mx D m n)
    (hw : w.map (finPart D) = 0) (hw' : w'.map (finPart D) = 0) (h : ∀ τ, compAt θ τ w = compAt θ τ w') : w = w' := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have e1 : finPart D (w i j) = 0 := congrFun (congrFun hw i) j
    have e2 : finPart D (w' i j) = 0 := congrFun (congrFun hw' i) j
    rw [RingHom.map_sub, e1, e2, sub_zero]
  · have e : θ τ (infPart D (w i j)) = θ τ (infPart D (w' i j)) := congrFun (congrFun (h τ) i) j
    rw [RingHom.map_sub, RingHom.map_sub, e, sub_self]

theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (w : Mx D m n)
    (hw : w.map (finPart D) = 0) (hz : ∀ τ, compAt θ τ w = z τ) : realPt θ z = w := by
  have hs : (realPt θ z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (realPt θ z) = z τ := by
    unfold realPt
    exact Classical.epsilon_spec (p := fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ) ⟨w, hw, hz⟩
  exact eq_of_comp hθ _ _ hs.1 hw fun τ => (hs.2 τ).trans (hz τ).symm

theorem hAt_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.VacUnique.hAt S T τ x y = ∑ i, ∑ j, x i j * starRingEnd ℂ (y i j) := by
  have h1 : gramAt D S τ = 1 := by
    unfold gramAt; rw [hS]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : gramAt D T τ = 1 := by
    unfold gramAt; rw [hT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  unfold GlobalTheory.VacUnique.hAt
  rw [h1, h2, inv_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}

theorem xiN_eq_zero (θ : InfFam D) (hθ : IsInfFam θ) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (δ : ℂ) (sc : ℝ) (hδ : δ ≠ 0) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (h0 : xiN θ S T hS hT δ sc f = 0) : f = 0 := by
  subst hS hT
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hf fun w hw => ?_
  have h1 := congrFun h0 (fun τ i j => -(δ * compAt θ τ w i j))
  have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * (fun τ i j => -(δ * compAt θ τ w i j) :
      VCx D.what₂.Tau S.rank T.rank) τ (Fin.cast rfl i) (Fin.cast rfl j))) = w := by
    refine realPt_eq hθ _ w hw fun τ => ?_
    funext i j
    simp only [Matrix.of_apply, Fin.cast_eq_self]
    field_simp
  unfold xiN at h1
  rw [hp, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Complex.exp_ne_zero _)

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem key_sum {ι : Type} [Fintype ι] (r0 k : ℝ) (s : ι → ℂ) :
    ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * s τ).re : ℝ) : ℂ) +
      Complex.I * ((∑ τ, 2 * (Complex.I * (r0 : ℂ) * (k : ℂ) * (-Complex.I * s τ)).re : ℝ) : ℂ) =
      2 * Complex.I * ((r0 * k : ℝ) : ℂ) * ∑ τ, s τ := by
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem scale_eq (x y sc : ℝ) (hy : y ≠ 0) (h : sc * y = 2 * x) : x * y⁻¹ = sc / 2 := by
  field_simp
  linarith

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead
variable {D : D7}
open GlobalTheory.FockCompare

theorem xiN_differentiable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (δ : ℂ) (sc : ℝ) (ψ : AddChar (AF D.host.F) ℂ) (hP : StdPair θ S T δ sc ψ) (f : WO S T → ℂ)
    (hf : IsHol θ S T ψ f) : Differentiable ℂ (xiN θ S T hS hT δ sc f) := by
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hP.std S T (fun _ => 1) (fun _ => 1) f
    hf.1 hf.2
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set r : ℝ := sc / 2 with hr
  let L : RW T S →L[ℂ] RW T S := (-δ⁻¹) • ContinuousLinearMap.id ℂ (RW T S)
  have hL : ∀ Z τ i j, L Z τ i j = -(δ⁻¹ * Z τ i j) := fun Z τ i j => by simp [L]
  set E : RW T S → ℂ := fun Z => Complex.exp ((Real.pi * r * ∑ τ, ∑ i, ∑ j, ‖Z τ i j‖ ^ 2 : ℝ) : ℂ) with hE
  have hxi : xiN θ S T rfl rfl δ sc f = fun Z => F (L Z) * E Z := by
    funext Z
    unfold xiN
    have hp : realPt θ (fun τ => Matrix.of fun i j => -(δ⁻¹ * Z τ (Fin.cast rfl i) (Fin.cast rfl j))) =
        iotaW σ T S (L Z) := by
      refine realPt_eq hP.inf _ _ (by funext i j; exact hσ.fin _) fun τ => ?_
      funext i j
      show θ τ (infPart D (σ fun τ' => L Z τ' i j)) = _
      rw [hσ.comp]
      simp [hL]
    rw [hp, mul_comm]
    congr 2
    show (Real.pi : ℂ) / 2 * ((sc : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j)) = _
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hr]; push_cast; ring
  rw [hxi]
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (L Z)) Z Y = fderiv ℝ F (L Z) (L Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (L Z)) ((fderiv ℝ F (L Z)).comp (L.restrictScalars ℝ)) Z :=
      (hF (L Z)).hasFDerivAt.comp Z (L.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]; rfl
  refine GlobalTheory.FockPos.differentiable_mul_of_cr (fun Z => F (L Z)) E
    (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ))
    (hF.comp (L.restrictScalars ℝ).differentiable) (GlobalTheory.FockPos.gauss_cr r).1 (fun Z Y => ?_)
    (GlobalTheory.FockPos.gauss_cr r).2
  rw [hdG, hdG]
  have hj : GlobalTheory.VacUnique.jO S T (fun _ => 1) (fun _ => 1) (L Y) = L (Complex.I • Y) := by
    rw [L.map_smul]; funext τ; rw [GlobalTheory.VacUnique.jO_apply]
    change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (L Y τ) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
    rw [Matrix.one_mul, Matrix.mul_one]; rfl
  have h := hann (L Z) (L Y)
  rw [hj] at h
  have hdd : δ⁻¹ * starRingEnd ℂ δ⁻¹ = (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_inv, Complex.normSq_eq_norm_sq]
  have hom : ∀ Y' : RW T S, GlobalTheory.VacUnique.omO S T (L Z) (L Y') =
      ∑ τ, 2 * (Complex.I * (((Real.sqrt D.host.d)⁻¹ : ℝ) : ℂ) * (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j)).re := by
    intro Y'
    rw [GlobalTheory.VacUnique.omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show 2 * (tauE D τ D.host.xi0 * GlobalTheory.VacUnique.hAt S T τ (L Z τ) (L Y' τ)).re = _
    rw [hP.xi τ]
    erw [hAt_one S T hP.gS hP.gT τ (L Z τ) (L Y' τ)]
    have hs : ∑ i, ∑ j, L Z τ i j * starRingEnd ℂ (L Y' τ i j) =
        (((‖δ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y' τ i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hL, hL, ← hdd]
      simp only [map_neg, map_mul]
      ring
    rw [hs]
    congr 2
    ring
  rw [hom, hom] at h
  have hs2 : ∀ τ, (∑ i, ∑ j, Z τ i j * starRingEnd ℂ ((Complex.I • Y) τ i j)) =
      -Complex.I * ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) := fun τ => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hs2] at h
  have key := key_sum ((Real.sqrt D.host.d)⁻¹) ((‖δ‖ ^ 2)⁻¹) fun τ => ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)
  have hrk : (Real.sqrt D.host.d)⁻¹ * (‖δ‖ ^ 2)⁻¹ = r :=
    scale_eq _ _ _ (pow_ne_zero 2 (norm_ne_zero_iff.2 hP.ne)) hP.scale
  rw [hrk] at key
  show _ = -((2 * Real.pi * r * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j) : ℂ) * F (L Z))
  linear_combination h + Real.pi * Complex.I * F (L Z) * key +
    2 * Real.pi * r * (∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Y τ i j)) * F (L Z) * Complex.I_sq

end GlobalTheory.AdForm.VacRead

namespace GlobalTheory.AdForm.VacRead

theorem xiN_entire_and_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ)
    (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ →
    (∀ f, IsHol θ S T ψ f → Differentiable ℂ (xiN θ S T hS hT δ sc f)) ∧
      ∀ f, IsThetaFunO ψ S T f → xiN θ S T hS hT δ sc f = 0 → f = 0 := by
  intro D ψ θ S T a b hS hT δ sc hP
  exact ⟨fun f hf => xiN_differentiable θ S T hS hT δ sc ψ hP f hf,
    fun f hf h0 => xiN_eq_zero θ hP.inf S T hS hT δ sc hP.ne ψ f hf h0⟩

end GlobalTheory.AdForm.VacRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSep

theorem map_infPart_eq_zero {D : D7} {S T : HSp D} {b : AE D} (hb : infPart D b = 0) {y : WO S T}
    (hy : IsHalf b y) : y.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hy i j, map_mul, hb, zero_mul]

theorem sep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ f₀ Φ f : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → ∀ g : GA D S, (∀ x, Φ x ≠ 0 → Φ (actO S T g 1 x) = 0) → ∃ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0 ∧ (actO S T g⁻¹ 1 (-(y i))).map (infPart D) = 0) ∧ ∑ i, a i • heisO ψ S T (y i) f = f ∧ ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) f = 0 := by
  classical
  intro D ψ S T hψ ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth g hsupp
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hfT : f = Tm Φ := hall Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinfc : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  obtain ⟨k, hk, hinv, hsup⟩ := hΦ.2
  obtain ⟨M, hM, hMact⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g 1
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  set N : ℕ := M * k with hN
  have hNpos : 0 < N := Nat.mul_pos hM hk
  let Ψ : WO S T → ℂ := fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0
  have hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ := fun t ht => by
    rw [hN, mul_smul]; exact Λ.nsmul_mem (hsup t ht) M
  have hΨ : IsSBHalf e Λ Ψ := by
    refine ⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact GlobalTheory.ThetaOrth.isHalf_nsmul (hΦ.1 t ht) N
    · have key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        constructor
        · rintro ⟨t, ht, h⟩
          refine ⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (GlobalTheory.ThetaOrth.isHalf_neg hvh) t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_neg N k t u v h
        · rintro ⟨t, ht, rfl⟩
          refine ⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_mul N k t v
      show (if _ then _ else _) = (if _ then _ else _)
      simp only [key]
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact Λ.nsmul_mem (hNt t ht) _
  have hspan := (GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT e ho.idem he.2 ho.infPart_eq).2 Ψ hΨ
  obtain ⟨q, hq, hqΨ⟩ := GlobalTheory.ThetaOrth.exists_char_of_wave N hspan
  have hq1 : ∀ t, Φ t ≠ 0 → q t = 1 := fun t ht => by
    rw [← hqΨ t (hΦ.1 t ht) (hNt t ht)]
    exact if_pos ⟨t, ht, rfl⟩
  have hq0 : ∀ t, Φ t ≠ 0 → q (actO S T g 1 t) = 0 := fun t ht => by
    have h1 : N • actO S T g 1 t ∈ Λ := by
      have := hMact (k • t) (hsup t ht)
      have e : actO S T g 1 (k • t) = k • actO S T g 1 t := map_nsmul (GlobalTheory.LatLevel.actHom S T g 1) k t
      rwa [e, ← mul_smul] at this
    rw [← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]
    refine if_neg ?_
    rintro ⟨t', ht', h⟩
    have : t' = actO S T g 1 t := GlobalTheory.ThetaOrth.nsmul_inj hNpos h
    exact ht' (this ▸ hsupp t ht)

  obtain ⟨n, a, yy, hqs⟩ := (Submodule.mem_span_set' (R := ℂ)).1 hq
  choose y hy hyq using fun i => (yy i).2
  have hqt : ∀ t, q t = ∑ i, a i * ψ (symplO S T t (y i)) := fun t => by
    rw [← hqs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hyq i, smul_eq_mul]
  set w : Fin n → WO S T := fun i => actO S T g⁻¹ 1 (-(y i)) with hw
  have hwh : ∀ i, IsHalf (cA D e) (w i) := fun i =>
    GlobalTheory.SplitHecke.isHalf_actO _ _ (GlobalTheory.ThetaOrth.isHalf_neg (hy i))
  have hact : ∀ i, actO S T g 1 (w i) = -(y i) := fun i => by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
    rwa [inv_one] at this
  refine ⟨n, a, y, fun i => ⟨map_infPart_eq_zero hinfc (hy i), map_infPart_eq_zero hinfc (hwh i)⟩, ?_, ?_⟩
  · have e1 : (fun t => q t * Φ t) = Φ := by
      funext t
      by_cases h : Φ t = 0
      · rw [h, mul_zero]
      · rw [hq1 t h, one_mul]
    have e2 : (fun t => q t * Φ t) = ∑ i, a i • fun t => ψ (symplO S T t (y i)) * Φ t := by
      funext t
      rw [hqt, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    have e3 := congrArg Tm e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum, ← hfT] at e3
    refine (Finset.sum_congr rfl fun i _ => ?_).trans e3.symm
    rw [map_smul, hTm.modul Φ hΦ (y i) (hy i), ← hfT]
  · have e1 : (fun t => conj (q (actO S T g 1 t)) * Φ t) = 0 := by
      funext t
      by_cases h : Φ t = 0
      · simp [h]
      · simp [hq0 t h]
    have e2 : (fun t => conj (q (actO S T g 1 t)) * Φ t) =
        ∑ i, conj (a i) • fun t => ψ (symplO S T t (w i)) * Φ t := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hqt, map_sum, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.ThetaOrth.conj_psi hψ,
        ← GlobalTheory.ThetaOrth.symplO_neg_right, ← hact i, GlobalTheory.SymplOInv.symplO_actO D S T g 1 t (w i), mul_assoc]
    have e3 := congrArg Tm e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_zero, map_sum] at e3
    rw [e3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hfT, hTm.modul Φ hΦ (w i) (hwh i)]

end GlobalTheory.HalfSep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionMovesByTranslatePair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatPairMove

variable {D : D7}

def finGL (V : HSp D) (g : GA D V) : GL (Fin V.rank) (EAf D) where
  val := (mt V g).map (toEAf D)
  inv := (mt V g⁻¹).map (toEAf D)
  val_inv := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  inv_val := by
    rw [← Matrix.map_mul, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mul (V : HSp D) (g h : GA D V) :
    (finGL V (g * h)).val = (mt V g).map (toEAf D) * (finGL V h).val := by
  change (mt V (g * h)).map (toEAf D) = _
  rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.map_mul]
  rfl

theorem latFr_rfl (V : HSp D) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    GlobalTheory.AdForm.latFr V rfl N = (N : Set (Fin V.rank → D.host.E)) := by
  ext x
  exact Iff.rfl

theorem eq_lat_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hN : Moves V rfl g N) : N = GlobalTheory.NormSum.AdLattice.lat (finGL V g) := by
  ext x
  rw [GlobalTheory.NormSum.AdLattice.mem_lat, hN x]
  rfl

theorem latO_move : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (g s : GA D S) (h s' : GA D T) N N' N₁ N₁', Moves S hS g N → Moves T hT h N' → Moves S hS (s * g) N₁ → Moves T hT (s' * h) N₁' → ∀ u : WO S T, u ∈ (latO S T (latFr S hS N₁) (latFr T hT N₁') fun _ => True) ↔ ∃ u₀ ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), u = actO S T s s' u₀ := by
  intro D S T a b hS hT g s h s' N N' N₁ N₁' hN hN' hN₁ hN₁' u
  subst hS hT
  rw [latFr_rfl, latFr_rfl, latFr_rfl, latFr_rfl]
  obtain rfl := eq_lat_of_moves S g N hN
  obtain rfl := eq_lat_of_moves T h N' hN'
  obtain rfl := eq_lat_of_moves S (s * g) N₁ hN₁
  obtain rfl := eq_lat_of_moves T (s' * h) N₁' hN₁'
  exact GlobalTheory.AdelicLatMove.mem_latO_iff_exists_actO D S T s s' _ _ _ _ (finGL S g) (finGL S (s * g)) (finGL T h)
    (finGL T (s' * h)) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.StdFrames.isFrame_lat _)
    (GlobalTheory.StdFrames.isFrame_lat _) (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice
    (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (GlobalTheory.NormSum.AdLattice.lat_isLattice _).toIsLattice (finGL_mul S s g)
    (finGL_mul T s' h) u

end GlobalTheory.LatPairMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InterEqSumReps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

theorem reps_bijective {V : Type} [AddCommGroup V] (A₁ A₂ : AddSubgroup V) {ι : Type} (s : Finset ι) (z : ι → V)
    (hz : ∀ i ∈ s, z i ∈ A₂) (hinj : ∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j)
    (hsurj : ∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) :
    Function.Bijective (fun i : s => ((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) := by
  constructor
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only at h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have : z j - z i ∈ A₁ := by simpa [neg_add_eq_sub] using h
    exact Subtype.ext (hinj j hj i hi this).symm
  · intro c
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨i, hi, hyi⟩ := hsurj y hy
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hyi

theorem inter_eq_sum_reps : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ)
    (A₁ A₂ : AddSubgroup V), Formalism.L2.Th1.H.IsHerm H → Formalism.L2.Th1.H.IsSelfDual H A₂ →
    Formalism.L2.Th1.H.IsSemiChar H A₁ α → Formalism.L2.Th1.H.IsSemiChar H A₂ α → ∀ {ι : Type} (s : Finset ι) (z : ι → V),
    (∀ i ∈ s, z i ∈ A₂) → (∀ i ∈ s, ∀ j ∈ s, z i - z j ∈ A₁ → i = j) → (∀ y ∈ A₂, ∃ i ∈ s, y - z i ∈ A₁) →
    ∀ F ∈ Formalism.L2.Th1.H.fixedBy H α A₁, ∀ w, Formalism.L2.Th1.H.inter H α A₁ A₂ F w =
      ((Real.sqrt (s.card : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i ∈ s, α (z i) * Formalism.L2.Th1.H.opU H (z i) F w := by
  intro V _ _ H α A₁ A₂ hH hd₂ hs₁ hs₂ ι s z hz hinj hsurj F hF w
  classical
  have hφ := reps_bijective A₁ A₂ s z hz hinj hsurj
  have : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := Finite.of_surjective _ hφ.2
  have := Fintype.ofFinite (A₂ ⧸ A₁.addSubgroupOf A₂)
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = s.card := by
    rw [← Fintype.card_of_bijective hφ, Fintype.card_coe]
  have hinv : ∀ (a : A₂), ∀ t ∈ A₁.addSubgroupOf A₂,
      α ((a + t : A₂) : V) * opU H ((a + t : A₂) : V) F w = α (a : V) * opU H (a : V) F w := by
    intro a t ht
    rw [AddSubgroup.coe_add, alpha_opU_add hH hd₂ hs₂ a.2 t.2,
      opU_of_fixed hs₁ hF (AddSubgroup.mem_addSubgroupOf.1 ht), opU_mul, ← mul_assoc (α t), alpha_sq hs₂ t.2, one_mul]
  rw [congrFun (inter_eq (H := H) (α := α) A₁ A₂ F) w, hcard]
  congr 1
  rw [← Finset.sum_coe_sort s]
  refine (Fintype.sum_bijective _ hφ _ _ fun i => ?_).symm
  have ht : -(⟨z i, hz i i.2⟩ : A₂) + Quotient.out (((⟨z i, hz i i.2⟩ : A₂) : A₂ ⧸ A₁.addSubgroupOf A₂)) ∈
      A₁.addSubgroupOf A₂ := by
    rw [← QuotientAddGroup.eq]
    exact (QuotientAddGroup.out_eq' _).symm
  have := hinv ⟨z i, hz i i.2⟩ _ ht
  rw [add_neg_cancel_left] at this
  exact this.symm

end GlobalTheory.ThetaInter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.LastStep

theorem chars_unram : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  intro D c v k _ _ _ _ ι o hS j h t hU hK χz χS' χT h1 h2 x hx
  obtain ⟨i, rfl⟩ := (hS.pre.tP x).1 hx
  have hpos : ∀ n, 0 < (c.X n).rank := fun n => by
    apply Nat.pos_of_ne_zero
    intro h0
    have P := o.Q n i
    revert P
    rw [h0]
    intro P
    exact P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hV : 0 < (c.V (j + 1)).rank := by
    have := (c.jac j 0 h).d.rank_add
    have := hpos (j + 1)
    omega
  obtain ⟨χS₃, χT₃, hW₃, hu₃⟩ := hK (j + 1) (by omega)
  obtain ⟨χS₂, χT₂, hW₂, hu₂⟩ := hU.top j h
  refine ⟨?_, ?_⟩
  · exact (_root_.GlobalTheory.CharsFromWeil.charUnram_of_weil D k (o.p i) c.ψ _ _ χS₃ χT₃ χS' (χT * χz⁻¹) (t.kom (j + 1)) hW₃ h1).2 (hpos _) (hu₃ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).1
  · exact (_root_.GlobalTheory.CharsFromWeil.charUnram_of_weil D k (o.p i) c.ψ _ _ χS₂ χT₂ χS' χT (t.omT j h) hW₂ h2).1 hV (hu₂ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).2

end GlobalTheory.LastStep
end

