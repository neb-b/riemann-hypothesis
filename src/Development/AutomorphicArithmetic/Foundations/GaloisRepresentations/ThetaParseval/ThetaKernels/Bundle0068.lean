module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinBase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0055
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0056
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.PolyKFinOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0044
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0058
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0045
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem cw_eInf_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (eInf F • Z) = d.cw w Z := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, St.piInf_smul, eInf_fst_apply, map_one, one_mul]
theorem cw_finOne_k (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) : d.cw w (finOne F • Z) = 0 := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.smul_apply, Place.piInf_finOne, Matrix.zero_apply]
theorem cw_zero_iff_k {p q : Type} (Z : Matrix p q (AE F E)) : (∀ w, d.cw w Z = 0) ↔ eInf F • Z = 0 := by
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [smul_smul, finOne_mul_eInf, zero_smul, smul_zero]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w Z, h]
    ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
theorem cw_one_iff_k {p : Type} [DecidableEq p] (M : Matrix p p (AE F E)) :
    (∀ w, d.cw w M = 1) ↔ eInf F • M = eInf F • (1 : Matrix p p (AE F E)) := by
  have h1 : ∀ w, d.cw w (1 : Matrix p p (AE F E)) = 1 := fun w => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  constructor
  · intro h
    refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w => ?_) ?_
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h w, h1 w]
    · rw [smul_smul, smul_smul, finOne_mul_eInf, zero_smul, zero_smul]
  · intro h w
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k d w M, h, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_eInf_k, h1 w]
def InvFin_k (f : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X
def InvInf_k (G : Mx F E d.m d.n → ℂ) : Prop := ∀ X Z, finOne F • Z = 0 → G (X + Z) = G X
def fcrd_k (X : Mx F E d.m d.n) : Fin d.m × Fin d.n × Fin 2 → Af F := fun k => (d.crd X k).2
theorem gram_add_left_k (X X' Z : Mx F E d.m d.n) : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_add, Matrix.add_mul]
theorem gram_add_right_k (X Z Z' : Mx F E d.m d.n) : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
theorem gram_smul_left_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram (c • X) Z = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
theorem gram_smul_right_k (c : AF F) (X Z : Mx F E d.m d.n) : d.gram X (c • Z) = c • d.gram X Z := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  have : (c • Z).map (cA σ) = c • Z.map (cA σ) := by
    ext i j
    simp [map_smul]
  rw [this, Matrix.mul_smul]
theorem gram_fin_inf_k {X Z : Mx F E d.m d.n} (hX : eInf F • X = 0) (hZ : finOne F • Z = 0) : d.gram X Z = 0 := by
  have eX : X = finOne F • X := by
    conv_lhs => rw [← smul_split X, hX, zero_add]
  rw [eX, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem gram_inf_fin_k {X Z : Mx F E d.m d.n} (hX : finOne F • X = 0) (hZ : eInf F • Z = 0) : d.gram X Z = 0 := by
  have eZ : Z = finOne F • Z := by
    conv_lhs => rw [← smul_split Z, hZ, zero_add]
  rw [eZ, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hX]
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
theorem tt_add_k (M M' : Mx F E d.n d.n) : d.tt (M + M') = d.tt M + d.tt M' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _)]
theorem crd_add_k (X Z : Mx F E d.m d.n) (k) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
theorem crd_smul_k (c : AF F) (X : Mx F E d.m d.n) (k) : d.crd (c • X) k = c * d.crd X k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
theorem cmb_crd_k (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem cmb_smul_k (c : AF F) (x : Fin d.m × Fin d.n × Fin 2 → AF F) : d.cmb (fun k => c * x k) = c • d.cmb x := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Matrix.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul]
theorem fcrd_invInf_k (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (fun X => g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)) := by
  intro X Z hZ
  show g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d (X + Z)) = g (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X)
  congr 1
  funext k
  show (d.crd (X + Z) k).2 = (d.crd X k).2
  rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_add_k]
  change (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
  have : (d.crd Z k).2 = 0 := by
    rw [← finOne_snd_mul (d.crd Z k), ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.crd_smul_k, hZ]
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [this, add_zero]
theorem invInf_fcrd_k {G : Mx F E d.m d.n → ℂ} (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G) (X : Mx F E d.m d.n) :
    G X = G (d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k)) := by
  set Y := d.cmb fun k => pairA F 0 (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k d X k) with hY
  have hp : ∀ c : AF F, finOne F * c = pairA F 0 c.2 := fun c =>
    Prod.ext (finOne_fst_mul c) (finOne_snd_mul c)
  have e1 : finOne F • X = Y := by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_crd_k d X]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    simp only [hp, hY, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.fcrd_k]
  have e2 : finOne F • Y = Y := by
    rw [hY, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cmb_smul_k]
    congr 1
    funext k
    rw [hp]
    rfl
  have h := hG Y (X - Y) (by rw [smul_sub, e1, e2, sub_self])
  rw [add_sub_cancel] at h
  exact h
def StepF_k (x : d.G) (A B : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ) : Prop :=
  (∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d (A f)) ∧ ∀ G, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G → _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d (B G) ∧
    ∀ f, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f → ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * G X) → d.T (d.om x Φ) = fun X => A f X * B G X
theorem step_comp_k {x x' : d.G} {A A' B B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x A B) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' A' B') : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x * x') (A ∘ A') (B ∘ B') := by
  refine ⟨fun f hf => h.1 _ (h'.1 f hf), fun G hG => ⟨(h.2 _ (h'.2 G hG).1).1, fun f hf Φ hΦ hT => ?_⟩⟩
  have e1 := (h'.2 G hG).2 f hf Φ hΦ hT
  have hΦ' : d.om x' Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x' Φ hΦ
  have e2 := (h.2 (B' G) (h'.2 G hG).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) hΦ' e1
  rw [map_mul, mul_apply_eq_comp]
  exact e2
theorem key_split_k {f G A' B' : Mx F E d.m d.n → ℂ} (hf : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d f) (hA : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvFin_k d A') (hG : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d G)
    (hB : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.InvInf_k d B') (h : ∀ X, f X * G X = A' X * B' X) : ∀ X Y, f X * G Y = A' X * B' Y := by
  intro X Y
  have hW1 : eInf F • X + finOne F • Y = X + finOne F • (Y - X) := by
    calc eInf F • X + finOne F • Y = (eInf F • X + finOne F • X) + finOne F • (Y - X) := by rw [smul_sub]; abel
      _ = X + finOne F • (Y - X) := by rw [smul_split]
  have hW2 : eInf F • X + finOne F • Y = Y + eInf F • (X - Y) := by
    calc eInf F • X + finOne F • Y = (eInf F • Y + finOne F • Y) + eInf F • (X - Y) := by rw [smul_sub]; abel
      _ = Y + eInf F • (X - Y) := by rw [smul_split]
  have hfin : ∀ w, d.cw w (finOne F • (Y - X)) = 0 := fun w => _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_finOne_k d w _
  have hinf : finOne F • (eInf F • (X - Y)) = 0 := by rw [smul_smul, finOne_mul_eInf, zero_smul]
  have e := h (eInf F • X + finOne F • Y)
  rw [hW1, hf X _ hfin, hA X _ hfin, ← hW1, hW2, hG Y _ hinf, hB Y _ hinf] at e
  exact e
theorem step_conj_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ B₁ B₂ B' : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ}
    (h₁ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₁ A₁ B₁) (h₂ : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x₂ A₂ B₂) (h' : _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d (x₁ * x' * x₂) id B := by
  have hc := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d (_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h') h₂
  have h0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.step_comp_k d h₁ h₂
  refine ⟨fun G => if h : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 then
      (G h.choose / B₁ (B₂ G) h.choose) • B₁ (B' (B₂ G)) else 0,
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · intro X Z hZ
      simp only [Pi.smul_apply, smul_eq_mul]
      have e := (hc.2 G hG).1 X Z hZ
      simp only [Function.comp_apply] at e
      rw [e]
    · intro X Z _
      rfl
  · have e := (hc.2 G hG).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 G hG).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, one_apply_eq_self, hTΦ] at e0
    have key := _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.key_split_k d hf (h0.1 f hf) hG (h0.2 G hG).1 (fun X => congrFun e0 X)
    by_cases hz : (∀ X, f X = 0) ∨ ∀ X, G X = 0
    · have hΦ0 : Φ = 0 := (hT.1 F E σ d).2.2 Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [hz])
      subst hΦ0
      have hT0 : d.T 0 = 0 := by
        funext X
        have hschr : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (0 : d.Fn) = 0 := by
          intro p
          funext x
          simp [schr]
        simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, hschr,
          map_zero, Pi.zero_apply]
      rw [map_zero, hT0]
      funext X
      rcases hz with hz | hz
      · simp [hz]
      · have hn : ¬ ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [dite_eq_right hn]
    · push Not at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        simp only [Function.comp_apply] at this
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (G hex.choose / B₁ (B₂ G) hex.choose) := by
        intro u
        have := key u hex.choose
        simp only [Function.comp_apply] at this
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [Function.comp_apply, id_eq, dite_eq_left hex, Pi.smul_apply, smul_eq_mul, hA]
      ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockGood
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem goodAwayEx_k : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := by
  intro F E _ _ _ _ _ σ d R w
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  refine ⟨Ψ, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun h0 => ?_, fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩
  have h1 := congrFun h0 0
  have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
    funext k
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    rfl
  have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
    rw [hc]
    exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
  have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
  exact hp (by simpa [Ψ, hg0] using h1)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinMul
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
def TK_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Submodule ℂ (Mx F E d.m d.n → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d).map (_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d)
theorem D_dg_mem_k {Φ : d.Fn} (hΦ : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) {Z : Mx F E d.m d.n} (hZ : At (evI F) Z) :
    Box.D (d.dd.e (Z * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d :=
  _root_.PositivityTheory.SiegelWeilFormula.KK.D_kfS_k (fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]) hΦ
theorem mul_var_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => evX (MvPolynomial.X k) (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  obtain ⟨Φ, hΦ, rfl⟩ := hf
  obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.var_span'_k R w k
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ +
    (c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ,
    add_mem (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h1)) (Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.KK.D_dg_mem_k hΦ h2)), funext fun X => ?_⟩
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_add ((c₁ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)
    ((c₂ / (-(2 * Real.pi * Complex.I))) • Box.D (d.dd.e (Z₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ)) Φ)) X
  simp only [map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = _ at t
  change d.T _ X = _ * d.T Φ X
  rw [t]
  change _ * d.T _ X + _ * d.T _ X = _
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h1, _root_.PositivityTheory.SiegelWeilFormula.KK.T_D_dg_k (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k hΦ) h2, e X]
  field_simp
theorem mul_pol_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) :
    (fun X => evX Q (R.loc w X) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a =>
    have : (fun X => evX (MvPolynomial.C a) (R.loc w X) * f X) = a • f := funext fun X => by
      simp [evX]
    rw [this]; exact Submodule.smul_mem _ _ hf
  | add p q hp hq =>
    have : (fun X => evX (p + q) (R.loc w X) * f X) = (fun X => evX p (R.loc w X) * f X) + fun X => evX q (R.loc w X) * f X :=
      funext fun X => by simp [evX, add_mul]
    rw [this]; exact add_mem (hp hf) (hq hf)
  | mul_X p k hp =>
    have : (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
        fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) := funext fun X => by
      simp only [evX, map_mul]; ring
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_var_k R w k (hp hf)
theorem mul_prod_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (s : Finset (InfinitePlace F)) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d) : (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert w s hw ih =>
    have : (fun X => (∏ w ∈ insert w s, evX (P w) (R.loc w X)) * f X) =
        fun X => evX (P w) (R.loc w X) * ((∏ w ∈ s, evX (P w) (R.loc w X)) * f X) := funext fun X => by
      rw [Finset.prod_insert hw, mul_assoc]
    rw [this]; exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_pol_k R w (P w) ih
theorem vac_mem_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ}
    (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  have hgen : _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun X => by
    simp [_root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_kfS_k (_root_.PositivityTheory.SiegelWeilFormula.KK.thA_k R) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε) (fun k hk w => _root_.PositivityTheory.SiegelWeilFormula.KK.commute_thB_k R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  have m1 : Box.D (d.dd.e u') Φ ∈ d.sch := Box.DP_mem hΦ _ _
  have m2 : Box.D (d.dd.e u) Φ ∈ d.sch := Box.DP_mem hΦ _ _
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem m1 (Submodule.smul_mem _ _ m2)) (funext fun X => ?_))
  have t := congrFun ((_root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t
  rw [t, _root_.PositivityTheory.SiegelWeilFormula.KK.vac_rel_k R g hΦ e hu hu' hr X, sub_self]
  rfl
theorem fock_le_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ _root_.PositivityTheory.SiegelWeilFormula.KK.TK_k d := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have e : (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k R g X := funext fun X => by
    simp only [fP, _root_.PositivityTheory.SiegelWeilFormula.KK.vacF_k, Finset.prod_mul_distrib]; ring
  rw [SetLike.mem_coe, e]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.mul_prod_k R P _ (_root_.PositivityTheory.SiegelWeilFormula.KK.vac_mem_k hT hF R hg)
theorem polyKFin_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k := by
  intro hT hF F E _ _ _ _ _ σ d R Φ hΦ hf
  obtain ⟨Φ', h', e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.fock_le_k hT hF R hf
  have : Φ = Φ' := (sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem hΦ (_root_.PositivityTheory.SiegelWeilFormula.KK.mem_sch_k h')) (by
    rw [show d.T (Φ - Φ') = _root_.PositivityTheory.SiegelWeilFormula.KK.Tl_k d (Φ - Φ') from rfl, map_sub]
    exact sub_eq_zero.2 e.symm))).symm ▸ rfl
  rw [this]
  exact _root_.PositivityTheory.SiegelWeilFormula.KK.kFin_of_mem_k h'
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isW_eps (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε := by
  have hmem : (mat2 w₀)ᵀ * dbl (incM F d.Y.J) * (mat2 w₀).map (cA σ) = dbl (incM F d.Y.J) := w₀.2
  have hmat : mat2 w₀ = incM F d.b.1 * inFrame d.b w₀ * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  have hc := congrArg (d.cw w) hmem
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, hmat,
    _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h w] at hc
  set P := d.b.1.map (d.B.emb w).1
  set Pi := (d.b⁻¹).1.map (d.B.emb w).1
  set D := (dbl d.Y.J).map (d.B.emb w).1
  set Wc := wM d.n ((ε : ℤ) : ℂ)
  have hPiP : Pi * P = 1 := by
    simp only [Pi, P]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  apply eps_of_unit d.ok.hn ε R.ε
  calc Wcᵀ * Krd.Qc d.n R.ε * Wc.map star
      = (Pi * P)ᵀ * Wcᵀ * (Pᵀ * D * P.map star) * Wc.map star * (Pi * P).map star := by
        rw [hPiP, hQ, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    _ = Pᵀ * ((P * Wc * Pi)ᵀ * D * (P * Wc * Pi).map star) * P.map star := by
        simp only [Matrix.transpose_mul, Krd.mapStar_mul, Matrix.mul_assoc]
    _ = Krd.Qc d.n R.ε := by rw [hc, hQ]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepWN
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepW_exp (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) : ∀ (ε : ℤˣ) (w₀ : d.G), d.IsW ε w₀ →
    ∃ (C : ℂ) (B : d.MF → d.MF), C ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  intro ε w₀ hw
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', hC, -, hfact⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.intFact_k F E σ d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero ε)
    · exact Int.cast_ne_zero.mpr (Units.ne_zero (R.sg w))
  refine ⟨(C : ℂ), fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', by exact_mod_cast hC.ne',
    fun f hf => KW.locFT_sw _ _ hs f hf, fun Ψ hΨ => ⟨?_, ?_⟩⟩
  · intro X Z hZ1 hZ2
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z₀ => ?_)
    simp only
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, _root_.PositivityTheory.SiegelWeilFormula.KW.psi_zero_gram_k, mul_one]
  · intro f hf Φ hΦ hTΦ
    funext X
    rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
    let Ψ' : Mx F E d.m d.n → ℂ := fun Z =>
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)))) * Ψ Z
    have hΨ' : ∀ X' Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ' (X' + Z) = Ψ' X' := by
      intro X' Z hZ1 hZ2
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
    have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
        R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) * f u) Ψ' := by
      funext Z
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Ψ']
      have h := _root_.PositivityTheory.SiegelWeilFormula.KW.psi_add_right_k d ε X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) (Z - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z))
      rw [add_sub_cancel] at h
      rw [h]
      ring
    rw [e, hfact _ Ψ' hΨ']
    have e2 : ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only [Ψ']
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_of_mem_k d R w Z.2, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_zero_k, sub_zero]
    rw [e2]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KW.kernel_k R w ε X]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

