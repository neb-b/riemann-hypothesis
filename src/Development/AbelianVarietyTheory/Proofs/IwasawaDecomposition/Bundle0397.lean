module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaMove.Moved

namespace GlobalTheory.Mem.NatEqui

variable {D : D7}

theorem chi_smulLat {χ : IdE D → ℂ} (hχ : IsChi D χ) {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
      χ (detId D (stdL D n) (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)) =
        (∏ τ : D.what₂.Tau, (embT D τ (γ : Matrix (Fin n) (Fin n) D.host.E).det)⁻¹) * χ (detId D (stdL D n) L) := by
  letI := D.host.cmStar
  intro γ
  have hst : ∀ x : D.host.E, star x = D.host.conj x := GlobalTheory.NormSum.AdLattice.star_eq_conj D
  let z : unitary D.host.E := ⟨_, Matrix.det_of_mem_unitary γ.2⟩
  rw [GlobalTheory.Mem.Col2.ChiFacLaw.detId_image D (stdL D n) L (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)
    (γ : Matrix (Fin n) (Fin n) D.host.E)
    (star (γ : Matrix (Fin n) (Fin n) D.host.E)) γ.2.2 (fun x hx => ⟨x, hx, rfl⟩) ?_,
    hχ.1 _ _ (GlobalTheory.Mem.Col2.ChiFacLaw.norm_one_span D z.1 (by rw [← hst]; exact z.2.2))
      (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (sd_stdL D n) hL hL).1, hχ.2 z]
  rintro _ ⟨y, hy, rfl⟩
  change (star (γ : Matrix (Fin n) (Fin n) D.host.E)).mulVec ((γ : Matrix (Fin n) (Fin n) D.host.E).mulVec y) ∈ L
  rwa [Matrix.mulVec_mulVec, γ.2.1, Matrix.one_mulVec]

theorem sd_smulLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, SD D (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L) := by
  intro γ
  obtain ⟨g, hg⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D n L hL
  obtain ⟨γA, hγ⟩ := GlobalTheory.TrueTheta.exists_rat γ
  exact GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.TrueTheta.moves_smulLat hγ hg)

theorem chiFac_ne_zero {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L'} (h : SD D L) (h' : SD D L') :
    Base.chiFac χ N N' L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N) h))
    (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N') h'))

theorem chiFac_right {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} (L) {L' L''} (h' : SD D L') (h'' : SD D L'') :
    Base.chiFac χ N N' L L'' = χ (detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N') h' h'', mul_zpow]
  ring

theorem chiFac_left {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L₁} (L') (h : SD D L) (h₁ : SD D L₁) :
    Base.chiFac χ N N' L₁ L' = χ (detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N) h h₁, mul_zpow]
  ring

theorem eqP : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  intro D cc δ B χ hc hδ hχ
  letI := D.host.cmStar
  have hC : Crv D cc δ := ⟨hc, hδ⟩
  obtain ⟨χ', e, hχ', hv, q1, q2, q3⟩ := _root_.GlobalTheory.TrueTheta.exists_family_of_curve D cc δ hC
  have key : ∀ N N', Even N → Even N' → ∃ a : ℂ, ∀ L L', SD D L → SD D L' → B.eNat χ N N' L L' =
      fun z => (a * (Base.chiFac χ N N' L L' / Base.chiFac χ' N N' L L')) * e N N' L L' z := by
    intro N N' hN hN'
    have s := sd_stdL D N
    have s' := sd_stdL D N'
    obtain ⟨v1, v2, -⟩ := hv N N' _ _ ⟨hN, hN', s, s'⟩
    obtain ⟨a, ha⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N' _
      (Or.inr ⟨_, _, s, s', rfl⟩)).1 _
      (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ B hC) N N') _ v1 v2
    refine ⟨a, fun L L' h h' => funext fun z => ?_⟩
    have e3 := q3 N N' ⟨_, s⟩ ⟨L, h⟩ ⟨_, s'⟩ hN hN'
    have e2 := congrFun (q2 N N' ⟨L, h⟩ ⟨_, s'⟩ ⟨L', h'⟩ hN hN') z
    dsimp only at e2 e3
    rw [e3, iop_mul, ← mul_assoc, mul_comm (χ' _ ^ _)] at e2
    have hh : B.thHalf N N' L = fun w => a * Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) (stdL D N'))
        (La D (tor0 D cc δ) L (stdL D N')) (e N N' (stdL D N) (stdL D N')) w := by
      funext w
      rw [Base.thHalf, ha]
      exact iop_mul D _ _ _ a _ w
    have h0 := chiFac_ne_zero hχ' h h'
    change Base.chiFac χ N N' L L' * B.thMoved N N' L L' z = _
    rw [Base.thMoved, hh, iop_mul, e2]
    change _ = a * (_ / Base.chiFac χ' N N' L L') * (Base.chiFac χ' N N' L L' * _)
    field_simp
  refine ⟨fun N N' L L' hN hN' γ γ' => ?_, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ'), ← q1 N N' L L' hN hN' γ γ']
    have h1 := chiFac_ne_zero hχ' (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ')
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    funext z
    change _ * pull D _ _ _ (e N N' L.1 L'.1) z = _
    congr 2
    rw [div_eq_div_iff h0 h1]
    unfold Base.chiFac
    rw [chi_smulLat hχ L.2, chi_smulLat hχ L'.2, chi_smulLat hχ' L.2, chi_smulLat hχ' L'.2]
    simp only [mul_zpow]
    ring
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L.2 L''.2, q2 N N' L L' L'' hN hN']
    funext z
    have h1 := zpow_ne_zero (-((N / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L'.2 L''.2)
    rw [iop_mul, chiFac_right hχ _ L'.2 L''.2, chiFac_right hχ' _ L'.2 L''.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L₁.2 L'.2, q3 N N' L L₁ L' hN hN']
    funext z
    have h1 := zpow_ne_zero (((N' / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L.2 L₁.2)
    rw [iop_mul, chiFac_left hχ _ L.2 L₁.2, chiFac_left hχ' _ L.2 L₁.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp

end GlobalTheory.Mem.NatEqui
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

def wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :=
  Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
    {c | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
      c = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E)}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ}
    (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t : ZMod g) : Prop :=
  c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w

def argS (X : HidaSetting D) (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem otherInstanceCharacter_eq_psi_symmetricArgument (X : HidaSetting D) (x : X.B.I.Gf) :
    X.chi2 x = X.psiEf (divN X.B.I X.B.g (argS X x)) := rfl


open Classical in
def side (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Bool := decide (GlobalTheory.Mem.SymFrame.EwAt X w)

def wtA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wtB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem wt_add (ρ k : ℕ) (s : Bool) {r : ℕ} (i j : Fin r) :
    wtA ρ k s i j + wtB ρ k s i j = 1 ∨ wtA ρ k s i j + wtB ρ k s i j = -1 := by
  unfold wtA wtB
  split_ifs <;> simp

theorem hA_smul_right' (X : HidaSetting D) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I x (c • y) = c * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y + z) = hA X.B.I x y + hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_zero_right' (X : HidaSetting D) (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {x v : VA X.B.I} (hx : x ∈ X.B.I.Lf)
    (hv : v ∈ wLf X w) : hA X.B.I x v ∈ wInt X w := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hv
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, y', hy', rfl⟩ := hy
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) := by
        funext i; simp [map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hint : hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) ∈
          Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        GlobalTheory.St.G.FrameClose.hA_int hx (Submodule.subset_span ⟨⟨y', hy'⟩, rfl⟩)
      rw [mul_comm]
      exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span ⟨a, ha, rfl⟩)
    | zero =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) ∈ wInt X w
      rw [e, hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) =
          (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) +
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (b i)) := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) ∈ wInt X w
      rw [e, hA_add_right']; exact add_mem ha hb
    | smul c a _ ha =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) := by
        funext i; simp [Algebra.smul_def, map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hc : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        Formalism.UG.P.easyc_inclE_mem _ _ _ (by first | exact ⟨c, rfl⟩ | exact c.2 | simp [Formalism.UG.intOE])
      exact (wInt X w).smul_mem (⟨_, hc⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) ha
  | zero => rw [hA_zero_right']; exact zero_mem _
  | add a b _ _ ha hb => rw [hA_add_right']; exact add_mem ha hb
  | smul c a _ ha =>
    show hA X.B.I x ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ wInt X w
    rw [hA_smul_right']
    exact (wInt X w).smul_mem c ha

theorem hA_sub_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y - z) = hA X.B.I x y - hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sum_right' (X : HidaSetting D) {ι : Type} (s : Finset ι) (x : VA X.B.I) (y : ι → VA X.B.I) :
    hA X.B.I x (∑ j ∈ s, y j) = ∑ j ∈ s, hA X.B.I x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hA_zero_right' X x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right', ih]

theorem hA_isMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : GlobalTheory.Mem.SymFrame.IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) -
      ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j) ∈ wInt X w := by
  have h := hA_mem_wInt X w hy (hN i)
  rw [hA_sub_right', hA_sum_right'] at h
  simpa only [hA_smul_right'] using h

theorem wInt_of_zmod (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ wInt X w := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨m, hm⟩ : D.host.g k ∣ X.B.g := by
    rw [X.g_eq]; fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hgen : ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
    · simp
    · simp
  have e : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t =
      ((m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (D.host.g k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    rw [hm, Nat.cast_mul]; ring
  rw [e]
  exact (wInt X w).smul_mem (⟨_, mul_mem (natCast_mem _ m) ht⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hgen

end GlobalTheory.Mem.SymChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointOverXHasAdelicPointBlockExtendMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TilQ

section ExtM

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A)

theorem extM_iC_iC (i j : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iC hN j) = g i j := by
  simp [TilX.extM, Br.iC]

theorem extM_iC_iL (i : Fin n) : TilX.extM hN g (Br.iC hN i) (Br.iL hN) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iC (j : Fin n) : TilX.extM hN g (Br.iL hN) (Br.iC hN j) = 0 := by
  simp [TilX.extM, Br.iC, Br.iL]

theorem extM_iL_iL : TilX.extM hN g (Br.iL hN) (Br.iL hN) = 1 := by
  simp [TilX.extM, Br.iL]

end ExtM

section Single

variable {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1)

theorem prH_single_iC (j : Fin n) : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iC hN j) 1) = Pi.single j 1 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Pi.single_eq_of_ne (fun e => h (Br.iC_inj hN e)), Pi.single_eq_of_ne h]

theorem prH_single_iL : GlobalTheory.TopStep.prH E hN (Pi.single (Br.iL hN) 1) = 0 := by
  funext i
  rw [GlobalTheory.TopStep.prH_apply, Pi.single_eq_of_ne]
  · rfl
  · intro e
    have := congrArg Fin.val e
    simp [Br.iC, Br.iL] at this
    omega

end Single

theorem adAt_of_bc_one {B : Base} {n : ℕ} {k : GA B n} (P : HeightOneSpectrum (𝓞 B.host.E))
    (hk : bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) k = 1) (i j : Fin n) :
    adAt B.host.F P (k.1 i j) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion B.host.E)) i j := by
  have h2 : prV (E := B.host.E) (P.under (𝓞 B.host.F))
      (k.1 i j - (1 : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin n) _ => g.1 i j) hk
    simp only [Units.val_one] at h3
    have h4 : prV (E := B.host.E) (P.under (𝓞 B.host.F)) (k.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := TilX.adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp


set_option maxHeartbeats 1600000 in
theorem pt_tilF_gen : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (k t : GA B (B.R.N B.R.m)), (∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m)) → (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) → (∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = (B.R.N B.R.m) → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) → t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs → (∀ (P : I.Q a) (i j : Fin (B.R.N B.R.m)), adAt B.host.F P.1 (t.1 i j) = algebraMap B.host.E _ (if i = j then (if i.1 + 1 = (B.R.N B.R.m) then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 1) else 0)) → ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * (k * t)) (tilF I.sel (I.tup a) u d) := by
  intro B X I hI hP l Z u a k t hk1 hk2 hk3 ht htP d g' g hg' hext
  haveI : IsEmpty ↥(∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := ⟨fun x => Finset.notMem_empty _ x.2⟩
  obtain ⟨p0, hp0, hN0⟩ := hk1
  have hPr := (base_fields_primes_ok B X).2.1
  have hN := N_m_succ B.R
  have hgw : ∀ w : (B.primes X).vGs, ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
    intro w
    have h1 : ∃ i, w.1 ∈ (B.primes X).vG i := by
      have h0 := w.2
      unfold Primes.vGs at h0
      simp only [Finset.mem_union] at h0
      rcases h0 with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, ?_⟩
    rw [← hPr.piG_norm i]
    exact w.1.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)
  have hpi1 : ∀ w : (B.primes X).vGs, (B.primes X).piT u - 1 ∈ w.1.asIdeal := by
    intro w
    obtain ⟨i, hi⟩ := hgw w
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    rw [hc]
    refine w.1.asIdeal.mul_mem_right _ ?_
    have hd : (B.primes X).g i ∣ (B.primes X).cond * ((B.primes X).g 0 * (B.primes X).g 1) ^ 2 := by
      refine dvd_mul_of_dvd_right (dvd_pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨c', hc'⟩ := hd
    rw [hc']
    push_cast
    exact w.1.asIdeal.mul_mem_right _ hi
  have hTw : ∀ w : (B.primes X).vGs, (B.T u : 𝓞 B.host.F) ∉ (w.1.under (𝓞 B.host.F)).asIdeal := by
    intro w hT
    obtain ⟨i, hi⟩ := hgw w
    have h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.1.asIdeal := hT
      rw [map_natCast] at h2
      exact h2
    have hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i) :=
      (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)
    have h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
      have e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) +
          (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [← hab]; push_cast; ring
      have e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E) := by simp
      rw [e', e]
      exact add_mem (w.1.asIdeal.mul_mem_left _ h1) (w.1.asIdeal.mul_mem_left _ hi)
    exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
  have hkw : ∀ (w : (B.primes X).vGs) (i j : Fin (B.R.N B.R.m)),
      adAt B.host.F w.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 i j) = (1 : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (w.1.adicCompletion B.host.E)) i j := by
    intro w i j
    refine adAt_of_bc_one w.1 ?_ i j
    rw [map_inv, hk2 _ (hTw w), inv_one]
  have hA := TilX.isPtOf_tilFr (hc := B.sp.cm) (ST := (B.primes X).vT u) hN (conj_piT_notMem hPr u) hpi1
    (hg'.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)) hp0.uni
    (by have := hp0.lat; rwa [hN0] at this) hkw hk3
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 ht
  have hB := (isPtOf_mul_J0 B.host.F B.host.E B.sp.cm _ ((B.primes X).vT u) (B.primes X).vGs ∅ _ m.1 _
    (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)) 1).2.1 rfl hA m.2 (by rw [inv_one]; exact hm)
  obtain ⟨-, -, hiX, -⟩ := _root_.GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have hgext : g = TilX.extGL hN g' := by
    refine Units.ext (TilX.eq_extM_of_ext hN (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) hpi0
      (TilX.iXm_apply hiX hN) hext.1 ?_)
    have h2 := hext.2
    have hz : z0 X u = Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) := TilX.lastCoordinateUniformizerVector_eq_single u
    rw [hz] at h2
    exact h2
  have hQ := PerLaw.piT_notMem_Q hI u a
  have hQ0 : ∀ P : (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))), (B.primes X).piT u ∉ P.1.asIdeal := fun P => isEmptyElim P
  have e : (tilF I.sel (I.tup a) u d).deco =
      (tilFr (ST := (B.primes X).vT u) hN ((B.primes X).piT u) (extTo ∅ d)).deco := by
    rw [tilF_deco I.sel (I.tup a) hPr u hQ d, tilFr_deco hN (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) hQ0, extTo_deco]
  rw [show ((1, 1, 1) : UF B.fields.E (B.R.N B.R.m) × GLG (E := B.fields.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) ×
    GLQ B.fields.E (B.R.N B.R.m) ∅) = 1 from rfl, one_smul] at hB
  rw [hgext, ← mul_assoc]
  refine ⟨hB.uni, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact hB.lat
  · rw [e]; exact hB.f
  · rw [e]; exact hB.be
  · intro P i j
    have hTq : (B.T u : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
      intro hT
      have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.1.asIdeal := hT
      rw [map_natCast] at h2
      exact T_notMem_QE I.sel (I.tup a) u hPr hI.sel_ok (hI.T_mem u) P.1 P.2 h2
    have hkP := adAt_of_bc_one P.1 (hk2 _ hTq)
    have e1 : adAt B.host.F P.1 (((TilX.extGL hN g' * k * (J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m :
        GA B (B.R.N B.R.m)) : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) i j) =
        adAt B.host.F P.1 (TilX.extM hN g'.1 i j) *
          adAt B.host.F P.1 ((((J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)).subtype m : GA B (B.R.N B.R.m)) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) j j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j]
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_eq_single j, map_mul, hkP, Matrix.one_apply_eq, mul_one]
          · rfl
          · intro l _ hl
            rw [map_mul, hkP, Matrix.one_apply_ne hl, mul_zero]
          · simp
      · intro l _ hl
        rw [map_mul, htP P l j, if_neg hl, map_zero, mul_zero]
      · simp
    rw [e1, htP P j j, if_pos rfl, tilF_fr I.sel (I.tup a) hPr u hQ d P]
    rcases GlobalTheory.TopStep.idx_cases hN i with ⟨i', rfl⟩ | rfl <;> rcases GlobalTheory.TopStep.idx_cases hN j with ⟨j', rfl⟩ | rfl
    · have h1 : ¬ ((Br.iC hN j').1 + 1 = B.R.N B.R.m) := by
        show ¬ (j'.1 + 1 = B.R.N B.R.m)
        have := j'.2
        omega
      rw [if_neg h1, map_one, mul_one, extM_iC_iC, hg'.fr P i' j']
      congr 1
      exact ((congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) _ (Pi.single (Br.iC hN j') 1)) i').trans
        (by rw [prH_single_iC])).symm
    · have h0 := (congrFun (GlobalTheory.TopStep.prH_sumE hN (d.fr P) (unitOf ((B.primes X).piT u)) (Pi.single (Br.iL hN) 1)) i').trans
        (by rw [prH_single_iL, map_zero])
      rw [extM_iC_iL, map_zero, zero_mul]
      exact (congrArg (algebraMap B.host.E _) h0).trans (map_zero _) |>.symm
    · rw [extM_iL_iC, map_zero, zero_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_of_ne, mul_zero, map_zero]
      intro e
      have := congrArg Fin.val e
      simp [Br.iC, Br.iL] at this
      omega
    · have h1 : (Br.iL hN).1 + 1 = B.R.N B.R.m := by
        show (B.R.N B.R.m - 1) + 1 = B.R.N B.R.m
        omega
      rw [if_pos h1, extM_iL_iL, map_one, one_mul, GlobalTheory.TopStep.sumE_last, Pi.single_eq_same, mul_one,
        unitOf_val (hQ P)]

end GlobalTheory.Mem.Col2.TilQ

end
end

