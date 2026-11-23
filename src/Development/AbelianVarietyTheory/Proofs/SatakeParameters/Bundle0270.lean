module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderValuation.WeakApprox
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Formalism.LocalToGlobal.Columns.Bundle0041
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
section
noncomputable section

namespace GlobalTheory.CosetApprox

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_valuation_le (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : P.valuation E x ≤ 1) :
    Formalism.L2.Col.IntAt P x := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x h
  exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

theorem apply_eq_sum {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) (w : Fin n → E) (l : Fin n) :
    g w l = ∑ k, w k * g (Pi.single k 1) l := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (g : T → (Fin n → E) →ₗ[E] (Fin n → E))
    (c : T → E) (t : T → Fin n → E) :
    ∃ d : Fin n → E, ∀ P : T, ∀ l, (P.1).valuation E (c P * g P (d - t P) l) ≤ 1 := by
  classical
  have hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧
      ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b := by
    intro P
    obtain ⟨b, hb⟩ := (Set.finite_range fun lk : Fin n × Fin n =>
      (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove
    exact ⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩
  choose B hB1 hBle using hb
  have hB0 : ∀ P, B P ≠ 0 := fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'
  have hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹ := by
    intro k
    obtain ⟨a, -, ha, -⟩ := PI.FinOrdValD.WA.weakApprox T
      (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0)
      (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1)
      (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))
    refine ⟨a, fun P => ?_⟩
    have h := ha P.1 P.2
    simp only [dif_pos P.2, Subtype.coe_eta] at h
    rw [← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h
  choose a ha using hk
  refine ⟨a, fun P l => ?_⟩
  rw [apply_eq_sum, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring,
    map_mul, Pi.sub_apply]
  calc (P.1).valuation E (a k - t P k) * (P.1).valuation E (c P * g P (Pi.single k 1) l)
      ≤ (B P)⁻¹ * B P := mul_le_mul' (ha k P).le (hBle P l k)
    _ = 1 := inv_mul_cancel₀ (hB0 P)

end Gen

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.MainNotions _root_.Formalism.L2.DIV _root_.Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem exists_sameCoset {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  classical
  obtain ⟨d, hd⟩ := exists_approx (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n))
    (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))
  refine ⟨d, fun P l => intAt_of_valuation_le _ _ ?_⟩
  have h := hd P l
  have e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [e]
  exact h

end GlobalTheory.CosetApprox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramesOfRightTranslatePointPrincipalCongruence
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.LevFrames

open Matrix

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem intAtA_neg' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

theorem intAtA_pow' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact GlobalTheory.CplPt.intAtA_mul ih h

theorem core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y⁻¹ * ratA F G₁)) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = 1 + Bm := by
    rw [hMh', hAm, hBm, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hB i j))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hA i j))))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_sum _ _ fun l _ => GlobalTheory.CplPt.intAtA_mul (hA i l) (hm l j)))
  have desc : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by
    intro m
    induction m with
    | zero => intro hm i j; simpa using hm i j
    | succ m ih => intro hm; exact ih (step m hm)
  obtain ⟨J, hJ⟩ := qth_bound Q Mm
  have hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ) := by
    have h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem _
    have := (Q.intValuation_le_pow_iff_mem _ 1).2 h0
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
    simpa using this
  have hbig : ∀ i j, IntAtA (F := F) Q (d ^ (J + 1) * (qi * Mh i j)) := by
    intro i j
    have e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j) := by
      rw [hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]
    rw [e]
    refine GlobalTheory.CplPt.intAtA_of_intAt ((qth_intAt_iff Q _).2 ?_)
    rw [map_mul, map_pow]
    calc Q.valuation E ((qOf Q : ℕ) : E) ^ (n * J) * Q.valuation E (Mm i j) ≤ WithZero.exp (-1 : ℤ) ^ (n * J) * WithZero.exp (J : ℤ) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hqv _) (hJ i j)
      _ ≤ 1 := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          have : (J : ℤ) ≤ (n : ℤ) * J := by exact_mod_cast Nat.le_mul_of_pos_left J hn
          rw [nsmul_eq_mul]
          push_cast
          linarith
  have hfin := desc (J + 1) hbig a b
  show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)
  refine GlobalTheory.RatInt.intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open Formalism.L2.Ker Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

theorem intAt_of_seamP (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E) (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

end Seam

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem frames_lev : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A a j hj β x x₁ κ hx p p₁ hp hp₁ P g hg
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  set F₀ := frsF t.sel (t.tup μ) p P with hF₀
  set F₁ := frsF t.sel (t.tup μ) p₁ P with hF₁
  have hX : NearAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)))
      (seamGL t.seam F₀ * seamGL t.seam g.1) :=
    GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) hg (GlobalTheory.CplPt.seamGL_int t.seam g)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 * ratA D.host.F (A.fb j hj β P) =
      (ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)) := by
    rw [hx]; group
  have hX₁ := hp₁.frame P
  rw [e, ← hF₁] at hX₁
  have hc := core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ hX hX₁
  set C₀ := g.1⁻¹ * F₀⁻¹ * F₁ with hC₀
  have hM : (seamGL t.seam F₀ * seamGL t.seam g.1)⁻¹ * seamGL t.seam F₁ = seamGL t.seam C₀ := by
    rw [hC₀, map_mul, map_mul, map_inv, map_inv, _root_.mul_inv_rev]
  simp only [hM] at hc
  have hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (C₀ (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N j)) l)) := by
    intro s l
    have hc' := hc l s
    rw [GlobalTheory.TwU.MidIndep.qOf_seamP] at hc'
    refine intAt_of_seamP t.seam P.1 _ ?_
    convert hc' using 1
    have hm := congrFun (seamGL_mulVec t.seam C₀ (Pi.single s 1)) l
    have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N _)) j)) = Pi.single s (1 : D.host.E) := by
      funext j
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hs1, Matrix.mulVec_single_one] at hm
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : l = s
    · subst h; simp [Matrix.col_apply]
    · simp [h, Matrix.col_apply]
  obtain ⟨hk, hpc⟩ := GlobalTheory.CongOne.mem_glint_prinCong_of_cols P.1 ((t.cst μ).D P) C₀ hD hcol
  refine ⟨⟨C₀, hk⟩, hpc, fun a' b' => ?_, ?_⟩
  · have h1 := GlobalTheory.CplPt.intAtA_of_intAt (F := D.host.F) (hc a' b')
    convert h1 using 2
    rw [map_mul (iA D.host.F D.host.E), Matrix.sub_apply, Matrix.sub_apply, map_sub (iA D.host.F D.host.E), GlobalTheory.CplPt.ratA_apply,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · show F₁ = F₀ * (g.1 * C₀)
    rw [hC₀]
    group

end GlobalTheory.LevFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelClassSumsCarryChainComplexForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical

namespace GlobalTheory.KFiClose

theorem kFi_of_tie : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D)
    (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → FormsPin t → OrbitPlaces.KFi D ex.tw := by
  intro D L hT Gi Gl K Y cX ex t hC hF
  have second : ∀ u μ, DV.Used D μ → ∀ i < D.R.m, ∀ φ ∈ (ex.tw.fm u μ).Fi i, (D.chTw u μ).K i φ ∈ (ex.tw.fm u μ).Fi (i + 1) := by
    intro u μ hμ
    obtain ⟨G, hFA, hSP⟩ := hF u μ hμ
    exact _root_.GlobalTheory.KerJ.FiCore.K_mem_Fi D u (D.chTw u μ) _ _ (ex.tw.fm u μ) (t.O u μ) G hFA (t.unf u μ)
      (fun i hi c c' => GlobalTheory.KerTieEntire.kerTie_entire D L hT Gi Gl K Y cX ex t u μ i hi c c')
      (_root_.GlobalTheory.KerJ.term_law D L hT Gi Gl K Y cX ex t hC u μ G hSP)
  have h0 : DV.Used D D.what₂.mu0 := by
    unfold DV.Used
    exact Or.inl rfl
  exact ⟨fun u i hi => GlobalTheory.KFiMu0.memberForms_stable_of_reference_tuple D ex.tw u i hi (second u _ h0 i hi), second⟩

end GlobalTheory.KFiClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.AwayTopG

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem hom_mem_stdAt {n m : ℕ} (f : HomE E n m) (hf : ∀ j l, IntAt P (f (Pi.single j 1) l)) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : f v ∈ stdAt E m P :=
  mem_stdAt.2 fun l => by
    have h := intAt_form_of_mem_stdAt (1 : E) (LinearMap.proj l ∘ₗ f) (fun i => by simpa using hf i l) hv
    simpa using h

theorem symm_mem_stdAt {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    κ.symm w ∈ stdAt E n P :=
  (hκ (κ.symm w)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hw)

theorem symm_near {n D : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P)
    (hD : ∀ w ∈ stdAt E n P, ((qOf P : E) ^ D)⁻¹ • (κ w - w) ∈ stdAt E n P) {w : Sp E n} (hw : w ∈ stdAt E n P) :
    ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) ∈ stdAt E n P := by
  have h := hD _ (symm_mem_stdAt hκ hw)
  rw [LinearEquiv.apply_symm_apply] at h
  have e : ((qOf P : E) ^ D)⁻¹ • (κ.symm w - w) = -(((qOf P : E) ^ D)⁻¹ • (w - κ.symm w)) := by
    rw [← smul_neg, neg_sub]
  rw [e]
  exact Submodule.neg_mem _ h

end SlopeTestRemainingChoices

theorem topDat_frames_vGs : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie P hP κ κ' hκ hκD hκ' hκ'D y y'' hy''
  have hok := t.idx_ok μ
  have hc := hok.cst_ok
  have hn : TopNum D.R (t.m2 + 1) := topNum_of (m_eq t μ)
  have hX : t.X.Ok := hPin.fields.ok
  have hPr := t.pr_ok
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := qOf_ne_zero
  obtain ⟨d, hd⟩ : ∃ d, (t.cst μ).D P = d + 1 := ⟨(t.cst μ).D P - 1, by have := hc.D_pos P; omega⟩
  by_cases hI : ∀ j l, IntAt P.1 (y (Pi.single j 1) l)
  ·
    have hA : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') := by
      refine topDat_congr t.Ch t.sel (t.tup μ) (t.cst μ) hX hPr hc hn P hP _ _ _ ?_ ?_
      · have h1 : κ.symm ((qOf P.1 : t.X.E) • y'') ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ (mem_stdAt.2 hy'')
        rw [map_smul] at h1
        intro j
        simpa using mem_stdAt.1 h1 j
      · intro j
        have hkj : κ (Pi.single j 1) ∈ stdAt t.X.E _ P.1 := (hκ _).2 (single_mem_stdAt j)
        have hv : y (κ (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 := hom_mem_stdAt y hI hkj
        have hz : κ'.symm (y (κ (Pi.single j 1))) ∈ stdAt t.X.E _ P.1 := symm_mem_stdAt hκ' hv
        have hzI : ∀ l, IntAt P.1 ((κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l) := fun l => mem_stdAt.1 hz l
        refine ⟨iff_of_true hzI (hI j), fun _ l => ?_⟩
        set s := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ (Pi.single j 1) - Pi.single j 1) with hs
        set s' := ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.symm (y (κ (Pi.single j 1))) - y (κ (Pi.single j 1))) with hs'
        have hsI : s ∈ stdAt t.X.E _ P.1 := hκD _ (single_mem_stdAt j)
        have hs'I : s' ∈ stdAt t.X.E _ P.1 := symm_near hκ' hκ'D hv
        have hys : IntAt P.1 (y s l) := mem_stdAt.1 (hom_mem_stdAt y hI hsI) l
        have e1 : y s l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (y (κ (Pi.single j 1)) l - y (Pi.single j 1) l) := by
          rw [hs, map_smul, map_sub]
          rfl
        have e2 : s' l = ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (κ'.symm (y (κ (Pi.single j 1))) l - y (κ (Pi.single j 1)) l) := by
          rw [hs']
          rfl
        have key : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (Pi.single j 1) l =
            y (Pi.single j 1) l + (qOf P.1 : t.X.E) * ((qOf P.1 : t.X.E) ^ d * (y s l + s' l)) := by
          rw [e1, e2, hd]
          show κ'.symm (y (κ (Pi.single j 1))) l = _
          field_simp
          ring
        rw [key, redP_add_q ((intAt_pow (intAt_nat _) d).mul (hys.add (mem_stdAt.1 hs'I l)))]
    have hB : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y (κ.symm y'') =
        topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' := by
      unfold topDat
      congr 1
      have hw : (qOf P.1 : t.X.E) • y'' ∈ stdAt t.X.E _ P.1 := mem_stdAt.2 hy''
      have hsw := symm_near hκ hκD hw
      have hdiff : κ.symm y'' - y'' ∈ stdAt t.X.E _ P.1 := by
        refine mem_stdAt.2 fun i => ?_
        have hi := mem_stdAt.1 hsw i
        have e : (κ.symm y'' - y'') i = (qOf P.1 : t.X.E) ^ d *
            ((((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.symm ((qOf P.1 : t.X.E) • y'') - (qOf P.1 : t.X.E) • y'')) i) := by
          rw [map_smul, hd]
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp
          ring
        rw [e]
        exact (intAt_pow (intAt_nat _) d).mul hi
      have h := ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (fun h => absurd hP h) (κ := 1)
        (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ y) y'' (κ.symm y'')
        (fun _ => hy'') (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
      exact h
    exact hA.trans hB
  ·
    push_neg at hI
    obtain ⟨j, l, hjl⟩ := hI
    have h0 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'' = 0 := by
      by_contra h
      exact hjl (topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP y y'' h j l)
    have h1 : topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') = 0 := by
      by_contra h
      have hzI := topDat_int t.Ch t.sel (t.tup μ) (t.cst μ) hn P hP _ _ h
      apply hjl
      have hm : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) ∈ stdAt t.X.E _ P.1 :=
        hom_mem_stdAt _ hzI (symm_mem_stdAt hκ (single_mem_stdAt j))
      have e : (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm (Pi.single j 1)) = κ'.symm (y (Pi.single j 1)) := by
        simp
      rw [e] at hm
      have hm' := (hκ' _).2 hm
      rw [LinearEquiv.apply_symm_apply] at hm'
      exact mem_stdAt.1 hm' l
    rw [h0, h1]

end GlobalTheory.TwV.AwayTopG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeChainComparisonIndepDivisionLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd


set_option maxHeartbeats 1000000 in
theorem cmpLite_setDiv : ∀ (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : G.Fills (D.gat u w hg)) (Lv : G.Levels Fl) (Ch : G.Chain Lv), GlobalTheory.TwU.CmpLite D c Tw u μ w hg Ch → GlobalTheory.TwU.CmpLite (setDiv D N h) (cmpTr N h c) (twTr N h Tw) u μ w hg Ch := by
  intro D N h c Tw u μ w hg Fl Lv Ch H
  exact H

end GlobalTheory.Svd
end

