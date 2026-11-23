module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Formalism.LocalToGlobal.Columns.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0247

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgre
section
noncomputable section

namespace GlobalTheory.FrameAway

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.UG _root_.Formalism.L2.Col GlobalTheory.TwU GlobalTheory.TwU.Model
open scoped TensorProduct

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem intAtA_of_prV (P : HeightOneSpectrum (𝓞 E)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v P → prV (E := E) v z = 0) : IntAtA (F := F) P z :=
  GlobalTheory.T.integralAt_of_component_zero_under_prime P z h

theorem intAt_of_intAtA (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : IntAtA (F := F) P (iA F E x)) : IntAt P x :=
  GlobalTheory.T.integralAt_of_adelic_integralAt P x h

theorem intAtA_of_intAt (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : IntAt P x) : IntAtA (F := F) P (iA F E x) := by
  obtain ⟨r, s, hs, e⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [← map_mul, e]
  exact (Formalism.L2.DIV.toRInt F E r).2

theorem intAtA_neg (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

theorem intAtA_pow (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact intAtA_mul ih h

theorem frame_core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y y₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y₁⁻¹ * ratA F G₁))
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → bc (prV (E := E) v) y₁ = bc (prV (E := E) v) y) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y₁⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hCm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = (1 + Cm) * (1 + Bm) := by
    rw [hMh', hAm, hBm, hCm, add_sub_cancel, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Cm * (1 + Bm) + Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hC : ∀ v : HeightOneSpectrum (𝓞 F), IsOver v Q → ∀ i j, prV (E := E) v (Cm i j) = 0 := by
    intro v hvv i j
    have h1 : bc (prV (E := E) v) (y⁻¹ * y₁) = 1 := by
      rw [map_mul, map_inv, hv v hvv, inv_mul_cancel]
    have h2 := congrArg (fun g : GL (Fin N) (E ⊗[F] v.adicCompletion F) => (g : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) i j) h1
    simp only [Units.val_one] at h2
    change prV (E := E) v (((y⁻¹ * y₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) i j) = (1 : Matrix (Fin N) (Fin N) _) i j at h2
    rw [hCm, Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * (Cm * (1 + Bm)) i j) + d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    refine intAtA_add (intAtA_add (intAtA_add ?_ (intAtA_mul (intAtA_pow Q hd m) (hB i j))) (intAtA_neg Q (intAtA_mul (intAtA_pow Q hd m) (hA i j)))) (intAtA_neg Q (intAtA_sum _ _ fun l _ => intAtA_mul (hA i l) (hm l j)))
    refine intAtA_of_prV Q _ fun v hvv => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_mul, Matrix.mul_apply, map_sum]
    simp [hC v hvv]
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
    refine intAtA_of_intAt Q _ ((qth_intAt_iff Q _).2 ?_)
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
  refine intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open _root_.Formalism.L2.Ker _root_.Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

theorem qOf_seamP (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hy
      refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm y, (mem_seamP s P _).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact (mem_seamP s P x).2 hx
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s.iE) hI).symm.toEquiv

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

open _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Ker _root_.Formalism.L2.DIV GlobalTheory.TwV in
theorem frame_away : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β x x₁ p p₁ hp hp₁ P hv
  letI := D.host.cmStar
  have hD := (t.idx_ok μ).cst_ok.D_pos P
  set k := (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P with hk
  refine ⟨k, (mul_inv_cancel_left _ _).symm, fun s l => ?_⟩
  have hf : CongAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p P))) :=
    hp.frame P
  have hf₁ : CongAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P))⁻¹ * ratA D.host.F (seamGL t.seam (frsF t.sel (t.tup μ) p₁ P))) :=
    hp₁.frame P
  have hw : ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) →
      bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by
    intro v hvv
    have e := hv v hvv
    simp only [map_mul]
    rw [e]
  have hc := frame_core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ _ hf hf₁ hw l s
  rw [← map_inv, ← map_mul, qOf_seamP, ← hk] at hc
  refine intAt_of_seamP t.seam P.1 _ ?_
  convert hc using 1
  have hm := congrFun (seamGL_mulVec t.seam k (Pi.single s 1)) l
  have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) j)) = Pi.single s (1 : D.host.E) := by
    funext j
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [hs1, Matrix.mulVec_single_one] at hm
  rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
  by_cases h : l = s
  · subst h; simp [Matrix.col_apply]
  · simp [h, Matrix.col_apply]

end GlobalTheory.FrameAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFramesCongruentOneOfSameBadPlaceComponents
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameAgree

theorem inv_mul_cong {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {N : ℕ} (π : K) (hπ0 : π ≠ 0)
    (hπ : Valued.v π < 1) (a a₁ : GL (Fin N) K)
    (ha : ∀ i j, Valued.v (π⁻¹ * ((a : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1)
    (ha₁ : ∀ i j, Valued.v (π⁻¹ * ((a₁ : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1) :
    ∀ i j, Valued.v (π⁻¹ * (((a⁻¹ * a₁ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) - 1) i j) ≤ 1 :=
  _root_.GlobalTheory.GL_inv_mul_congr_one π hπ0 hπ a a₁ ha ha₁

theorem glint_of_cong {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ)
    (g : Sp E n ≃ₗ[E] Sp E n)
    (hg : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b)))
    (hg' : ∀ a b, IntAt P (((qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) :
    g ∈ GLint E n P ∧ ∀ w ∈ stdAt E n P, ((qOf P : E) ^ d)⁻¹ • (g w - w) ∈ stdAt E n P :=
  GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow P d g hg hg'

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

abbrev locM (Q : HeightOneSpectrum (𝓞 E)) : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) →* GL (Fin N) (Q.adicCompletion E) :=
  bc (GlobalTheory.Mem.Col2.adAt F Q)

theorem congAt_loc (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : CongAt (F := F) Q n k) : ∀ a b, Valued.v ((algebraMap E (Q.adicCompletion E) (((qOf Q : ℕ) : E) ^ n))⁻¹ *
      (((locM Q k : GL (Fin N) (Q.adicCompletion E)) : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) - 1) a b) ≤ 1 := by
  have hι : IsAdIso (GlobalTheory.Mem.Col2.afIso F E) := ⟨GlobalTheory.Mem.Col2.afIso_tmul_one F E, GlobalTheory.Mem.Col2.mem_rInt_iff F E⟩
  intro a b
  have h1 := hι.val_le (h a b)
  have e1 : ∀ z, GlobalTheory.Mem.Col2.afIso F E z Q = GlobalTheory.Mem.Col2.adAt F Q z := fun z => rfl
  rw [e1, map_mul, GlobalTheory.Mem.Col2.adAt_inclE, map_inv₀, Matrix.sub_apply, map_sub] at h1
  have e2 : GlobalTheory.Mem.Col2.adAt F Q ((1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) =
      (1 : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) a b := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2] at h1
  rw [Matrix.sub_apply]
  exact h1

theorem loc_agree (Q : HeightOneSpectrum (𝓞 E)) {x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : bc (prV (E := E) (Q.under (𝓞 F))) x₁ = bc (prV (E := E) (Q.under (𝓞 F))) x) : locM Q x₁ = locM Q x := by
  apply Units.ext
  refine Matrix.ext fun a b => ?_
  have h1 := congrArg (fun g : GL (Fin N) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => Units.val g a b) h
  change prV (E := E) (Q.under (𝓞 F)) ((x₁ : Matrix (Fin N) (Fin N) _) a b) =
    prV (E := E) (Q.under (𝓞 F)) ((x : Matrix (Fin N) (Fin N) _) a b) at h1
  have h0 : prV (E := E) (Q.under (𝓞 F)) ((x₁ : Matrix (Fin N) (Fin N) _) a b - (x : Matrix (Fin N) (Fin N) _) a b) = 0 := by
    rw [map_sub, sub_eq_zero]; exact h1
  have h2 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E _ _).1.1 h0 Q rfl
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem val_alg (Q : HeightOneSpectrum (𝓞 E)) (e : E) :
    Valued.v (algebraMap E (Q.adicCompletion E) e) = Q.valuation E e :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q e

theorem intAt_of_val (Q : HeightOneSpectrum (𝓞 E)) (c m o : E)
    (h : Valued.v ((algebraMap E (Q.adicCompletion E) c)⁻¹ * (algebraMap E (Q.adicCompletion E) m - algebraMap E (Q.adicCompletion E) o)) ≤ 1) :
    IntAt Q (c⁻¹ * (m - o)) := by
  rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val, ← val_alg, map_mul, map_inv₀, map_sub]
  exact h

theorem one_entry {E₀ : Type} [Field E₀] (Q : HeightOneSpectrum (𝓞 E)) (ψ : E₀ ≃+* E) (a b : Fin N) :
    (1 : Matrix (Fin N) (Fin N) (Q.adicCompletion E)) a b = algebraMap E (Q.adicCompletion E) (ψ ((1 : Matrix (Fin N) (Fin N) E₀) a b)) := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Loc

theorem map_expr {E₀ E : Type} [Field E₀] [Field E] (σ : E₀ ≃+* E) (q d : ℕ) (m o : E₀) :
    ((q : E) ^ d)⁻¹ * (σ m - σ o) = σ (((q : E₀) ^ d)⁻¹ * (m - o)) := by
  simp [map_mul, map_inv₀, map_pow, map_natCast, map_sub]

theorem qOf_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) : qOf (seamP s P) = qOf P := by
  have hI : (seamP s P).asIdeal = P.asIdeal.map (RingOfIntegers.mapRingEquiv s.iE) := by
    ext y
    rw [← (RingOfIntegers.mapRingEquiv s.iE).apply_symm_apply y, mem_seamP, Ideal.mem_map_of_equiv]
    constructor
    · intro hy; exact ⟨_, hy, rfl⟩
    · rintro ⟨z, hz, e⟩
      rw [(RingOfIntegers.mapRingEquiv s.iE).injective e] at hz
      exact hz
  unfold qOf
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (seamP s P).asIdeal (RingOfIntegers.mapRingEquiv s.iE) hI).toEquiv).symm

theorem intAt_seamP {D : D7} {X : Fields} (s : Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) (e : X.E) :
    IntAt (seamP s P) (s.iE e) ↔ IntAt P e := by
  have hc : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (RingOfIntegers.mapRingEquiv s.iE y) = s.iE (algebraMap (𝓞 X.E) X.E y) :=
    fun y => rfl
  constructor
  · rintro ⟨r, c, hc', h⟩
    refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, (RingOfIntegers.mapRingEquiv s.iE).symm c, ?_, ?_⟩
    · rw [← mem_seamP s, RingEquiv.apply_symm_apply]; exact hc'
    · apply s.iE.injective
      rw [map_mul, ← hc, ← hc, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      exact h
  · rintro ⟨r, c, hc', h⟩
    refine ⟨RingOfIntegers.mapRingEquiv s.iE r, RingOfIntegers.mapRingEquiv s.iE c, ?_, ?_⟩
    · rw [mem_seamP s]; exact hc'
    · rw [hc, hc, ← map_mul, h]

end GlobalTheory.FrameAgree

namespace GlobalTheory.FrameAgree

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem core (hTie : AdTie A dtU a) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j) (hp : IsPtAd A a j hj β x p) (hp₁ : IsPtAd A a j hj β x₁ p₁)
    (hx : ∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1)
    (P : SB t μ) : ∀ a b, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (LinearMap.toMatrix' ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm).toLinearMap a b -
        (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) t.X.E) a b)) := by
  set Q := seamP t.seam P.1 with hQdef
  have hQ : Q ∈ ssRec t u μ := (mem_ssRec t u μ P.1).2 (by rw [hTie.isChainTop.1]; classical exact Finset.mem_union.2 (Or.inr P.2))
  have hv : Q.under (𝓞 D.host.F) ∈ plUnder D.host.F (ssRec t u μ) := ⟨Q, hQ, rfl⟩
  have hag := loc_agree Q (hx _ hv)
  have c0 := congAt_loc Q _ _ (hp.frame P)
  have c1 := congAt_loc Q _ _ (hp₁.frame P)
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hq0 : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hπ0 : algebraMap D.host.E (Q.adicCompletion D.host.E) (((qOf Q : ℕ) : D.host.E) ^ (t.cst μ).D P) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap D.host.E _).injective]
    exact pow_ne_zero _ (by exact_mod_cast hq0)
  have hπ : Valued.v (algebraMap D.host.E (Q.adicCompletion D.host.E) (((qOf Q : ℕ) : D.host.E) ^ (t.cst μ).D P)) < 1 := by
    rw [val_alg, map_pow]
    refine pow_lt_one₀ zero_le' ?_ (by omega)
    have e : ((qOf Q : ℕ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E (qOf Q : 𝓞 D.host.E) := by rw [map_natCast]
    rw [e, HeightOneSpectrum.valuation_of_algebraMap]
    exact (Q.intValuation_lt_one_iff_mem _).2 (Ideal.absNorm_mem _)
  have key := inv_mul_cong _ hπ0 hπ _ _ c0 c1
  have hs : (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm =
      (frsF t.sel (t.tup μ) p P)⁻¹ * frsF t.sel (t.tup μ) p₁ P := by
    ext w; rfl
  have e : (locM Q (((ratA D.host.F) (A.crd j hj) * x.1 * (ratA D.host.F) (A.fb j hj β P))⁻¹ *
        (ratA D.host.F) ((seamGL t.seam) (frsF t.sel (t.tup μ) p P))))⁻¹ *
      locM Q (((ratA D.host.F) (A.crd j hj) * x₁.1 * (ratA D.host.F) (A.fb j hj β P))⁻¹ *
        (ratA D.host.F) ((seamGL t.seam) (frsF t.sel (t.tup μ) p₁ P))) =
      locM Q (ratA D.host.F (seamGL t.seam ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm))) := by
    rw [hs]
    simp only [map_mul, map_inv]
    rw [hag]
    group
  rw [e] at key
  intro a b
  have k := key a b
  obtain ⟨g, hg⟩ : ∃ g, g = (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm := ⟨_, rfl⟩
  rw [← hg] at k ⊢
  have ent : ((locM Q (ratA D.host.F (seamGL t.seam g)) : GL (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) :
      Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) a b =
      algebraMap D.host.E _ (t.seam.iE (LinearMap.toMatrix' g.toLinearMap a b)) := by
    show GlobalTheory.Mem.Col2.adAt D.host.F Q (inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (((seamGL t.seam g : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) a b)) = _
    rw [GlobalTheory.Mem.Col2.adAt_inclE]
    rfl
  have one : (1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) (Q.adicCompletion D.host.E)) a b =
      algebraMap D.host.E _ (t.seam.iE ((1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) t.X.E) a b)) := by
    exact one_entry Q t.seam.iE a b
  rw [Matrix.sub_apply, ent, one] at k
  have k2 := intAt_of_val Q _ _ _ k
  rw [hQdef, qOf_seamP, map_expr] at k2
  exact (intAt_seamP t.seam P.1 _).1 k2

end GlobalTheory.FrameAgree

namespace GlobalTheory.FrameAgree

theorem frame_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have h1 := core hTie j hj β x x₁ p p₁ hp hp₁ hx P
  have h2 := core hTie j hj β x₁ x p₁ p hp₁ hp (fun v hv => (hx v hv).symm) P
  have hsymm : ((frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm).symm =
      (frsF t.sel (t.tup μ) p P).trans (frsF t.sel (t.tup μ) p₁ P).symm := by
    ext w; rfl
  exact glint_of_cong P.1 ((t.cst μ).D P) _ h1 (by rw [hsymm]; exact h2)

end GlobalTheory.FrameAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  first | exact @GlobalTheory.LevOne.cong_mem_level_chr_one | exact GlobalTheory.LevOne.cong_mem_level_chr_one | (intros; apply GlobalTheory.LevOne.cong_mem_level_chr_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem errXS_pi_of_colT : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : GlobalTheory.Mem.Top.Bl.ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  intro B f T w Z t
  have hc : t.full.1.cols = t.C.herm := t.full.2
  refine ⟨?_, ?_⟩
  · show (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← t.C.piG]
    exact (t.std _).gl.piG
  · funext u
    show (t.full.1.cols.atT u).piU = _
    rw [hc, ← t.C.piU u]
    exact (t.std u).piU

end GlobalTheory.Svd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtAdeleMulOfPlaceComponentEqZero
section
open NumberField IsDedekindDomain

namespace GlobalTheory.VanishAtOver

theorem intAtA_mul_of_prV_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (Q : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v Q →
    ∀ a : TensorProduct F E (FiniteAdeleRing (𝓞 F) F), Formalism.UG.prV (E := E) v a = 0 →
    ∀ c : E, Formalism.L2.Col.IntAtA (F := F) Q (Formalism.L2.Col.iA F E c * a) := by
  intro F E _ _ _ _ _ v Q hv a ha c
  apply GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero
  intro w hw
  have hwv : w = v := HeightOneSpectrum.ext (hw.trans hv.symm)
  subst hwv
  rw [map_mul, ha, mul_zero]

end GlobalTheory.VanishAtOver
end

