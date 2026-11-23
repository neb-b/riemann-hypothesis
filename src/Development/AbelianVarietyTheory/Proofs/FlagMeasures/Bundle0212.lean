module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbedding
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (G : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (G : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ G := by
  first
  | exact @_root_.GlobalTheory.DenominatorTheorem.main_theorem
  | exact _root_.GlobalTheory.DenominatorTheorem.main_theorem
  | (apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorTheorem.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorTheorem.main_theorem ..)

theorem mem_locFlag_of_smul (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) {c : 𝓞 E} (hc : c ≠ 0) {y : Fin n → E}
    (hy : c • y ∈ F b) : (P⁻¹ *ᵥ fun l => φ (y l)) ∈ locFlag φ P F b := by
  have hc1 : φ (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc
  have e : (fun l => φ (y l)) = (φ (algebraMap (𝓞 E) E c))⁻¹ • fun l => φ ((c • y) l) := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  rw [e, Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

omit [NumberField E] in
theorem mulVec_mem_of_span (φ : E →+* ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (S : Set (Fin n → E))
    (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ S, (Q *ᵥ fun l => φ (y l)) ∈ W) {u : Fin n → ℂ}
    (hu : u ∈ Submodule.span ℂ ((fun w : Fin n → E => fun i => φ (w i)) '' S)) : Q *ᵥ u ∈ W := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact h y hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem _ hx

theorem form_frame {P K M : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * K * P = M)
    (u v : Fin n → ℂ) : star (P⁻¹ *ᵥ u) ⬝ᵥ (M *ᵥ v) = star u ⬝ᵥ (K *ᵥ (P *ᵥ v)) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]

omit [NumberField E] in
theorem form_emb [StarRing E] (φ : E →+* ℂ) (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x))
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    star (fun l => φ (x l)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) = φ (star x ⬝ᵥ (J *ᵥ y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ]

theorem locDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  intro E _ _ _ n m J φ P ε F hφ hP hJ hF hsp
  classical
  obtain ⟨hmono, h0, hm, hd⟩ := hF
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hinv : ∀ z : Fin n → ℂ, P⁻¹ *ᵥ (P *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hinv' : ∀ z : Fin n → ℂ, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have htop : locFlag φ P F m = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [← hinv z]
    refine mulVec_mem_of_span φ _ _ _ ?_
      (GlobalTheory.PerpBaseChange.mem_span_of_forms φ ∅ (P *ᵥ z) (by simp))
    intro y _
    obtain ⟨c, hc, hy⟩ := exists_smul_mem _ hsp y
    exact mem_locFlag_of_smul φ P F m hc hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, htop⟩
  · intro a b hab
    exact Submodule.span_mono (Set.image_mono (hmono hab))
  · unfold locFlag
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have : y = 0 := by simpa using hy
    subst this
    have e : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    simp only [e, Matrix.mulVec_zero]
  · intro b hb
    unfold locFlag
    rw [hm b hb]
  · intro b hb z
    constructor
    · intro hz
      refine ⟨by rw [htop]; trivial, fun x hx => ?_⟩
      induction hz using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        induction hx using Submodule.span_induction with
        | zero => simp
        | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
        | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]
        | mem a ha =>
          obtain ⟨v, hv, rfl⟩ := ha
          rw [form_frame hP hJ, hinv', form_emb φ hφ, ((hd b hb y).1 hy).2 v hv, map_zero]
    · rintro ⟨-, hz⟩
      rw [← hinv z]
      let f : (Fin n → E) → Module.Dual E (Fin n → E) := fun x =>
        { toFun := fun y => star x ⬝ᵥ (J *ᵥ y)
          map_add' := fun y y' => by rw [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c y => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }
      have hf : ∀ x y, f x y = star x ⬝ᵥ (J *ᵥ y) := fun _ _ => rfl
      refine mulVec_mem_of_span φ _ _ _ ?_
        (GlobalTheory.PerpBaseChange.mem_span_of_forms φ (f '' (F b : Set _)) (P *ᵥ z) ?_)
      · intro y hy
        obtain ⟨c, hc, hcy⟩ := exists_smul_mem _ hsp y
        refine mem_locFlag_of_smul φ P F _ hc ((hd b hb _).2 ⟨hcy, fun x hx => ?_⟩)
        have h1 : star x ⬝ᵥ (J *ᵥ y) = 0 := hy (f x) ⟨x, hx, rfl⟩
        rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := hz _ (Submodule.subset_span ⟨x, hx, rfl⟩)
        rw [form_frame hP hJ] at h1
        rw [← h1]
        generalize P *ᵥ z = u
        simp only [hf, Matrix.mulVec_single_one]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ, Finset.sum_mul, Finset.mul_sum,
          Pi.star_apply, Matrix.map_apply, Matrix.col_apply, mul_assoc]
        rw [Finset.sum_comm]
        rfl

end GlobalTheory.LocDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagPieceHeights
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private theorem hform_eq_dotProduct_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (s y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J s y = star s ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem pieceHt_dualFlag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), IsDualFlag I.J F (2 * a + 1) → F (2 * a + 1) = lamX I (1, xf) → (∀ i : Fin (a + 1), F i = S i) → (∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ∧ pieceHt (frm I (1, xf)) F i = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) ∧ pieceHt (frm I (1, xf)) F (2 * a - i) = (Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i))⁻¹) ∧ pieceHt (frm I (1, xf)) F a = 1 ∧ ∀ b, 2 * a + 1 ≤ b → pieceHt (frm I (1, xf)) F b = 1 := by
  intro I xf a j hj S hS F hF hFm hFS
  have hmaj := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  haveI : IsTotallyComplex I.E := hmaj.1
  have hf : Formalism.HN.nPl I.E = I.f := hmaj.2.1
  have hX : ∀ w, IsUnit (frm I (1, xf) w).det := fun w => GlobalTheory.Count.FrameMajorant.frm_unit I (1, xf) w
  have hΛfg : (lamX I (1, xf)).FG := (GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.1
  have hmain := GlobalTheory.Count.PerpStep.main I (1, xf)
  have hht1 : Formalism.HN.ht (bas I) (frm I (1, xf)) (lamX I (1, xf)) = 1 := hmain.1
  have hperp := hmain.2.2.2
  have hfg : ∀ N : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) → N.FG := by
    intro N hN
    haveI := isNoetherian_of_fg_of_noetherian _ hΛfg
    have h1 : (N.comap (lamX I (1, xf)).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (lamX I (1, xf)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h2

  have hrat : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      Formalism.HN.ht (bas I) (frm I (1, xf)) N / Formalism.HN.ht (bas I) (frm I (1, xf)) T =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX N (hfg N hN),
      GlobalTheory.Count.PerpStep.ht_eq (bas I) (frm I (1, xf)) hX T (hfg T (hT.1.trans hN)),
      GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT, ← Real.exp_sub]
    congr 1
    ring
  have hqpos : ∀ N T : Submodule (𝓞 I.E) (Fin I.n → I.E), N ≤ lamX I (1, xf) →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) N T →
      0 < Formalism.HN.htQ (bas I) (frm I (1, xf)) N T := by
    intro N T hN hT
    rw [GlobalTheory.Count.PerpStep.htQ_eq (bas I) (frm I (1, xf)) hX N T (hfg N hN) hT]
    exact Real.exp_pos _

  have hdual : ∀ b, b ≤ 2 * a + 1 → perpIn I (1, xf) (F b) = F (2 * a + 1 - b) := by
    intro b hb
    ext y
    rw [GlobalTheory.Count.PerpStep.perpIn_eq, GlobalTheory.Count.PerpStep.mem_perp, hF.2.2.2 b hb y, hFm]
    refine and_congr_right fun _ => forall₂_congr fun s _ => ?_
    rw [hform_eq_dotProduct_mulVec]

  have hsatS : ∀ i : Fin (a + 1),
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (S i) := by
    intro i
    have h := GlobalTheory.Count.PerpStep.sat_inf (bas I) (frm I (1, xf)) hX (lamX I (1, xf)) hΛfg
      (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    convert h using 1
    ext y
    rw [Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact hS.2.2.2.1 i y
  have hsatF : ∀ b, b ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (lamX I (1, xf)) (F b) := by
    intro b hb
    by_cases hba : b ≤ a
    · have e : F b = S ⟨b, by omega⟩ := hFS ⟨b, by omega⟩
      rw [e]
      exact hsatS _
    · have e : F (2 * a + 1 - b) = S ⟨2 * a + 1 - b, by omega⟩ := hFS ⟨2 * a + 1 - b, by omega⟩
      have h := (hperp (F (2 * a + 1 - b)) (F (2 * a + 1 - b)) (by rw [e]; exact hsatS _)
        (by rw [e]; exact hsatS _) le_rfl).1
      rwa [hdual _ (by omega), show 2 * a + 1 - (2 * a + 1 - b) = b by omega] at h
  have hpiece : ∀ b, b + 1 ≤ 2 * a + 1 →
      pieceHt (frm I (1, xf)) F b = Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (b + 1)) (F b) := by
    intro b hb
    unfold pieceHt
    exact hrat _ _ (hsatF _ hb).1
      (GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
        (hF.1 (Nat.le_succ b)) (hsatF _ hb).1)
  have hsat' : ∀ b, b + 1 ≤ 2 * a + 1 →
      Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I (1, xf))) (F (b + 1)) (F b) := fun b hb =>
    GlobalTheory.Count.PerpStep.sat_mono (bas I) (frm I (1, xf)) (hsatF b (by omega))
      (hF.1 (Nat.le_succ b)) (hsatF _ hb).1
  refine ⟨fun i => ?_, ?_, fun b hb => ?_⟩
  · have hi := i.isLt
    have hFi : F i = S i.castSucc := by simpa using hFS i.castSucc
    have hFi1 : F (i + 1) = S i.succ := by simpa using hFS i.succ
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' i (by omega))
    rw [hFi1, hFi] at hq
    have hrk : ((Formalism.HN.rkK (S i.succ) : ℝ) - Formalism.HN.rkK (S i.castSucc)) = j i := by
      rw [hS.2.2.1 i]
      push_cast
      ring
    have hjpos : (0 : ℝ) < j i := by exact_mod_cast hj i
    have hfpos : (0 : ℝ) < I.f := by
      rw [← hf]
      exact_mod_cast Fintype.card_pos
    have hsz : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^
          ((1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ))) := by
      unfold Formalism.HN.sizeQ
      rw [hrk, hf]
    have hpow : Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ (2 * I.f * j i) =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hsz, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]
      have hc : (1 : ℝ) / (2 * (I.f : ℝ) * (j i : ℝ)) * ((2 * I.f * j i : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [hc, Real.rpow_one]
    have hpi : pieceHt (frm I (1, xf)) F i =
        Formalism.HN.htQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) := by
      rw [hpiece i (by omega), hFi1, hFi]
    refine ⟨by rw [hsz]; exact Real.rpow_pos_of_pos hq _, by rw [hpi, hpow], ?_⟩
    rw [hpow, hpiece (2 * a - i) (by omega)]
    have hPi := hdual i (by omega)
    have hPi1 := hdual (i + 1) (by omega)
    rw [show 2 * a + 1 - i = 2 * a - i + 1 by omega] at hPi
    rw [show 2 * a + 1 - (i + 1) = 2 * a - i by omega] at hPi1
    have h := (hperp (F i) (F (i + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPi, hPi1, hFi1, hFi] at h
    exact h
  · have hPa := hdual a (by omega)
    have hPa1 := hdual (a + 1) (by omega)
    rw [show 2 * a + 1 - a = a + 1 by omega] at hPa
    rw [show 2 * a + 1 - (a + 1) = a by omega] at hPa1
    have h := (hperp (F a) (F (a + 1)) (hsatF _ (by omega)) (hsatF _ (by omega))
      (hF.1 (Nat.le_succ _))).2.2.2.2
    rw [hPa, hPa1] at h
    have hq := hqpos _ _ (hsatF _ (by omega)).1 (hsat' a (by omega))
    rw [hpiece a (by omega)]
    set q := Formalism.HN.htQ (bas I) (frm I (1, xf)) (F (a + 1)) (F a) with hqdef
    have hmul : q * q = 1 := by
      calc q * q = q⁻¹ * q := by rw [← h]
        _ = 1 := inv_mul_cancel₀ hq.ne'
    nlinarith
  · unfold pieceHt
    rw [hF.2.2.1 (b + 1) (by omega), hF.2.2.1 b hb, hFm, hht1]
    norm_num

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
section
open Formalism.MainNotions Formalism.BasicNotions Filter

namespace GlobalTheory

theorem sizes_large_of_power_bounds {D : D7} (L : SizeData₂ D) (h : SizesAt L) (M : ℝ)
    (h1 : M ≤ L.sc.x ^ (1 / 4 : ℝ)) (h2 : M ≤ L.sc.x ^ L.sc.eps)
    (h3 : 5 * |M| * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps) :
    M ≤ (D.R.m : ℝ) ∧ M ≤ L.sc.L ∧ (D.R.k : ℝ) ^ M ≤ L.sc.b ∧ D.host.rdE ≤ L.sc.b ∧
      (D.R.k : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) := by
  obtain ⟨-, hM, hK, -, hT, hC, hQ, -, -, -, -, -, -, -, -, -, hD, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hL0 : 0 ≤ L.sc.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL0
  refine ⟨?_, h2, ?_, ?_, ?_⟩
  · refine h1.trans (le_trans ?_ hM.1)
    have e : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 + -(L.sc.eps / 8)) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
      rfl
    rw [e, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    linarith
  · have hk1 : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := by
      refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
      unfold szTh
      linarith
    calc (D.R.k : ℝ) ^ M ≤ (D.R.k : ℝ) ^ |M| := Real.rpow_le_rpow_of_exponent_le hk1 (le_abs_self M)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |M| := Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg M)
      _ = Real.exp (5 * |M| * Real.log L.sc.x) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ L.sc.b := Real.exp_le_exp.mpr h3
  · have hr := hQ.2.2.2.2.2.2.2
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
      have hn : ∀ n : ℕ, Real.sqrt n ≤ n := by
        intro n
        rw [Real.sqrt_le_left (by positivity)]
        exact_mod_cast Nat.le_self_pow two_ne_zero n
      exact_mod_cast hn (D.host.q * D.host.d)
    have hn0 : (0 : ℝ) ≤ D.R.n := by positivity
    have hqd : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by positivity
    have hc : D.host.rdE ≤ szCond L := by
      unfold szCond
      nlinarith [mul_le_mul_of_nonneg_left hs hn0, mul_nonneg hn0 hqd]
    refine hc.trans ?_
    rcases le_total (szCond L) 1 with h | h
    · exact h.trans hb1
    · have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
      calc szCond L ≤ szCond L ^ 36 := le_self_pow₀ h (by norm_num)
        _ ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) ht
        _ ≤ Real.sqrt L.sc.b := hC
        _ ≤ L.sc.b := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  · refine le_trans ?_ hD.1
    have : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    gcongr

theorem family_sizes_eventually_large : ∀ (eps : ℝ) (Fm : FamP eps) (M : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Fm.x1 < x ∧ M ≤ ((Fm.D x i).R.m : ℝ) ∧ M ≤ (Fm.L x i).sc.L ∧ ((Fm.D x i).R.k : ℝ) ^ M ≤ (Fm.L x i).sc.b ∧ (Fm.D x i).host.rdE ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * ((Fm.D x i).R.m : ℝ) ^ 10 ≤ ((Fm.D x i).s.Del : ℝ) := by
  intro eps Fm M
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  have e1 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop M
  have e2 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ eps := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have e3 : ∀ᶠ x : ℝ in atTop, 5 * |M| * Real.log x ≤ x ^ eps := by
    have := ((isLittleO_log_rpow_atTop he).const_mul_left (5 * |M|)).bound one_pos
    filter_upwards [this, eventually_ge_atTop 0] with x hx h0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)] at hx
    exact (le_abs_self _).trans hx
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and (eventually_gt_atTop Fm.x1))))
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 x hx
  refine ⟨a4, sizes_large_of_power_bounds (Fm.L x i) (Fm.sizes x a4 i) M ?_ ?_ ?_⟩ <;>
    simp only [Fm.L_x x i a4, Fm.L_eps x i] <;> assumption

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPieces

theorem sizesLe_stepLe (I : AutInst) (x : I.GA) {t : ℝ} (ht : 0 < t)
    (A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) : SizesLe I x (stepLe I x t) A' t := by
  intro N _ hN hne
  have hle : stepLe I x t ≤ lamX I x := GlobalTheory.PointFlag.stepLe_le I x t
  have hne0 : stepLe I x t ≠ ⊥ := by
    intro h0
    apply hne
    rw [h0] at hN ⊢
    exact le_bot_iff.mp hN.1
  exact (GlobalTheory.PointFlag.sizeQ_le I x hle hN hne).trans ((_root_.GlobalTheory.CountSteps.steps I x t ht).2.2.2.2.1 hne0)

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun y hy => hy.1
  · intro y hy
    apply Submodule.subset_span
    refine ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).mp hs]
    simp [Formalism.UG.hform]

theorem flag_pieces : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  intro I x a S τ hF
  have h35 := _root_.GlobalTheory.Count.PerpStep.main I x
  have h34 := (_root_.GlobalTheory.PointFlag.flag_spec I x).2.2 a S τ hF
  have hsat : ∀ m, SatX I x (S m) := fun m => GlobalTheory.PointFlag.flag_sat hF m
  have hperpLast : perpIn I x (S (Fin.last a)) = stepLe I x 2 := by
    rw [hF.2.2.1, (h35.2.2.1 (1 / 2) (by norm_num)).2]
    norm_num
  have hle_last : ∀ i, S i ≤ S (Fin.last a) := fun i => hF.2.1.monotone (Fin.le_last i)
  have hlast_le : S (Fin.last a) ≤ stepLe I x 2 := by
    rw [hF.2.2.1]
    exact (GlobalTheory.PointFlag.stepLt_le_stepLe I x _).trans (GlobalTheory.PointFlag.stepLe_mono I x (by norm_num))
  refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
  · have hp := h35.2.2.2 (S i) (S i) (hsat i) (hsat i) le_rfl
    have hp' := h35.2.2.2 (S i) (S (Fin.last a)) (hsat i) (hsat _) (hle_last i)
    refine ⟨hsat i, hp.1, ?_, hp'.2.2.2.1, hp.2.1⟩
    rw [hperpLast]
    exact (hle_last i).trans hlast_le
  · rw [hF.1]
    exact GlobalTheory.FlagPieces.perpIn_bot I x
  · rw [hperpLast]
    exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (by norm_num) _
  · obtain ⟨hcs, _, hlarge, hge, hlei⟩ := h34.1 i
    obtain ⟨hτpos, _, hsucc, _⟩ := hF.2.2.2.2.1 i
    have hsuccle : S i.succ ≤ lamX I x := by
      rw [hsucc]
      exact GlobalTheory.PointFlag.stepLe_le I x _
    refine ⟨?_, hlei, ?_, ?_, hlarge.le, ?_⟩
    · intro N hlt hle
      exact hge N hlt (hle.trans hsuccle)
    · rw [hcs, hsucc, (h35.2.2.1 _ hτpos).1, (h35.2.2.1 _ hτpos).2]
      exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (inv_pos.mpr hτpos) _
    · intro h
      have hlt : S i.castSucc < S i.succ := hF.2.1 (Fin.castSucc_lt_succ ..)
      rw [h] at hlt
      exact not_lt_bot hlt
    · split_ifs with h
      · have e : (⟨(i : ℕ) + 1, h⟩ : Fin a).castSucc = i.succ := Fin.ext (by simp)
        have hn := (h34.1 ⟨(i : ℕ) + 1, h⟩).2.2.2.1
        rw [e] at hn
        intro N hlt hle
        exact hn N hlt hle
      · have hi := i.isLt
        have e : i.succ = Fin.last a := Fin.ext (by simp; omega)
        rw [e, hF.2.2.1]
        intro N hlt hle
        exact (_root_.GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hlt hle

end GlobalTheory.FlagPieces
end

