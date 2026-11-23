module

public import Formalism.LocalToGlobal.Columns.Bundle0033
public import Formalism.LocalToGlobal.Columns.Bundle0029
public import Formalism.LocalToGlobal.Columns.HeckeSpCount
public import Formalism.LocalToGlobal.Columns.MemLocPOfSmul
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.XiTopTilRefHolds
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.RecPerFF
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

def zOfRow0 (σ₀ : X.K →+* ℂ) (hM : (rowGSD W ΛM).Ok) (F : (rowGSD W ΛM).EqFun) : Fin ((rowGSD W ΛM).hDim hM) → ℂ :=
  fun a => σ₀ (((rowGSD W ΛM).hB hM).repr F a)

end Gen

section Cast

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem levFam_eq_cast {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG')
    (A : LevFam E K n SG) (B : LevFam E K n SG') (h : ∀ (w : SG') (hw : w.1 ∈ SG), B w = A ⟨w.1, hw⟩) : B = e ▸ A := by
  subst e
  funext w
  exact h w w.2

variable {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
  (Λ' : LevFam X.E X.K (R.N R.m - 1) SG')

def rowCast (hΛ : Λ' = e ▸ A) (F : (formGSD (rowVal W SG') Λ').EqFun) : (rowGSD W A).EqFun := by
  subst hΛ
  subst e
  exact F

end Cast

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs)

theorem rowTy_inv_cast : (rowTy Ch sel mu P).inv = rcol_rowSG_eq sel mu hQ ▸ (rowTyG Ch P).inv := by
  refine levFam_eq_cast (rcol_rowSG_eq sel mu hQ) _ _ fun w hw => ?_
  first
  | (simp only [LevFam.inv, rowTy, LevFam.glue, dif_pos hw]; done)
  | (unfold LevFam.inv rowTy LevFam.glue; rw [dif_pos hw])
  | (simp [LevFam.inv, rowTy, LevFam.glue, hw])

def zOfRow (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) (F : MtildeV W Ch sel mu P) : Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ :=
  zOfRow0 W (rowTyG Ch P).inv σ₀ hM (rowCast W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P) F)

end Main

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQLat
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

theorem qdf_frExists : FrExists (n := n) ST SG Q := by
  intro d P
  first
  | exact DetChrL.frame_exists P.1 ((let d := d; _root_.Formalism.L2.Col.hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))
  | exact DetChrL.frame_exists P.1 d.2.lat

abbrev qPi (q : QLoc hc n Q Θ) (P : Q) : E ⊗[F] Formalism.L2.Herm.Af F →+* (qv F P.1).adicCompletion F :=
  ((RingHom.fst _ _).comp (q.sp P).toRingHom).comp (prV (E := E) (qv F P.1))

theorem qdf_at_val (q : QLoc hc n Q Θ) (P : Q) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    ((q.at P x : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) = (x : Matrix (Fin n) (Fin n) _).map (qPi q P) := rfl

theorem qdf_phi_int (q : QLoc hc n Q Θ) (P : Q) (r : 𝓞 E) : q.phi P (r : E) ∈ (qv F P.1).adicCompletionIntegers F := by
  have h : Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E (qv F P.1) :=
    Subring.subset_closure (Or.inl ⟨⟨(r : E), r, rfl⟩, rfl⟩)
  exact ((q.sp_int P _).1 h).1

theorem qdf_pi_int (q : QLoc hc n Q Θ) (P : Q) {a : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E) :
    qPi q P a ∈ (qv F P.1).adicCompletionIntegers F := by
  have hle : Formalism.L2.Herm.intAf F E ≤
      (Formalism.BasicNotions.intV E (qv F P.1)).comap (Formalism.UG.prV (E := E) (qv F P.1)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨y, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨x, ?_⟩))
      simp [Formalism.UG.prV]
    · have hy : ∀ v, (y : Formalism.L2.Herm.Af F) v ∈ v.adicCompletionIntegers F := y.2
      refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨⟨(y : Formalism.L2.Herm.Af F) (qv F P.1), hy _⟩, ?_⟩))
      simp [Formalism.UG.prV] <;> rfl
  exact ((q.sp_int P _).1 (hle ha)).1

theorem qdf_phi_unit (q : QLoc hc n Q Θ) (P : Q) {s : 𝓞 E} (hs : s ∉ P.1.asIdeal) :
    q.phi P (s : E) ≠ 0 ∧ (q.phi P (s : E))⁻¹ ∈ (qv F P.1).adicCompletionIntegers F := by
  have h1 : Valued.v (q.phi P (s : E)) ≤ 1 := qdf_phi_int q P s
  have h2 : ¬ Valued.v (q.phi P (s : E)) < 1 := fun h => hs ((q.sp_P P s).1 h)
  have hv : Valued.v (q.phi P (s : E)) = 1 := le_antisymm h1 (not_lt.1 h2)
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, map_zero] at hv
    exact zero_ne_one hv
  · show Valued.v (q.phi P (s : E))⁻¹ ≤ 1
    rw [map_inv₀, hv, inv_one]

theorem qdf_phi_intAt (q : QLoc hc n Q Θ) (P : Q) {a : E} (h : IntAt P.1 a) : q.phi P a ∈ (qv F P.1).adicCompletionIntegers F := by
  obtain ⟨r, s, hs, h⟩ := h
  have hu := qdf_phi_unit q P hs
  have hm : q.phi P (s : E) * q.phi P a = q.phi P (r : E) := by
    rw [← map_mul]
    exact congrArg (q.phi P) h
  have ha : q.phi P a = q.phi P (r : E) * (q.phi P (s : E))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hu.1, mul_comm]
    exact hm
  rw [ha]
  exact mul_mem (qdf_phi_int q P r) hu.2

theorem qdf_frLat (q : QLoc hc n Q Θ) : FrLat ST SG q := by
  intro x p hx P
  have hN : p.deco.1.N = Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n) := by
    rw [← hx, rlc_decoOf_val hc n ST SG x.2]; rfl
  set fr := p.fr P with hfr

  have hfrN : ∀ w ∈ p.deco.1.N, ∀ i, q.phi P ((fr.symm w) i) ∈ (qv F P.1).adicCompletionIntegers F := by
    intro w hw i
    have h1 : fr (fr.symm w) ∈ p.deco.1.at P.1 := by
      rw [LinearEquiv.apply_symm_apply]
      exact (mem_locP P.1 _ w).2 ⟨1, P.1.isPrime.one_notMem, by rw [one_smul]; exact hw⟩
    have h2 : fr.symm w ∈ stdAt E n P.1 := (p.2 P (fr.symm w)).1 h1
    exact qdf_phi_intAt q P ((mem_localization_standardLattice P.1 _).1 h2 i)
  have hFinv : ((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) = bc (q.phi P) (qGL n fr.symm) := by
    rw [← map_inv]; congr 1
  constructor
  ·
    set xm : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := x.1 with hxm
    have key : ∀ z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)), ∀ i,
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (z k))) i ∈
          (qv F P.1).adicCompletionIntegers F := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨w, hw, rfl⟩ := hz
        intro i
        rw [hFinv]
        have e1 : ((bc (q.phi P) (qGL n fr.symm) : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => qPi q P (iA F E (w k))) =
            fun k => q.phi P ((fr.symm w) k) := by
          funext k
          rw [← toGLm_mulVec fr.symm w]
          exact (RingHom.map_mulVec (q.phi P) _ w k).symm
        rw [e1]
        exact hfrN w (by rw [hN]; exact hw) i
      | zero =>
        intro i
        have e0 : (fun k => qPi q P ((0 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) k)) = 0 := by funext k; simp
        rw [e0, Matrix.mulVec_zero]
        exact zero_mem _
      | add z1 z2 _ _ h1 h2 =>
        intro i
        have e2 : (fun k => qPi q P ((z1 + z2) k)) = (fun k => qPi q P (z1 k)) + (fun k => qPi q P (z2 k)) := by
          funext k; simp
        rw [e2, Matrix.mulVec_add]
        exact add_mem (h1 i) (h2 i)
      | smul a z1 _ h1 =>
        intro i
        have e2 : (fun k => qPi q P ((a • z1) k)) = qPi q P (a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => qPi q P (z1 k)) := by
          funext k
          show qPi q P ((a : E ⊗[F] Formalism.L2.Herm.Af F) * z1 k) = _
          rw [map_mul]; rfl
        rw [e2, Matrix.mulVec_smul]
        exact mul_mem (qdf_pi_int q P a.2) (h1 i)
    intro i j
    have hz : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) ∈ Formalism.L2.Herm.hatL (F := F)
        (Formalism.UG.CS.globLat (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (stdLat E n)) := by
      have hspan : Submodule.span E (stdLat E n : Set (Sp E n)) = ⊤ := by
        apply top_unique
        rw [← (Pi.basisFun E (Fin n)).span_eq]
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        simpa using (single_mem_stdLat (E := E) (n := n) i 1)
      refine (Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin n) (stdLat E n)
        (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) hspan xm _).2 ?_
      have e3 : (((xm⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => (xm : Matrix (Fin n) (Fin n) _) k j) = fun k => iA F E ((Pi.single j (1 : E) : Sp E n) k) := by
        have : (fun k => (xm : Matrix (Fin n) (Fin n) _) k j) =
            (xm : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ Pi.single j (1 : E ⊗[F] Formalism.L2.Herm.Af F) := by
          funext k; rw [Matrix.mulVec_single_one]; rfl
        rw [this, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        funext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [Pi.single_apply, hk]
      rw [e3]
      exact Submodule.subset_span ⟨Pi.single j 1, by
        have := single_mem_stdLat (E := E) (n := n) j 1
        simpa using this, rfl⟩
    have := key _ hz i
    have e7 : ((((bc (q.phi P) (qGL n fr))⁻¹ * q.at P xm : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j) =
        ((((bc (q.phi P) (qGL n fr))⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
          fun k => qPi q P ((xm : Matrix (Fin n) (Fin n) _) k j)) i := by
      rw [Units.val_mul, qdf_at_val]; rfl
    rw [e7]
    exact this
  ·
    intro i j
    have e0 : (((bc (q.phi P) (qGL n fr))⁻¹ * q.at P x)⁻¹ : GL (Fin n) _) = (q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) := by
      rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    have hcol : fr (Pi.single j 1) ∈ p.deco.1.at P.1 :=
      (p.2 P (Pi.single j 1)).2 ((mem_localization_standardLattice P.1 _).2 fun k => ⟨if k = j then 1 else 0, 1, P.1.isPrime.one_notMem, by
        by_cases hk : k = j <;> simp [Pi.single_apply, hk]⟩)
    obtain ⟨s, hs, hsN⟩ := (mem_locP P.1 _ _).1 hcol
    rw [hN] at hsN
    have hpull := (mem_globLat x.1 (s • fr (Pi.single j 1))).1 hsN
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hs
    have e4 : ((((q.at P x)⁻¹ * bc (q.phi P) (qGL n fr) : GL (Fin n) _)) : Matrix (Fin n) (Fin n) _) i j =
        (q.phi P (s : E))⁻¹ * qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) := by
      have e5 : qPi q P (pullV x.1 (s • fr (Pi.single j 1)) i) =
          ((((q.at P x)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun k => q.phi P ((s • fr (Pi.single j 1)) k)) i := by
        unfold pullV
        rw [RingHom.map_mulVec, ← qdf_at_inv, qdf_at_val]
        rfl
      rw [e5]
      have e6 : (fun k => q.phi P ((s • fr (Pi.single j 1)) k)) = q.phi P (s : E) • fun k => q.phi P ((fr (Pi.single j 1)) k) := by
        funext k
        simp [Submodule.smul_def, Algebra.smul_def]
      rw [e6, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul, Units.val_mul,
        Matrix.mul_apply]
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
    rw [e4]
    exact mul_mem hinv (qdf_pi_int q P (hpull i))

variable {H : Subgroup (GLG (E := E) (n := n) (SG := SG))}

end QLat

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TopG

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure TopNum (R : Ranks) (i : ℕ) : Prop where
  a_eq : R.r + (i + 1 - 1) * R.t = R.N i
  a_le : R.r + (i + 1 - 1) * R.t ≤ (R.N (i + 1) - 1) + 0
  c0 : cOf R i = 0

theorem topNum_of {m2 : ℕ} (hm : R.m = m2 + 2) : TopNum R (m2 + 1) := by
  have h := xt_a_eq (R := R) hm
  have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
  rw [e] at h
  refine ⟨h, ?_, xt_cOf hm⟩
  rw [h]
  unfold Ranks.N
  have e2 : (m2 + 1 + 1) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
  omega

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xtPhiTopG_congr (hX : X.Ok) (hPr : Pr.Ok) {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hD : ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x' = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTopG
  rw [ite_eq_left hP]
  cases sharp
  · simp only [Bool.false_eq_true, ite_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [ite_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')

theorem xtPhiTopG_int {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0)) (h : PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x ≠ 0) :
    ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i →
      IntAt P (LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  unfold PhiTopG at h
  rw [ite_eq_left hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, ite_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (hn.a_eq.symm ▸ hp')
  · simp only [ite_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (hn.a_eq.symm ▸ hp')

def topDat (i : ℕ) (P : rowSG Pr sel mu) (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y) y''

theorem XiTop_eq {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x *
      ∏ P : rowSG Pr sel mu, topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem xt_last_lt (R : Ranks) (j : ℕ) : R.N j - 1 < R.N j := by have := R.N_pos j; omega

theorem xt_atNL (j : ℕ) (a : Sp X.E (R.N j)) : atNL X.E (R.N j) (R.N j - 1) a = a ⟨R.N j - 1, xt_last_lt R j⟩ := by
  unfold atNL
  rw [dite_eq_left (xt_last_lt R j)]
  rfl

theorem xt_split {P : HeightOneSpectrum (𝓞 X.E)} (j : ℕ) (a : Sp X.E (R.N j)) :
    (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prXpG X.E (R.N j) a i)) ∧ IntAt P (atNL X.E (R.N j) (R.N j - 1) a) := by
  rw [xt_atNL]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.1 < R.N j - 1
    · exact h1 ⟨i.1, by omega⟩
    · have : i = ⟨R.N j - 1, xt_last_lt R j⟩ := Fin.ext (by show i.1 = R.N j - 1; have := i.2; omega)
      rw [this]
      exact h2

theorem topDat_congr (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y y₁ : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (hy : ∀ j, IntAt P.1 ((qOf P.1 : X.E) * y'' j))
    (H : ∀ j : Fin (R.N i), ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) ↔ ∀ l, IntAt P.1 (y₁ (Pi.single j 1) l)) ∧
      ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) → ∀ l, redP P.1 (y (Pi.single j 1) l) = redP P.1 (y₁ (Pi.single j 1) l))) :
    topDat Ch sel mu cst i P y y'' = topDat Ch sel mu cst i P y₁ y'' := by
  classical
  have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R i)
    (n' := R.N i) (n := R.N (i + 1) - 1) (N := R.N (i + 1)) hn.c0 (PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1)
    (fun x x' h => xtPhiTopG_congr Ch mu hX hPr hn cst.sharp hP x x' h) (fun x h => xtPhiTopG_int Ch mu hn cst.sharp hP x h)
    (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXpG X.E (R.N (i + 1))) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1))
    (fun a => xt_split (i + 1) a) y (prXpG X.E (R.N (i + 1)) ∘ₗ y₁) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y₁)
    (fun j => ⟨(H j).1.trans (xt_split (i + 1) _), fun hall => ⟨fun l => (H j).2 hall _, by
      show redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _) = redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _)
      rw [xt_atNL, xt_atNL]
      exact (H j).2 hall _⟩⟩) y'' hy
  unfold topDat ftY
  rw [ite_eq_left hP, ite_eq_left hP]
  exact key

theorem topDat_int {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (h : topDat Ch sel mu cst i P y y'' ≠ 0) (j : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 (y (Pi.single j 1) l) := by
  classical
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  refine (xt_split (i + 1) (y (Pi.single j 1))).2 ⟨fun l => ?_, ?_⟩ l
  · have := xtPhiTopG_int Ch mu hn cst.sharp hP _ h1 l.1 j.1 l.2 j.2
    rwa [xtEntB hn.c0 _ (by have := l.2; omega) j.2, LinearMap.comp_apply, LinearMap.comp_apply, xtRes j.2] at this
  · unfold ftY at h2
    rw [ite_eq_left hP] at h2
    by_contra h3
    exact h2 (ite_eq_right fun hh => h3 (hh j))

end TopG

end Formalism.L2.Col
end
end

