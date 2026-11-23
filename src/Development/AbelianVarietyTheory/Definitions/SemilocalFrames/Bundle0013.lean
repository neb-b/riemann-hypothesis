module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AbsOfRange
section
noncomputable section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal
namespace GlobalTheory.Amp.RangeModel

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem sizes_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) (hb : D.host.rdE ≤ large₂.sc.b)
    (h : HypZ D large₂ C' Cl Cg cb Cu cT CT C0) : Sizes D large₂ Cl Cg CT := by
  obtain ⟨⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, hg1', hg2, hg2', -, -, -, hv, -, -, hgap, hT, hCl, hCl0⟩, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb1 : 1 < large₂.sc.b := lt_trans (by simpa using Real.exp_lt_exp.2 (zero_lt_one (α := ℝ))) hbe
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h8 : (1 : ℝ) ≤ (D.R.k * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 1 ≤ gg D := by unfold gg; nlinarith
  have hu : ∀ w τ, StrictAnti (uS D w τ) := fun w τ => by
    have hk0 : D.R.k = (D.R.k - 1) + 1 := by have := D.R.m_add_three_le_k; omega
    have key : ∀ (i : ℕ) (hi : i + 1 < D.R.k), uS D w τ ⟨i + 1, hi⟩ < uS D w τ ⟨i, by omega⟩ := fun i hi => by
      have a := (D.hcW w τ).u_gt_v ⟨i, by omega⟩
      have b := (D.hcW w τ).v_gt_u ⟨i, by omega⟩
      unfold uS; exact_mod_cast b.trans a
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih => exact (key c hc).trans (ih (by omega) hc')
  refine ⟨hL, Real.log_exp _, hbe, hm, hr, D.what₂.card_Tau, hCl, hmf.trans hfk, hv, hrd, rfl, hrd ▸ hb, hgg, ?_, ?_, ?_,
    fun w => (hT w).2, fun w τ => ⟨vand_pos (hu w τ), ?_⟩, ?_⟩
  · rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1' hg2' (by linarith) (by linarith)
  · have : large₂.sc.b ^ (8 : ℝ) ≤ large₂.sc.b ^ Cg := by
      refine le_trans ?_ (hg1.trans hg1')
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) 8
    exact (Real.rpow_le_rpow_left_iff hb1).1 this
  · refine le_trans ?_ (hg1.trans hg1')
    exact le_trans (by nlinarith) (le_self_pow₀ hkb (by norm_num))
  · have h1 : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    have h2 : 0 < D.host.rdE := by linarith
    have h3 : 0 < gg D := by linarith
    have h4 : 0 < VV D τ := mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)
    have h5 := vand_pos (hu w τ)
    unfold Tcrit; positivity
  · intro τ
    have hp : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by positivity
    have key : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1),
        Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := fun i hi => by
      have := hgap τ ⟨i, by omega⟩ (by simpa [hr] using hi)
      have h0 : (0 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 10 := by positivity
      exact lt_of_le_of_lt (le_add_of_nonneg_right h0) this
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih =>
      have := key c hc
      have := ih (by omega) hc'
      linarith

theorem theta_pos (D : D7) (τ w w') (θ : ℝ) (W : LocW D.R.k D.R.rS) (h : GoodW D τ w w' θ W) : 0 < θ := by
  by_contra hθ
  obtain ⟨-, -, -, -, -, -, hG, -, -, -, -, hN, hq, -⟩ := h
  have hv : 0 ≤ D.host.v := by unfold Host.v Host.rdE; positivity
  have h0 : kapN D θ = 0 := ENNReal.ofReal_eq_zero.2
    (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith) _) (not_lt.1 hθ))
  have hN0 : W.μN = 0 := by rw [hN, h0]; simp [haarLie]
  have := hq (fun _ => 1) measurable_const
  simp [muS, hN0] at this
  exact hG.2.1 this

end GlobalTheory.Amp.RangeModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Uni {K : Type} [Zero K] [One K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

def Chg {K W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f : Fin n → W)
    (A : Matrix (Fin n) (Fin n) K) (g : Fin n → W) : Prop :=
  ∀ b, g b = ∑ a, A a b • f a

def Tri (K : Type) {W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f g : Fin n → W) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) K, Uni A ∧ Chg f A g

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

def move (g : V ≃ₗ[E] V) (t : Term V M r) : Term V M r where
  abelian₂ := img g t.abelian₂
  f b := g (t.f b)
  f' b := g (t.f' b)
  T := t.T
  T' := t.T'

def Over {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r) : Prop :=
  ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ ∃ d' : Datum P, Datum.Rel d d' ∧ IsTermOver P d' (move g t)

def NU (H : HermSp M V) (f : Fin (r + 1) → V) : Set (V ≃ₗ[E] V) :=
  {n | IsUnitary H n ∧
    (∀ a : Fin r, n (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
    ∀ v ∈ H.perp (H.X f), n v - v ∈ H.X f}

def Cong (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V) (x : V) : Prop :=
  ∃ a ∈ H.smulLat (algebraMap F E (theta M)) Λ, ∃ b ∈ Λ, ∃ c ∈ Λ, b ∈ H.X f ∧ c ∈ H.X f' ∧ x = a + b + c

end Loc

section Glob

variable {D : D7}

def scaled (Z : LocDat D) (p : PlF D) (f : Fin (D.R.rS + 1) → (VS D).V) : Fin (D.R.rS + 1) → Vp D p :=
  fun a => frFac Z.δ p a • baseChange₂ D p (f a)

def locU (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ) : Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := frFac Z.δ p a • baseChange₂ D p (frame F a)
  f' b := frFac Z.δ p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

def AtBase (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (Tn T'n : ℕ) (P : LocNG.FPair (locH Z p) D.R.rS) : Prop :=
  P.A.f = scaled Z p (frame F) ∧ P.B.f = scaled Z p (frame F') ∧
    P.A.T = (Tn : (D.s.atP p).Fp) ∧ P.B.T = (T'n : (D.s.atP p).Fp)

def Ext (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Prop :=
  ∀ x, g (baseChange₂ D p x) = baseChange₂ D p (γ x)

end Glob

end GlobalTheory.LocOver
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass

abbrev HCo (a : ℕ) : Type := (Fin a → ℝ) × ({p : Fin a × Fin a // p.1 < p.2} → ℂ)

def hOf {a : ℕ} (t : HCo a) : Matrix (Fin a) (Fin a) ℂ := fun i j =>
  if h : i < j then t.2 ⟨(i, j), h⟩ else if h' : j < i then star (t.2 ⟨(j, i), h'⟩) else (t.1 i : ℂ)

abbrev Tup (k r a : ℕ) : Type := Fin (2 * r + k + 1) → Fin a → ℂ

def gramC {k r a : ℕ} (X : Tup k r a) : Matrix (Fin a) (Fin a) ℂ :=
  (Matrix.of X)ᴴ * Hpk k r * Matrix.of X

def DefPerp {k r a : ℕ} (X : Tup k r a) : Prop :=
  (gramC X).det ≠ 0 ∧ PosOnPerp (Hpk k r) (Matrix.of X)

def DefGram (k r a : ℕ) : Set (HCo a) := {t | ∃ X : Tup k r a, gramC X = hOf t ∧ DefPerp X}

def IsGramConst (k r a : ℕ) (μ : Measure (Mt k r)) (C : ℝ) : Prop :=
  0 < C ∧ ∀ Φ : Tup k r a → ℝ≥0∞, Measurable Φ → ∀ s : HCo a → Tup k r a,
    (∀ t ∈ DefGram k r a, gramC (s t) = hOf t) →
    (2 : ℝ≥0∞) ^ ((2 * r + k + 1) * a) * ∫⁻ X in {X | DefPerp X}, Φ X =
      (2 : ℝ≥0∞) ^ (a * (a - 1) / 2) * ∫⁻ t in DefGram k r a,
        ENNReal.ofReal (C * ‖(hOf t).det‖ ^ (2 * r + k + 1 - a)) *
          ∫⁻ g, Φ (Matrix.of.symm (Matrix.of g * Matrix.of (s t))) ∂μ

section Glob

variable {E : Type} [Field E] [NumberField E]

def tupLat {n a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (P : Matrix (Fin n) (Fin a) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin a) (x : E), x ∈ 𝔞 b ∧ v = x • fun i => P i b}

def dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (T : Matrix (Fin a) (Fin a) E) :
    Submodule (𝓞 E) (Fin a → E) :=
  Submodule.span (𝓞 E) {x | ∀ y ∈ tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E),
    form σ T x y ∈ (algebraMap (𝓞 E) E).range}

theorem mem_dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) (x : Fin a → E) :
    x ∈ dualM σ 𝔞 T ↔ ∀ y ∈ tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E),
      form σ T x y ∈ (algebraMap (𝓞 E) E).range := by
  refine ⟨fun hx => ?_, fun hx => Submodule.subset_span hx⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro y _; simp [form]
  | add x x' _ _ h h' =>
    intro y hy
    have : form σ T (x + x') y = form σ T x y + form σ T x' y := by
      simp [form, Matrix.mulVec_add]
    rw [this]; exact add_mem (h y hy) (h' y hy)
  | smul c x _ h =>
    intro y hy
    have : form σ T (c • x) y = algebraMap (𝓞 E) E c * form σ T x y := by
      rw [← algebraMap_smul E c x, form, form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
    rw [this]; exact mul_mem ⟨c, rfl⟩ (h y hy)

theorem mem_dualM_iff_mulVec (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) (x : Fin a → E) :
    x ∈ dualM σ 𝔞 T ↔ T *ᵥ x ∈ dualM σ 𝔞 1 := by
  simp [mem_dualM, form]

theorem latMap_dualM (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    {T : Matrix (Fin a) (Fin a) E} (hT : T.det ≠ 0) : latMap T (dualM σ 𝔞 T) = dualM σ 𝔞 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_dualM_iff_mulVec σ 𝔞 T y).1 hy
  · intro hx
    have e : T *ᵥ (T⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hT), Matrix.one_mulVec]
    exact ⟨T⁻¹ *ᵥ x, (mem_dualM_iff_mulVec σ 𝔞 T _).2 (e.symm ▸ hx), e⟩

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

def cork (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E) (T : Matrix (Fin a) (Fin a) E)
    (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.log (Ideal.absNorm v.asIdeal ^ 2)
    ((latMap T (tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E)) ⊔
      (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) • dualM σ 𝔞 1).toAddSubgroup.relIndex
        (dualM σ 𝔞 1).toAddSubgroup)

theorem relIndex_map_submodule {R M N : Type} [Ring R] [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f) (A B : Submodule R M) :
    (A.map f).toAddSubgroup.relIndex (B.map f).toAddSubgroup = A.toAddSubgroup.relIndex B.toAddSubgroup :=
  AddSubgroup.relIndex_map_map_of_injective (f := f.toAddMonoidHom) A.toAddSubgroup B.toAddSubgroup hf

theorem cork_eq_of_det_ne_zero (σ : E →+* E) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    {T : Matrix (Fin a) (Fin a) E} (hT : T.det ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    cork σ 𝔞 T v = Nat.log (Ideal.absNorm v.asIdeal ^ 2)
      ((tupLat 𝔞 (1 : Matrix (Fin a) (Fin a) E) ⊔
        (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) • dualM σ 𝔞 T).toAddSubgroup.relIndex
          (dualM σ 𝔞 T).toAddSubgroup) := by
  have hinj : Function.Injective (T.mulVecLin.restrictScalars (𝓞 E)) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det T).2 (Ne.isUnit hT))
  have key : ∀ (I : Ideal (𝓞 E)) (M D D' : Submodule (𝓞 E) (Fin a → E)), latMap T D = D' →
      (latMap T M ⊔ I • D').toAddSubgroup.relIndex D'.toAddSubgroup =
        (M ⊔ I • D).toAddSubgroup.relIndex D.toAddSubgroup := by
    rintro I M D _ rfl
    rw [← relIndex_map_submodule _ hinj (M ⊔ I • D) D, Submodule.map_sup, Submodule.map_smul'']
    rfl
  exact congrArg _ (key _ _ _ _ (latMap_dualM σ 𝔞 hT))

theorem mem_tupLat_one {a : ℕ} (x : Fin a → E) :
    x ∈ tupLat (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) (1 : Matrix (Fin a) (Fin a) E) ↔
      ∀ i, x i ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, c, hc, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
      intro i
      by_cases h : i = b <;> simp [Matrix.one_apply, h]
    | zero => simp
    | add x y _ _ h h' => exact fun i => add_mem (h i) (h' i)
    | smul c x _ h => exact fun i => mul_mem ⟨c, rfl⟩ (h i)
  · intro hx
    have : x = ∑ b, x b • fun i => (1 : Matrix (Fin a) (Fin a) E) i b := by
      ext i; simp [Finset.sum_apply, Matrix.one_apply]
    rw [this]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.subset_span ⟨b, x b, (FractionalIdeal.mem_one_iff _).2 (hx b), rfl⟩

theorem dualM_one_one (σ : E →+* E) {a : ℕ} :
    dualM σ (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) 1 =
      tupLat (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) (1 : Matrix (Fin a) (Fin a) E) := by
  ext x
  rw [mem_dualM, mem_tupLat_one]
  constructor
  · intro h i
    have := h (Pi.single i 1) ((mem_tupLat_one _).2 fun j => by
      by_cases hj : j = i <;> simp [Pi.single_apply, hj])
    simpa [form, dotProduct, Pi.single_apply, apply_ite σ] using this
  · intro h y hy
    rw [mem_tupLat_one] at hy
    simp only [form, Matrix.one_mulVec, dotProduct]
    refine sum_mem fun i _ => mul_mem ?_ (h i)
    obtain ⟨d, hd⟩ := hy i
    exact ⟨RingOfIntegers.mapRingHom σ d, by rw [← hd]; rfl⟩

theorem cork_one_one (σ : E →+* E) {a : ℕ} (v : HeightOneSpectrum (𝓞 F)) :
    cork σ (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) 1 v = 0 := by
  rw [cork_eq_of_det_ne_zero σ _ (by simp), dualM_one_one,
    AddSubgroup.relIndex_eq_one.2 (fun x hx => Submodule.mem_sup_left hx), Nat.log_one_right]

theorem cork_one_zero (σ : E →+* E) (h2 : Module.finrank F E = 2) {a : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) :
    cork σ (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) 0 v = a := by
  set I := v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) with hI
  let φ : (Fin a → 𝓞 E) →ₗ[𝓞 E] (Fin a → E) := (Algebra.linearMap (𝓞 E) E).compLeft (Fin a)
  have hφ : Function.Injective φ.toAddMonoidHom := fun x y h =>
    funext fun i => RingOfIntegers.coe_injective (congrFun h i)
  have h1 : tupLat (fun _ : Fin a => (1 : FractionalIdeal (𝓞 E)⁰ E)) (1 : Matrix (Fin a) (Fin a) E) =
      (⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E)).map φ := by
    ext x
    rw [mem_tupLat_one]
    constructor
    · intro h
      choose y hy using h
      exact ⟨y, trivial, funext hy⟩
    · rintro ⟨y, -, rfl⟩ i
      exact ⟨y i, rfl⟩
  have h3 : (I • (⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E))).toAddSubgroup =
      AddSubgroup.pi Set.univ fun _ => I.toAddSubgroup := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_pi, Set.mem_univ, true_imp_iff]
    constructor
    · intro hx i
      refine Submodule.smul_induction_on hx (fun r hr y _ => I.mul_mem_right _ hr) ?_
      exact fun y z hy hz => I.add_mem hy hz
    · intro hx
      have : x = ∑ b, x b • (Pi.single b 1 : Fin a → 𝓞 E) := by
        ext i; simp [Finset.sum_apply, Pi.single_apply]
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem_smul (hx b) trivial
  have h4 : I.toAddSubgroup.index = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← h2, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, ← Ideal.absNorm_algebraMap, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    rfl
  have h5 : latMap (0 : Matrix (Fin a) (Fin a) E) ((⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E)).map φ) = ⊥ := by
    simp [latMap]
  have hq : 1 < Ideal.absNorm v.asIdeal ^ 2 :=
    Nat.one_lt_pow two_ne_zero (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [cork, dualM_one_one, h1, h5, bot_sup_eq, ← hI, ← Submodule.map_smul'']
  have := AddSubgroup.relIndex_map_map_of_injective
    (I • (⊤ : Submodule (𝓞 E) (Fin a → 𝓞 E))).toAddSubgroup ⊤ hφ
  rw [AddSubgroup.relIndex_top_right, h3, AddSubgroup.index_pi] at this
  simp only [h4, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  rw [← h3] at this
  refine Eq.trans ?_ (Nat.log_pow hq a)
  rw [← this]
  rfl


open scoped Classical in
def eta₃ (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1

def densV (σ : E →+* E) (n : ℕ) {a : ℕ} (𝔞 : Fin a → FractionalIdeal (𝓞 E)⁰ E)
    (T : Matrix (Fin a) (Fin a) E) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  GlobalTheory.SgDen.densF (Ideal.absNorm v.asIdeal) (eta₃ E v) n a (cork σ 𝔞 T v)

def difAt (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ) ^
    (FractionalIdeal.count F v ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))

def StdAt (v : HeightOneSpectrum (𝓞 F)) (ψ : Fv F v → ℂ) : Prop :=
  ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔
    ∀ d ∈ differentIdeal ℤ (𝓞 F), x * algebraMap F (Fv F v) (d : F) ∈ v.adicCompletionIntegers F

def IsStdChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) : Prop :=
  IsCharAF F ψ ∧ (∀ x : Ainf F, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))) ∧
    ∀ v, StdAt v (psiV F ψ v)

variable (σ : E →ₐ[F] E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)

def IsModelAt (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ w, (A w)ᴴ * Hpk k r * A w = J.map w.embedding

end Glob

end GlobalTheory.SnMass
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
section
open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def OneVectorCc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    SW1a1 F E σ M J ∧
    (3 ≤ M → ∀ (β : F), β ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
      (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
      (Φf : (Fin 1 → Fin M → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φi → HasCompactSupport Φi →
      (∀ (N : ℕ) (e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φi ∘ e.symm)) →
      IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
      AllSome (IsCharAF F) fun ψ =>
      OnH F E σ M J fun μ 𝓕 =>
      OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t)) (fun v s t => psiV F ψ v (s * t))
        fun μi νi μv νv =>
        ∃ (Fi : Ainf F → ℂ) (Fl : ∀ v, Fv F v → ℂ),
          IsContDensityOn μi (fun X => qR (Ainf F) σ J (X 0)) id νi {c | IsUnit c} Φi Fi ∧
          (∀ v, IsContDensityOn (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) {c | c ≠ 0} (Φv v) (Fl v)) ∧
          Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) ∧
          meanC μ 𝓕 (thSum F E σ M J Φ {x | hE σ J (x 0) (x 0) = algebraMap F E β}) =
            Fi (algebraMap F (Ainf F) β) * ∏' v, Fl v (algebraMap F (Fv F v) β))

def IsDens {n : ℕ} (ε : Fin n → Bool) (φ : (Fin n → ℂ) → ℝ) (D : ℝ → ℝ) : Prop :=
  ContinuousOn D {t | t ≠ 0} ∧ ∀ S : Set ℝ, IsCompact S → S ⊆ {t | t ≠ 0} →
    ∫ y in {y | qEps ε y ∈ S}, φ y = ∫ t in S, D t

def SiegelMeanCc : Prop :=
  ∀ (I : AutInst), 3 ≤ I.n → ∀ (s : Bool) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    I.muA μf fund < ⊤ ∧
    ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ),
      (∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ v) ∧ HasCompactSupport (φ v) ∧ (∀ y, 0 ≤ φ v y) ∧
        IsDens (I.ε v) (φ v) (D v)) →
      ∫⁻ x in fund, (∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s},
          ENNReal.ofReal (∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))) ∂(I.muA μf) =
        I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, D v (sgn ℝ s))

end GlobalTheory.GaussMean
end
end

