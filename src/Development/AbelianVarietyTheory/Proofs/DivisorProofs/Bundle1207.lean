module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem norm_mul_exp_neg_log_normSq {u : ℂ} (hu : u ≠ 0) :
    ‖u‖ * Real.exp (-Real.log (‖u‖ ^ 2) / 2) = 1 := by
  have h : 0 < ‖u‖ := norm_pos_iff.2 hu
  rw [Real.log_pow, show -((2 : ℕ) * Real.log ‖u‖) / 2 = -Real.log ‖u‖ by push_cast; ring,
    Real.exp_neg, Real.exp_log h, mul_inv_cancel₀ h.ne']

theorem ratSec_div_eq {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    (h : genericPoint X ∈ L.U i ⊓ L.U j) :
    (r i : X.functionField) / (r j : X.functionField) = fnOf _ h (L.g i j : Γ(X, L.U i ⊓ L.U j)) := by
  rw [hr i j h, mul_div_cancel_right₀ _ (r j).ne_zero]

theorem regAt_ratSec_div {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι} {x : X}
    (hi : x ∈ L.U i) (hj : x ∈ L.U j) : RegAt x ((r i : X.functionField) / (r j : X.functionField)) := by
  rw [ratSec_div_eq hr (gen_mem (memInf hi hj))]
  exact regAt_fnOf (memInf hi hj) _ _

theorem ratVal_ratSec_div {σ : k →+* ℂ} {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) {i j : L.ι}
    {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ratVal ((r i : X.functionField) / (r j : X.functionField)) y = gv p σ L i j y := by
  have hy := mem_ptsIn_inf.2 ⟨hi, hj⟩
  rw [ratSec_div_eq hr (gen_mem (mem_ptsIn.1 hy)), ratVal_fnOf hy]
  rfl

theorem norm_ratSec_div {σ : k →+* ℂ} {L : LB X} (φ : Weight p σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {i j : L.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (L.U i)) (hj : y ∈ ptsIn p σ (L.U j)) :
    ‖ratVal ((r i : X.functionField) / (r j : X.functionField)) y‖ * Real.exp (-(φ.φ i y - φ.φ j y) / 2) = 1 := by
  rw [ratVal_ratSec_div hr hi hj, φ.trans i j y hi hj, sub_sub_cancel]
  exact norm_mul_exp_neg_log_normSq (gv_ne_zero hi hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.shift {A B : HermLB p} (t : ℝ) (h : Le B A) :
    Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (_root_.GlobalTheory.HSNef.le_iff_local k X p A B).1 h
  refine (_root_.GlobalTheory.HSNef.le_iff_local k X p _ _).2 ⟨r, r', hr, hr', hreg, fun σ y i j hi hj => ?_⟩
  have e : ((A.shift (fun _ => t) fun _ => rfl).φ σ).φ i y - ((B.shift (fun _ => t) fun _ => rfl).φ σ).φ j y =
      (A.φ σ).φ i y - (B.φ σ).φ j y := by
    simp only [HermLB.shift, Weight.addFn]; ring
  rw [e]
  exact hn σ y i j hi hj

theorem Le.trans {A B M : HermLB p} (h₁ : Le B A) (h₂ : Le A M) : Le B M := by
  obtain ⟨r₁, r₁', hr₁, hr₁', hreg₁, hn₁⟩ := (_root_.GlobalTheory.HSNef.le_iff_local k X p A B).1 h₁
  obtain ⟨r₂, r₂', hr₂, hr₂', hreg₂, hn₂⟩ := (_root_.GlobalTheory.HSNef.le_iff_local k X p M A).1 h₂
  obtain ⟨a₀, h₀⟩ := exists_chart A.isLB (genericPoint X)
  let c : X.functionFieldˣ := r₂' a₀ / r₁ a₀
  have hs : IsRatSec B.B fun j => r₁' j * c := fun i j h => by
    simp only [Units.val_mul]
    rw [hr₁' i j h, mul_assoc]
  have key (a : A.B.ι) (ha : genericPoint X ∈ A.B.U a) (i : M.B.ι) (j : B.B.ι) :
      (r₂ i : X.functionField) / ((r₁' j * c : X.functionFieldˣ) : X.functionField) =
        (r₂ i : X.functionField) / (r₂' a : X.functionField) * ((r₁ a : X.functionField) / (r₁' j : X.functionField)) := by
    have e₁ := hr₁ a a₀ (memInf ha h₀)
    have e₂ := hr₂' a a₀ (memInf ha h₀)
    have n₁ := (r₁ a₀).ne_zero
    have n₂ := (r₂' a₀).ne_zero
    have n₃ := (r₂' a).ne_zero
    have n₄ := (r₁' j).ne_zero
    simp only [c, Units.val_mul, Units.val_div_eq_div_val]
    rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero n₄ (div_ne_zero n₂ n₁)) (mul_ne_zero n₃ n₄), e₁, e₂]
    field_simp
  refine (_root_.GlobalTheory.HSNef.le_iff_local k X p M B).2 ⟨r₂, _, hr₂, hs, fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart A.isLB x
    rw [key a (gen_mem ha)]
    exact (hreg₂ x i a hi ha).mul (hreg₁ x a j ha hj)
  · have ha := mem_pick (A.φ σ).isLB y
    set a := pick (A.φ σ).isLB y
    have hx := mem_ptsIn.1 ha
    rw [key a (gen_mem hx), ratVal_mul (hreg₂ _ i a (mem_ptsIn.1 hi) hx) (hreg₁ _ a j hx (mem_ptsIn.1 hj)), norm_mul]
    have e : -((M.φ σ).φ i y - (B.φ σ).φ j y) / 2 =
        -((M.φ σ).φ i y - (A.φ σ).φ a y) / 2 + -((A.φ σ).φ a y - (B.φ σ).φ j y) / 2 := by ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((r₂ i : X.functionField) / (r₂' a : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ i y - (A.φ σ).φ a y) / 2)) *
        (‖ratVal ((r₁ a : X.functionField) / (r₁' j : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ a y - (B.φ σ).φ j y) / 2)) := by ring
      _ ≤ 1 := mul_le_one₀ (hn₂ σ y i a hi ha) (by positivity) (hn₁ σ y a j ha hj)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem Le.tens {A B : HermLB p} (M : HermLB p) (h : Le B A) : Le (M.tens B) (M.tens A) := by
  obtain ⟨r, r', hr, hr', hreg, hn⟩ := (_root_.GlobalTheory.HSNef.le_iff_local k X p A B).1 h
  obtain ⟨ρ, hρ⟩ := exists_isRatSec M.isLB
  have hs := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec A.isLB hr)).isRatSec
  have hs' := ((presents_divOfRatSec M.isLB hρ).tens (presents_divOfRatSec B.isLB hr')).isRatSec
  have key (c : M.B.ι × A.B.ι) (d : M.B.ι × B.B.ι) :
      ((ρ c.1 * r c.2 : X.functionFieldˣ) : X.functionField) / ((ρ d.1 * r' d.2 : X.functionFieldˣ) : X.functionField) =
        (ρ c.1 : X.functionField) / (ρ d.1 : X.functionField) * ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) := by
    rw [Units.val_mul, Units.val_mul, mul_div_mul_comm]
  refine (_root_.GlobalTheory.HSNef.le_iff_local k X p (M.tens A) (M.tens B)).2 ⟨fun c => ρ c.1 * r c.2, fun d => ρ d.1 * r' d.2, hs, hs',
    fun x c d hc hd => ?_, fun σ y c d hc hd => ?_⟩
  · beta_reduce
    erw [key c d]
    exact (regAt_ratSec_div hρ hc.1 hd.1).mul (hreg x c.2 d.2 hc.2 hd.2)
  · have hc' := mem_ptsIn_inf.1 hc
    have hd' := mem_ptsIn_inf.1 hd
    beta_reduce
    erw [key c d]
    rw [ratVal_mul (regAt_ratSec_div hρ (mem_ptsIn.1 hc'.1) (mem_ptsIn.1 hd'.1))
      (hreg _ c.2 d.2 (mem_ptsIn.1 hc'.2) (mem_ptsIn.1 hd'.2)), norm_mul]
    have e : -(((M.tens A).φ σ).φ c y - ((M.tens B).φ σ).φ d y) / 2 =
        -((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2 + -((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2 := by
      simp only [HermLB.tens, Weight.tens]; ring
    rw [e, Real.exp_add]
    calc _ = (‖ratVal ((ρ c.1 : X.functionField) / (ρ d.1 : X.functionField)) y‖ *
          Real.exp (-((M.φ σ).φ c.1 y - (M.φ σ).φ d.1 y) / 2)) *
        (‖ratVal ((r c.2 : X.functionField) / (r' d.2 : X.functionField)) y‖ *
          Real.exp (-((A.φ σ).φ c.2 y - (B.φ σ).φ d.2 y) / 2)) := by ring
      _ ≤ 1 := by
        rw [norm_ratSec_div (M.φ σ) hρ hc'.1 hd'.1, one_mul]
        exact hn σ y c.2 d.2 hc'.2 hd'.2

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem le_of_isometric {A B : HermLB p} (hi : B.Isometric A) : Le B A := by
  classical
  obtain ⟨w, hw, h⟩ := hi.exists_units
  obtain ⟨r, hr⟩ := exists_isRatSec B.isLB
  obtain ⟨b₀, h₀⟩ := exists_chart B.isLB (genericPoint X)
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ := gm (𝟙 X) (genericPoint X) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val :=
    gm_val (𝟙 X) _ U hU u
  have hw' (a a' b b') (h₁ : genericPoint X ∈ A.B.U a) (h₂ : genericPoint X ∈ A.B.U a')
      (h₃ : genericPoint X ∈ B.B.U b) (h₄ : genericPoint X ∈ B.B.U b') :
      F _ (w a b) = F _ (A.B.g a a') * (F _ (B.B.g b b'))⁻¹ * F _ (w a' b') :=
    hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄
  have hM (a) (h₁ : genericPoint X ∈ A.B.U a) : F _ (A.B.g a a) = 1 := gm_self A.isLB (𝟙 X) _ h₁
  have hL : F _ (B.B.g b₀ b₀) = 1 := gm_self B.isLB (𝟙 X) _ h₀
  have hr' : IsRatSec A.B fun a => F _ (w a b₀) * r b₀ := fun a a' h' => by
    beta_reduce
    rw [← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]
  have key (a b) (h' : genericPoint X ∈ A.B.U a ⊓ B.B.U b) :
      ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) / (r b : X.functionField) = fnOf _ h' (w a b).val := by
    rw [div_eq_iff (r b).ne_zero, ← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (B.B.g b b₀), ← Units.val_mul, ← Units.val_mul,
      hw' a a b b₀ h'.1 h'.1 h'.2 h₀, hM a h'.1, one_mul, mul_comm (F _ (B.B.g b b₀))⁻¹, mul_assoc,
      inv_mul_cancel_left]
  refine (_root_.GlobalTheory.HSNef.le_iff_local k X p A B).2 ⟨_, r, hr', hr, fun x a b ha hb => ?_, fun σ y a b ha hb => ?_⟩
  · beta_reduce
    rw [key a b (gen_mem (memInf ha hb))]
    exact regAt_fnOf (memInf ha hb) _ _
  · have hab := mem_ptsIn_inf.2 ⟨ha, hb⟩
    beta_reduce
    rw [key a b (gen_mem (mem_ptsIn.1 hab)), ratVal_fnOf hab, h σ a b y ha hb, add_sub_cancel_left, logSq,
      norm_mul_exp_neg_log_normSq (ev_ne_zero hab (Units.isUnit _))]

theorem le_tens_isometric_trans_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B M : HermLB p, (Le B A → Le (M.tens B) (M.tens A)) ∧ (B.Isometric A → Le B A) ∧ (Le B A → Le A M → Le B M) ∧
      ∀ t : ℝ, Le B A → Le (B.shift (fun _ => t) fun _ => rfl) (A.shift (fun _ => t) fun _ => rfl) :=
  fun _ _ _ _ _ _ _ _ => ⟨Le.tens _, le_of_isometric, Le.trans, fun t => Le.shift t⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameUnipotentLeFlagUnipotent
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E}
    (hy : y ∈ GlobalTheory.StdPar.colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan
  | (apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSpanCoefficients.exists_coeff_of_mem_colSpan ..)

theorem unip_le_unipFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S s hs hS d hd g hg
  refine Subgroup.subset_closure (?_ : g ∈ GlobalTheory.UAut.unipSet σ J (X.submatrix id (Fin.castLE hs)) d)
  have hlt : ∀ i : Fin r, (∃ k ∈ S, i ≤ k) → ∃ j : Fin s, Fin.castLE hs j = i :=
    fun i h => ⟨⟨i.val, (hS i).2 h⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have h1 := (Subgroup.mem_iInf.1 hg.1 (Fin.castLE hs i)).2 _ (Submodule.subset_span ⟨Fin.castLE hs i, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := exists_coeff_of_mem_colSpan hs X {i' | ∃ k ∈ S, i' ≤ k ∧ k < Fin.castLE hs i} (fun j => d j < d i) (fun i' ⟨k, hk, h1, h2⟩ => by
      obtain ⟨j, rfl⟩ := hlt i' ⟨k, hk, h1⟩
      exact ⟨j, rfl, (depth_lt_iff S s hs d hd i j).2 ⟨k, hk, h1, h2⟩⟩) h1
    refine ⟨a, fun j hj => ha j (not_lt.2 hj), ?_⟩
    rw [sub_mulVec, one_mulVec, e]
    rfl
  · have hp : (fun i => inclR (F := F) (AF F) (x i)) ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ S, i ≤ k} := by
      simp only [GlobalTheory.StdPar.colPerp, Submodule.mem_iInf, LinearMap.mem_ker]
      intro i hi
      obtain ⟨j, rfl⟩ := hlt i hi
      refine (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x (Fin.castLE hs j)).symm.trans ?_
      rw [show ((Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ x) (Fin.castLE hs j) =
        ((Formalism.UG.cT (σ : E →+* E) (X.submatrix id (Fin.castLE hs)) * J) *ᵥ x) j from rfl, hx]
      exact map_zero _
    obtain ⟨a, -, e⟩ := exists_coeff_of_mem_colSpan hs X _ (fun _ => True)
      (fun i' h => let ⟨j, hj⟩ := hlt i' h; ⟨j, hj, trivial⟩) (hg.2.2 _ hp)
    exact ⟨a, by rw [sub_mulVec, one_mulVec, e]⟩

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfRegularSection
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_pow_le_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X) (hL : L.IsLB), (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ p : ℕ, 1 ≤ p → ∀ s : (lbPow L p).Sec, Mono (cutHom F (isLB_lbPow hL p) s) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL hE F _ hF p hp s hs i hi
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX
  have hcut : suppDim (cut F (isLB_lbPow hL p) s) ≤ d := suppDim_cut_le F (isLB_lbPow hL p) s hF
  obtain ⟨C, hC⟩ := hE (cut F (isLB_lbPow hL p) s) hcut i hi
  refine sum_bound_of_step_diff (fun m => hdim k (twist F (lbPow L m)) i) d p C hp fun m => ?_
  have hcls : cls (lbPow L (m + p)) (isLB_lbPow hL (m + p)) =
      cls (lbPow L m) (isLB_lbPow hL m) + cls (lbPow L p) (isLB_lbPow hL p) := by
    rw [cls_lbPow hL (m + p), cls_lbPow hL m, cls_lbPow hL p, add_smul]
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F (lbPow L p) (lbPow L (m + p)) (lbPow L m) (isLB_lbPow hL p)
    (isLB_lbPow hL (m + p)) (isLB_lbPow hL m) s hs hcls).1 i
  have hb := hC (m + p)
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyTwistBoundOfTwoCuts
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_lbPow_le_of_two_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hp d L hL ih F _ hF i hi
  obtain ⟨H, hH⟩ : ∃ H : LB X, IsAmpleLB H := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  have : IsLocallyNoetherian X := (isNoetherian_of_isProjOver hp).toIsLocallyNoetherian
  obtain ⟨A, B, hA, hB, s, t, hs, ht, e⟩ := hH.exists_sub_of_mono_cutHom F (cls L hL)
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨C₁, h₁⟩ := ih (cut F hA s) (suppDim_cut_le F hA s hF) (j + 1) (by omega)
  obtain ⟨C₂, h₂⟩ := ih (cut F hB t) (suppDim_cut_le F hB t hF) j (by omega)
  refine sum_bound_of_step_diff (fun m => hdim k (twist F (lbPow L m)) (j + 1)) d 1 (C₁ + C₂)
    le_rfl fun m => ?_
  obtain ⟨M, hM, eM⟩ := cls_surj (m • cls L hL - cls B hB)
  have a₁ := (T.sheafCohomologyDim_twist_cut_inequalities k X hp F A (lbPow L (m + 1)) M hA (isLB_lbPow hL _) hM s hs (by
    rw [cls_lbPow hL, eM, succ_nsmul]
    nth_rewrite 2 [e]
    abel)).1 (j + 1)
  have a₂ := (T.sheafCohomologyDim_twist_cut_inequalities k X hp F B (lbPow L m) M hB (isLB_lbPow hL _) hM t ht (by
    rw [cls_lbPow hL, eM, sub_add_cancel])).2.1 j
  have a₃ := h₁ (m + 1)
  have a₄ : hdim k (twist (cut F hB t) (lbPow L m)) j ≤ C₂ * (d * (m + 1 + 1) ^ (d - 1)) :=
    (h₂ m).trans (by gcongr; omega)
  rw [add_mul]
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ProjLift

theorem exists_factor {A B X I : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup X] [Module ℂ X]
    (L₁ : A →ₗ[ℂ] X) (L₂ : B →ₗ[ℂ] X) (j : I → B) (hj : Submodule.span ℂ (Set.range j) = ⊤) (h : ∀ x, ∃ t, L₁ t = L₂ (j x)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y, L₁ (φ y) = L₂ y := by
  have h1 : ∀ y, L₂ y ∈ LinearMap.range L₁ := fun y =>
    (Submodule.span_le (p := (LinearMap.range L₁).comap L₂)).2 (by rintro _ ⟨x, rfl⟩; exact h x) (hj.ge Submodule.mem_top)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property L₁.rangeRestrict (L₂.codRestrict _ h1) L₁.surjective_rangeRestrict
  exact ⟨φ, fun y => congrArg Subtype.val (LinearMap.congr_fun hφ y)⟩

section Low

open Matrix Formalism.MainNotions.S GlobalTheory.DefLift

variable {D : D7}


open Classical in
theorem eq_on_low {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ)
    {U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) (v : ∀ τ, lowT M τ) : T (fun τ => (v τ : M.sm τ)) = U v := by
  have hT' : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
    intro τ g hg v w hw
    clear h
    induction hT using Submodule.span_induction with
    | mem T hT => exact hT.equiv τ g hg v w hw
    | zero => rfl
    | add x y _ _ hx hy => exact (congrArg₂ (· + ·) hx hy).trans rfl
    | smul a x _ hx => exact (congrArg (a • ·) hx).trans rfl
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT' τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem kEquiv_thetaP {θ : InfFam D} {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {Δ : PolF D W.rank V.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} {B : Submodule ℂ (GA D V → c.W)}
    {thP : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ))}
    (hth : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω h g φ) pt io B thP) (y : B) :
    KEquiv θ M ((thP y).compMultilinearMap (PiTensorProduct.tprod ℂ)) := by
  intro τ k hk v u hu
  have hmul : ∀ h g k φ, thetaKO ω h (g * k) φ = thetaKO ω h g (ω (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  funext g
  simp only [LinearMap.compMultilinearMap_apply, rTr, hth.eq, Lift.thetaPInt, hmul, hio.2.1 τ k hk v u hu]

theorem exists_lift {θ : InfFam D} {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D W)} {χ : GA D W → ℂ} {A B I : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : A →ₗ[ℂ] MMap M) (he : ∀ t, e t ∈ Mult θ M J χ)
    (L : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ)))
    (hL : ∀ y, KEquiv θ M ((L y).compMultilinearMap (PiTensorProduct.tprod ℂ))) (j : I → B)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (v : ∀ τ, lowT M τ) (hv : ∀ τ, v τ ≠ 0)
    (h : ∀ x, ∃ t, e t (fun τ => (v τ : M.sm τ)) = L (j x) (PiTensorProduct.tprod ℂ v)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y (u : ∀ τ, lowT M τ), e (φ y) (fun τ => (u τ : M.sm τ)) = L y (PiTensorProduct.tprod ℂ u) := by
  let L₁ : A →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun t u => e t (fun τ => (u τ : M.sm τ))
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  let L₂ : B →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun y u => L y (PiTensorProduct.tprod ℂ u)
      map_add' := fun a b => by rw [map_add (f := _)]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  obtain ⟨φ, hφ⟩ := exists_factor L₁ L₂ j hj fun x => (h x).imp fun t ht =>
    funext fun u => eq_on_low h1 h2 (he t) (hL (j x)) v hv ht u
  exact ⟨φ, fun y u => congrFun (hφ y) u⟩

end Low

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem holShape_of_overK (R : RealDat D A Ks) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) :
    GlobalTheory.HolDict.HolShape (R.MW i σ) := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
    rw [← hs ρ]
    exact GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  exact fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩

theorem proj_apply (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : (R.HW i σ).H)
    (v : (R.MW i σ).Vec) :
    (R.HW i σ).e ((∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) t) v = R.eWf i σ ((R.HW i σ).e t v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, hg i σ, postOn_apply]
  rfl


end GlobalTheory.GalLift.ProjLift

end
end

