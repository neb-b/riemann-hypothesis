module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonGaugeDmonOfHLIntegral
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValColumnsCongr
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ColumnValue

theorem dmonOf_zero_index {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (g : PS k 1 d) : DmonOf F u 0 g = g := by
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, ih]; rfl

theorem dmonOf_smul {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (c : k) (g : PS k 1 d) :
    DmonOf F u mo (c • g) = C c * DmonOf F u mo g := by
  rw [smul_eq_C_mul]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, DerivEndo.iterate_dof_C_mul]

theorem column_value {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d) (hh : B.IsCanonGauge k h)
    (w0 a : O) (N m : ℕ) (w : PS R 1 d)
    (hw : FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0))
    (I : Ideal R) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (α : ι → R) (hI : ∀ l, α l ∈ I)
    (hα : ∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) =
      algebraMap R k (α l) • (fun i => algebraMap R k (u l i)))
    (hβ : ∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
      ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range)
    (f : PS R 1 d) (y : ι → R) (hf : ∀ l mo, coeff mo (Dof B.G.F (u l) f - C (y l) * f) ∈ I)
    (mo : ι →₀ ℕ) :
    ∃ s : R, s - (∏ l, y l ^ mo l) * constantCoeff f ∈ I ∧
      B.nabVal k h w0 (N * m) (FB.toK k (f * w ^ m)) (fun l i => algebraMap R k (u l i))
        (MvPolynomial.monomial mo 1) = algebraMap R k s := by
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : FB.toK k (f * w ^ m) * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      FB.toK k f * FB.expS k ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0)) := by
    have e : FB.toK k (f * w ^ m) = FB.toK k f * FB.toK k w ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hw, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • ev (n := 1) ![B.actK k a] (B.hL k h w0))) = algebraMap R k r := by
    intro mo
    rcases eq_or_ne mo 0 with rfl | hmo
    · exact ⟨0, I.zero_mem, by rw [dmonOf_zero_index, nt_const_smul, cA, mul_zero, map_zero]⟩
    · obtain ⟨l, hl⟩ := Finsupp.ne_iff.1 hmo
      obtain ⟨t, ht⟩ := canonGauge_dmonOf_hL_integral R d O k B h hh w0 ι u hβ mo
      refine ⟨(m : R) * ((∏ l, α l ^ mo l) * t), I.mul_mem_left _ (I.mul_mem_right _
        (Ideal.prod_mem I (Finset.mem_univ l) (I.pow_mem_of_mem (hI l) _ (Nat.pos_of_ne_zero hl)))), ?_⟩
      rw [dmonOf_smul, map_mul, constantCoeff_C,
        (invariantDeriv_along_endo R d O k B a).2 ι _ (fun l => algebraMap R k (α l)) hα mo, ← ht]
      simp only [map_mul, map_prod, map_pow, map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cA, mul_zero]) hφ f mo
  refine ⟨constantCoeff (DmonOf B.G.F u mo f) + r, ?_, ?_⟩
  · rw [add_sub_right_comm]
    exact I.add_mem (constantCoeff_dmonOf_sub_mem R d B.G.F I ι u y f hf mo) hr
  · unfold FB.nabVal
    rw [hG, PullbackColumn.dpolyOf_monomial_one]
    exact e

end GlobalTheory.ColumnValue

namespace GlobalTheory

open ColumnValue

theorem nabVal_columns_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l ∈ I) → (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) → (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) → ∀ (n : ℕ) (f : Fin n → PS R 1 d) (y : ι × Fin n → R), (∀ l b mo, coeff mo (Dof B.G.F (u l) (f b) - C (y (l, b)) * f b) ∈ I) → ∀ P : MvPolynomial (ι × Fin n) R, ∃ r ∈ I, ∑ mo ∈ P.support, algebraMap R k (P.coeff mo) * ∏ b, B.nabVal k h w0 (N * m) (FB.toK k (f b * w ^ m)) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial (colM mo b) 1) = algebraMap R k (MvPolynomial.eval y P * ∏ b, constantCoeff (f b) + r) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw I ι _ u α hI hα hβ n f y hf P
  choose s hs he using fun (mo : ι × Fin n →₀ ℕ) (b : Fin n) =>
    column_value B h hh w0 a N m w hw I u α hI hα hβ (f b) (fun l => y (l, b)) (fun l => hf l b) (colM mo b)
  refine ⟨∑ mo ∈ P.support, P.coeff mo * ∏ b, s mo b -
    MvPolynomial.eval y P * ∏ b, constantCoeff (f b), ?_, ?_⟩
  · rw [MvPolynomial.eval_eq', Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine I.sum_mem fun mo _ => ?_
    rw [mul_assoc, ← mul_sub]
    refine I.mul_mem_left _ ?_
    rw [Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib, ← Ideal.Quotient.eq, map_prod, map_prod]
    exact Finset.prod_congr rfl fun b _ => Ideal.Quotient.eq.2 (hs mo b)
  · rw [add_sub_cancel]
    simp only [he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QkIsPullFLeftIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtRestrictCompare

section General

variable {X Y Y' Z Z' : Scheme.{0}} {L : LB X}

theorem gen_eq_of_pull {φ : PUnit → (Y ⟶ X)} {ε : PUnit → ℤ} (t t' : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (hinj : ∀ U : Y.Opens, Function.Injective (h.app U))
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) : t = t' := by
  obtain ⟨s⟩ := t
  obtain ⟨s'⟩ := t'
  congr 1
  funext j
  have e := H j j (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hle : h ⁻¹ᵁ (LB.wchart L φ j) ≤
      LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j := fun _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩
  have key : ∀ {U : Y.Opens} {A B : Z.Opens} (h₁ : h ⁻¹ᵁ U ≤ A) (h₂ : A ≤ B)
      (h₃ : B ≤ h ⁻¹ᵁ U) (s : Γ(Y, U)ˣ),
      ((res h₁ (res h₂ (res h₃ (pullU h U s))) : Γ(Z, h ⁻¹ᵁ U)ˣ) : Γ(Z, h ⁻¹ᵁ U)) = (h.app U).hom s := by
    intro U A B h₁ h₂ h₃ s
    change (h.app U ≫ Z.presheaf.map (homOfLE h₃).op ≫ Z.presheaf.map (homOfLE h₂).op ≫
      Z.presheaf.map (homOfLE h₁).op).hom s.1 = (h.app U).hom s.1
    rw [← Functor.map_comp, ← Functor.map_comp]
    erw [Z.presheaf.map_id]
    rw [Category.comp_id]
  refine Units.ext (hinj _ ?_)
  exact (key hle _ _ _).symm.trans ((congrArg (fun u => (res hle u).1) e).trans (key hle _ _ _))

end General

variable {R : Type} [CommRing R] [IsDomain R]

section Points

variable (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))

variable {D T}

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

section OnOpen

variable {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}


theorem psiOn_unique (ψ ψ' : PsiOn D W) : ψ = ψ' := by
  have hd : IsDominant (jK R) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R (FractionRing R))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant (jK R) := .of_isDominant _
  have : IsSchemeTheoreticallyDominant (jK R ∣_ W) :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict (jK R) W).flip
  have e : ψ.psi = ψ'.psi := funext fun χ => gen_eq_of_pull _ _ (jK R ∣_ W) (Scheme.Hom.app_injective _)
    (corr_trans D.P.isLB (ψ.psi_eq χ) (corr_symm (ψ'.psi_eq χ)))
  obtain ⟨a, _, _⟩ := ψ
  obtain ⟨b, _, _⟩ := ψ'
  obtain rfl : a = b := e
  rfl

variable {ψ : PsiOn D W} {k : ℕ} {T : Over W.toScheme}

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end OnOpen

end GlobalTheory.GtRestrictCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwo
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_io_pr_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (j : ℕ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → Lev ε E μ j w → ∀ s c d, Lev ε E μ (j + 2) (io s (pr s (Pi.single c w)) d) := by
  intro M _ _ n ε E N _ _ F io pr μ j w hE hF hT hw s c d
  obtain ⟨hc, hwt⟩ := hw
  have hn : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos s
    exact_mod_cast this
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · have h1 := _root_.GlobalTheory.casKLe_proj_single M n ε E N F io pr _ w hE hF hT h0 hc s c
    have h2 := _root_.GlobalTheory.casKLe_io_component M n ε E N F io pr _ s _ hE hF hT (by linarith) h1 d
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h2
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by linarith)
    push_cast
    nlinarith
  · have h1 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) j hT).1 w hwt s c
    have h2 := (GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j + 1) hT).2 s _ h1 d
    have e : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 1 + 1 := by push_cast; ring
    rw [e]
    exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjDualTensorLevelAddTwo
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem algTens_pr_single_lev :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)]
      [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
      (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ)
      (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr →
      Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
      ∀ c s, Lev ε (F s) (μ - Pi.single s 1) (j + 2) (pr s (Pi.single c w)) := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hE hF hT hS _ hw c s
  obtain ⟨hlow, hsq⟩ := _root_.GlobalTheory.lowK_sub_single_and_sqrt_ckv_le n kk ε μ bv s hS
  obtain ⟨hw1, hw2⟩ := hw
  have h0 : 0 ≤ Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * (j : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hS1, hS2, hS3, hS4⟩ :=
      _root_.GlobalTheory.casKLe_proj_single M n ε E N F io pr _ w hE.2.1 (fun s => (hF s).2.1) hT h0 hw1 s c
    refine ⟨S, hS1, hS2, hS3, fun x hx => (hS4 x hx).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (add_nonneg h0 (Real.sqrt_nonneg _))
    push_cast
    linarith
  · have h1 := (_root_.GlobalTheory.algTens_wtNear M n ε E N F io pr (lowK ε μ) (j : ℝ) hT).1 w hw2 s c
    refine wtNear_le_of_add_dist_le (N s) n ε (F s) _ _ _ _ ?_ h1
    have h2 : ∑ a, |lowK ε μ a - lowK ε (μ - Pi.single s 1) a| = 1 := by
      rw [hlow, Finset.sum_eq_single s]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    rw [h2]
    push_cast
    linarith

end GlobalTheory
end

