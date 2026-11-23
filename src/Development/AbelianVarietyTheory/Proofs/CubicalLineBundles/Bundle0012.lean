module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoPowOfHermFormPullEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory
namespace PullIso
open CubeValues SymmetricSemicharacter ComplexPoints

section Values

variable {X : Scheme.{0}}

lemma val_resG (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' x V (resG X hVU f) = valAt' x U f :=
  (valueRules X x).2.2.1 U V hVU f h

lemma val_mul (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)) :
    valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he, map_mul]

lemma val_unit_inv (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U (f⁻¹).val = (valAt' x U f.val)⁻¹ := by
  obtain ⟨e, he⟩ := (valueRules X x).2.1 U h
  simp only [he]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

lemma exists_of_iSup (x : Sp ℂ ⟶ X) {I : Type*} (U : I → X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (⨆ i, U i)) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ U i := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (((valueRules X x).1 _).1 h)
  exact ⟨i, ((valueRules X x).1 _).2 hi⟩

lemma exists_of_local_quotient (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {E I : Type} (e : E → (Sp ℂ ⟶ X)) (he : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, e z = x)
    (W : X.Opens) (φ : E → ℂ) (a b : I → Γ(X, W))
    (hb : ∀ z, ⊤ ≤ e z ⁻¹ᵁ W → ∃ i, valAt' (e z) W (b i) ≠ 0)
    (hab : ∀ i z, ⊤ ≤ e z ⁻¹ᵁ W → valAt' (e z) W (a i) = φ z * valAt' (e z) W (b i)) :
    ∃ c : Γ(X, W), ∀ z, ⊤ ≤ e z ⁻¹ᵁ W → valAt' (e z) W c = φ z := by
  have hu : ∀ i, IsUnit (resG X (X.basicOpen_le (b i)) (b i)) := fun i =>
    X.toRingedSpace.isUnit_res_basicOpen (b i)
  let q : ∀ i, Γ(X, X.basicOpen (b i)) := fun i =>
    resG X (X.basicOpen_le (b i)) (a i) * ((hu i).unit⁻¹).val
  have hq : ∀ i z, ⊤ ≤ e z ⁻¹ᵁ X.basicOpen (b i) → valAt' (e z) _ (q i) = φ z := fun i z hz => by
    have hW : ⊤ ≤ e z ⁻¹ᵁ W := fun y hy => X.basicOpen_le (b i) (hz hy)
    have hne := ((valueRules X (e z)).2.2.2.2.1 W (b i)).1 hz
    simp only [q]
    rw [val_mul _ hz, val_unit_inv _ hz, IsUnit.unit_spec, val_resG _ _ hz, val_resG _ _ hz,
      hab i z hW, mul_inv_cancel_right₀ hne]
  have hc : W ≤ ⨆ i, X.basicOpen (b i) := opens_le_of_complexPoints p _ _ fun x hx hW => by
    obtain ⟨z, rfl⟩ := he x hx
    obtain ⟨i, hi⟩ := hb z hW
    exact fun y hy => le_iSup (fun i => X.basicOpen (b i)) i
      (((valueRules X (e z)).2.2.2.2.1 W (b i)).2 hi hy)
  obtain ⟨c, hc', -⟩ := X.sheaf.existsUnique_gluing' (fun i => X.basicOpen (b i)) W
    (fun i => homOfLE (X.basicOpen_le (b i))) hc q (fun i j => by
      refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq p (X.basicOpen (b i) ⊓ X.basicOpen (b j)) _ _ fun x hx hij => ?_
      obtain ⟨z, rfl⟩ := he x hx
      obtain ⟨hi, hj⟩ := (le_preimage_inf _ _ _).1 hij
      exact ((val_resG _ inf_le_left hij (q i)).trans (hq i z hi)).trans
        ((val_resG _ inf_le_right hij (q j)).trans (hq j z hj)).symm)
  refine ⟨c, fun z hW => ?_⟩
  obtain ⟨i, hi⟩ := hb z hW
  have hz := ((valueRules X (e z)).2.2.2.2.1 W (b i)).2 hi
  rw [← hq i z hz, ← val_resG _ (X.basicOpen_le (b i)) hz c]
  exact congrArg _ (hc' i)

lemma pow_chart_iff (x : Sp ℂ ⟶ X) (L : LB X) (n : ℕ) (J : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (lbPow L n).U J ↔ ⊤ ≤ x ⁻¹ᵁ L.U (J PUnit.unit) :=
  (le_preimage_wchart x L (K := PUnit) (fun _ => 𝟙 X) J).trans
    ⟨fun h => h PUnit.unit, fun h _ => h⟩

lemma pull_chart_iff {Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (J : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U J ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (J PUnit.unit) :=
  (le_preimage_wchart x L (K := PUnit) (fun _ => f) J).trans
    ⟨fun h => h PUnit.unit, fun h _ => h⟩

lemma val_pow_g (x : Sp ℂ ⟶ X) (L : LB X) (n : ℕ) (J J' : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (lbPow L n).U J) (h' : ⊤ ≤ x ⁻¹ᵁ (lbPow L n).U J') :
    valAt' x ((lbPow L n).U J ⊓ (lbPow L n).U J') ((lbPow L n).g J J').val =
      valAt' x (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g _ _).val ^ n := by
  refine (val_linComb x valueRules L (K := PUnit) (fun _ => 𝟙 X) _ J J' h h').trans ?_
  rw [Fintype.prod_unique, Category.comp_id, zpow_natCast]

lemma val_pull_g {Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (J J' : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (L.pull f).U J) (h' : ⊤ ≤ x ⁻¹ᵁ (L.pull f).U J') :
    valAt' x ((L.pull f).U J ⊓ (L.pull f).U J') ((L.pull f).g J J').val =
      valAt' (x ≫ f) (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g _ _).val := by
  refine (val_linComb x valueRules L (K := PUnit) (fun _ => f) _ J J' h h').trans ?_
  rw [Fintype.prod_unique, zpow_one]

lemma lbIso_of_frames (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced X]
    {E : Type} (e : E → (Sp ℂ ⟶ X)) (he : ∀ x : Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ z, e z = x)
    (M N : LB X) (α : M.ι → E → ℂ) (β : N.ι → E → ℂ)
    (hα : ∀ i z, ⊤ ≤ e z ⁻¹ᵁ M.U i → α i z ≠ 0) (hβ : ∀ i z, ⊤ ≤ e z ⁻¹ᵁ N.U i → β i z ≠ 0)
    (hα' : ∀ i j z, ⊤ ≤ e z ⁻¹ᵁ M.U i → ⊤ ≤ e z ⁻¹ᵁ M.U j →
      α i z = valAt' (e z) (M.U i ⊓ M.U j) (M.g i j).val * α j z)
    (hβ' : ∀ i j z, ⊤ ≤ e z ⁻¹ᵁ N.U i → ⊤ ≤ e z ⁻¹ᵁ N.U j →
      β i z = valAt' (e z) (N.U i ⊓ N.U j) (N.g i j).val * β j z)
    (h : ∀ i j, ∃ c : Γ(X, M.U i ⊓ N.U j), ∀ z, ⊤ ≤ e z ⁻¹ᵁ (M.U i ⊓ N.U j) →
      valAt' (e z) _ c = α i z / β j z) : LBIso N M := by
  choose c hc using h
  have hu : ∀ i j, IsUnit (c i j) := fun i j => isUnit_of_valAt'_ne_zero p _ _ fun x hx hij => by
    obtain ⟨z, rfl⟩ := he x hx
    obtain ⟨hi, hj⟩ := (le_preimage_inf _ _ _).1 hij
    rw [hc i j z hij]
    exact div_ne_zero (hα i z hi) (hβ j z hj)
  refine ⟨⟨fun q => (hu q.1 q.2).unit⟩, fun q r => Units.ext ?_⟩
  refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq p (M.U q.1 ⊓ N.U q.2 ⊓ (M.U r.1 ⊓ N.U r.2)) _ _ fun x hx hqr => ?_
  obtain ⟨z, rfl⟩ := he x hx
  obtain ⟨hq, hr⟩ := (le_preimage_inf _ _ _).1 hqr
  obtain ⟨hq1, hq2⟩ := (le_preimage_inf _ _ _).1 hq
  obtain ⟨hr1, hr2⟩ := (le_preimage_inf _ _ _).1 hr
  refine ((val_res _ valueRules inf_le_left hqr _).trans (hc q.1 q.2 z hq)).trans (Eq.symm ?_)
  refine (val_unit_mul _ valueRules hqr _ _).trans ?_
  refine (congrArg₂ (· * ·) ((val_unit_mul _ valueRules hqr _ _).trans
    (congrArg₂ (· * ·) (val_res _ valueRules _ hqr (M.g q.1 r.1))
      ((val_unit_inv _ hqr _).trans (congrArg (·⁻¹) (val_res _ valueRules _ hqr (N.g q.2 r.2))))))
    ((val_res _ valueRules inf_le_right hqr _).trans (hc r.1 r.2 z hr))).trans ?_
  have n1 := val_unit_ne_zero _ valueRules ((le_preimage_inf _ _ _).2 ⟨hq2, hr2⟩) (N.g q.2 r.2)
  have n2 := hβ _ z hr2
  rw [hα' q.1 r.1 z hq1 hr1, hβ' q.2 r.2 z hq2 hr2]
  field_simp

end Values

lemma exists_generating_sections (P : Out.PolAV (Sp ℂ)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → (lbPow P.L N).Sec),
      ⨆ i, Out.nonzeroLocus (s i) = ⊤ := by
  obtain ⟨N, hN, m, s, hcov, -⟩ := P.ample ⊤ (isAffineOpen_top _)
  have : IsIso (P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso (P.A.left.topIso).hom)
  let ψ := inv (P.A.hom ⁻¹ᵁ ⊤).ι
  have hψ : ψ ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  have loc := fun i => VeryAmpleCharts.locus_move P.L N hψ P.isLB (s i)
  refine ⟨N, hN, m, fun i => VeryAmpleCharts.move P.L N hψ (s i), top_le_iff.1 fun y _ => ?_⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show ψ y ∈ ⨆ i, Out.nonzeroLocus (s i) by rw [hcov]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩

end PullIso


open PullIso CubeValues SymmetricSemicharacter in
theorem lbIso_pow_of_hermForm_pull_eq :
    ∀ (P P' : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (u' : HolUnif P'.A P'.L P'.g)
    (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Hm' : Matrix (Fin P'.g) (Fin P'.g) ℂ) (χ' : u'.Λ → ℂ),
  u.IsAH Hm χ → u'.IsAH Hm' χ' →
  (∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃! s, u.IsFnPow k s θ) →
  (∀ (k : ℕ) s, ∃! θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ) →
  ∀ (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ)) (n : ℕ), (∀ l ∈ u.Λ, F l ∈ u'.Λ) →
  (∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) → ∀ f : P.A ⟶ P'.A, (∀ z, u'.ex (F z) = u.ex z ≫ f) →
  ∃ N : ℕ, 1 ≤ N ∧ LBIso (lbPow (P'.L.pull f.left) N) (lbPow P.L (N * n)) := by
  intro P P' u u' Hm χ Hm' χ' hu hu' hsec hfn F n hΛ hH f hF
  obtain ⟨N, hN, m, s, hcov⟩ := exists_generating_sections P'
  have hFl : ∀ z, (u'.ex (F z)).left = (u.ex z).left ≫ f.left := fun z => by
    rw [hF, Over.comp_left]
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  choose θ hθ using fun i => (hfn N (s i)).exists
  have hθ0 : ∀ z, ∃ i, θ i z ≠ 0 := fun z => by
    obtain ⟨i, hi⟩ := exists_of_iSup (u'.ex z).left (fun i => Out.nonzeroLocus (s i))
      (by rw [hcov]; exact le_rfl)
    obtain ⟨k, hk⟩ := exists_of_iSup (u'.ex z).left _ hi
    have h1 := ((valueRules _ (u'.ex z).left).2.2.2.2.1 _ _).1 hk
    rw [(hθ i).2 k z fun y hy => P'.A.left.basicOpen_le _ (hk hy)] at h1
    exact ⟨i, left_ne_zero_of_mul h1⟩
  have hT : ∀ i, u.IsThetaFn Hm χ (2 * N * n) (fun z => θ i (F z) ^ 2) := fun i => by
    refine ⟨((hθ i).1.1.comp hFd).pow 2, fun l z => ?_⟩
    have h1 := (hθ i).1.2 ⟨F l, hΛ l l.2⟩ (F z)
    have c1 := semicharacter_sq_eq_one_of_symmetric P u Hm χ hu l
    have c2 := semicharacter_sq_eq_one_of_symmetric P' u' Hm' χ' hu' ⟨F l, hΛ l l.2⟩
    have e : Complex.exp (Real.pi * (n * hermForm Hm z l) + Real.pi / 2 * (n * hermForm Hm l l)) =
        Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ n := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    simp only [hH, e] at h1
    simp only [map_add (f := _), h1]
    generalize Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) = a
    generalize χ' ⟨F l, hΛ l l.2⟩ = b at c2
    generalize χ l = c at c1
    have d1 : c ^ (2 * N * n) = 1 := by rw [_root_.mul_assoc, pow_mul, c1, one_pow]
    have d2 : b ^ (N * 2) = 1 := by rw [_root_.mul_comm, pow_mul, c2, one_pow]
    rw [mul_pow, mul_pow c, d1, ← pow_mul, mul_pow, d2]
    ring
  choose t ht using fun i => (hsec _ _ (hT i)).exists
  have hsm : Smooth P.A.hom := by
    have := P.smoothDim
    exact SmoothOfRelativeDimension.smooth P.g P.A.hom
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  have he : ∀ x : Sp ℂ ⟶ P.A.left, x ≫ P.A.hom = 𝟙 _ → ∃ z, (u.ex z).left = x := fun x hx => by
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
    exact ⟨z, congrArg (fun φ => φ.left) hz⟩
  have hK : ∀ (K : (lbPow (P'.L.pull f.left) (2 * N)).ι) z,
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow (P'.L.pull f.left) (2 * N)).U K →
      ⊤ ≤ (u'.ex (F z)).left ⁻¹ᵁ P'.L.U (K PUnit.unit PUnit.unit) := fun K z hz => by
    rw [hFl]
    exact (pull_chart_iff _ _ _ _).1 ((pow_chart_iff _ _ _ _).1 hz)
  refine ⟨2 * N, by omega, lbIso_of_frames P.A.hom (fun z => (u.ex z).left) he _ _
    (fun J z => u.fr (J PUnit.unit) z ^ (2 * N * n))
    (fun K z => u'.fr (K PUnit.unit PUnit.unit) (F z) ^ (2 * N))
    (fun J z hz => pow_ne_zero _ (u.fr_ne _ _ ((pow_chart_iff _ _ _ _).1 hz)))
    (fun K z hz => pow_ne_zero _ (u'.fr_ne _ _ (hK K z hz)))
    (fun J J' z hz hz' => ?_) (fun K K' z hz hz' => ?_) (fun J K => ?_)⟩
  · rw [val_pow_g _ _ _ _ _ hz hz', ← mul_pow, ← u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2
      ⟨(pow_chart_iff _ _ _ _).1 hz, (pow_chart_iff _ _ _ _).1 hz'⟩)]
  · rw [val_pow_g _ _ _ _ _ hz hz', val_pull_g _ _ _ _ _ ((pow_chart_iff _ _ _ _).1 hz)
      ((pow_chart_iff _ _ _ _).1 hz'), ← hFl, ← mul_pow, ← u'.fr_compat _ _ _
      ((le_preimage_inf _ _ _).2 ⟨hK K z hz, hK K' z hz'⟩)]
  · have le : (lbPow P.L (2 * N * n)).U J ⊓ (lbPow (P'.L.pull f.left) (2 * N)).U K ≤
        f.left ⁻¹ᵁ (lbPow P'.L N).U (K PUnit.unit) := fun y hy =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 PUnit.unit) PUnit.unit
    let σ := fun i => resG _ le ((f.left.app _).hom ((s i).f (K PUnit.unit)))
    have hσ : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow P.L (2 * N * n)).U J ⊓
        (lbPow (P'.L.pull f.left) (2 * N)).U K) → valAt' (u.ex z).left _ (σ i * σ i) =
        θ i (F z) ^ 2 * u'.fr (K PUnit.unit PUnit.unit) (F z) ^ (2 * N) := fun i z hz => by
      have h1 : valAt' (u.ex z).left _ (σ i) =
          θ i (F z) * u'.fr (K PUnit.unit PUnit.unit) (F z) ^ N := by
        refine (val_resG _ le hz _).trans
          (((valueRules _ (u.ex z).left).2.2.2.1 _ f.left _ _).trans ?_)
        rw [← hFl]
        exact (hθ i).2 _ _ ((pow_chart_iff _ _ _ _).2 (hK K z ((le_preimage_inf _ _ _).1 hz).2))
      rw [val_mul _ hz, h1]
      ring
    refine exists_of_local_quotient P.A.hom (fun z => (u.ex z).left) he _ _
      (fun i => resG _ inf_le_left ((t i).f J)) (fun i => σ i * σ i) (fun z hz => ?_)
      (fun i z hz => ?_)
    · obtain ⟨i, hi⟩ := hθ0 (F z)
      refine ⟨i, ?_⟩
      rw [hσ i z hz]
      exact mul_ne_zero (pow_ne_zero _ hi)
        (pow_ne_zero _ (u'.fr_ne _ _ (hK K z ((le_preimage_inf _ _ _).1 hz).2)))
    · have n1 := u'.fr_ne _ _ (hK K z ((le_preimage_inf _ _ _).1 hz).2)
      rw [hσ i z hz, val_resG _ inf_le_left hz, ht i J z ((le_preimage_inf _ _ _).1 hz).1]
      field_simp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocallyQuasiFiniteOfQuasiFiniteAt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.OntoFinite

theorem eq_genericPoint {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (g : ℕ) (hX : SmoothOfRelativeDimension g (f ≫ p))
    (hY : SmoothOfRelativeDimension g p) (x : X) (hx : f x = genericPoint Y) : x = genericPoint X := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f x) trivial
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ U) (x := x) hxU
  have hVU : V ≤ f ⁻¹ᵁ U := hVU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ p)
  let φ := f.appLE U V hVU
  have sq : Spec.map φ ≫ hU.fromSpec = hV.fromSpec ≫ f := hU.SpecMap_appLE_fromSpec f hV hVU
  algebraize [α.hom, φ.hom, φ.hom.comp α.hom]
  have t₁ : Algebra.trdeg K Γ(Y, U) = g :=
    trdeg_eq_of_smoothOfRelativeDimension K Y p g hY Γ(Y, U) hU.fromSpec inferInstance hα.symm
  have t₂ : Algebra.trdeg K Γ(X, V) = g :=
    trdeg_eq_of_smoothOfRelativeDimension K X (f ≫ p) g hX Γ(X, V) hV.fromSpec inferInstance (by
      rw [← Category.assoc, ← sq, Category.assoc, ← hα, ← Spec.map_comp]; rfl)
  obtain ⟨q, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have gU : hU.fromSpec (genericPoint (Spec Γ(Y, U))) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have gV : hV.fromSpec (genericPoint (Spec Γ(X, V))) = genericPoint X := genericPoint_eq_of_isOpenImmersion _
  have e : Spec.map φ q = genericPoint (Spec Γ(Y, U)) := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [gU, ← hx, ← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply]
  rw [genericPoint_eq_bot_of_affine] at e
  have e' : q.asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) = ⊥ := congrArg PrimeSpectrum.asIdeal e
  have : FaithfulSMul Γ(Y, U) Γ(X, V) := by
    rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← e']
    exact Ideal.ker_le_comap _
  have : FaithfulSMul K Γ(Y, U) := by
    rw [faithfulSMul_iff_algebraMap_injective]; exact RingHom.injective _
  have h := trdeg_add_eq K Γ(Y, U) (A := Γ(X, V))
  rw [t₁, t₂] at h
  have h0 : Algebra.trdeg Γ(Y, U) Γ(X, V) = 0 :=
    Cardinal.eq_of_add_eq_add_left (h.trans (add_zero _).symm) (Cardinal.natCast_lt_aleph0)
  have halg : Algebra.IsAlgebraic Γ(Y, U) Γ(X, V) := trdeg_eq_zero_iff.1 h0
  have hq : q.asIdeal = ⊥ := by
    by_contra hne
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact Ideal.comap_ne_bot_of_algebraic_mem ha0 ha (halg.isAlgebraic a) e'
  rw [← gV, genericPoint_eq_bot_of_affine]
  exact congrArg _ (PrimeSpectrum.ext hq)

theorem quasiFiniteAt_genericPoint {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f] (g : ℕ)
    (hX : SmoothOfRelativeDimension g (f ≫ p)) (hY : SmoothOfRelativeDimension g p) :
    f.QuasiFiniteAt (genericPoint X) := by
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  obtain rfl := eq_genericPoint p f g hX hY x hx
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : Subsingleton (f.fiber (f (genericPoint X))) := by
    refine (f.fiberHomeo _).toEquiv.subsingleton_congr.2 ⟨fun a b => Subtype.ext ?_⟩
    exact (eq_genericPoint p f g hX hY a.1 (a.2.trans hx)).trans
      (eq_genericPoint p f g hX hY b.1 (b.2.trans hx)).symm
  exact isOpen_discrete _

theorem isIso_transl {S : Scheme.{0}} {A : Over S} [GrpObj A] (x : 𝟙_ (Over S) ⟶ A) :
    IsIso ((toUnit A ≫ x) * 𝟙 A).left := by
  have hu (t : A ⟶ A) : t ≫ toUnit A = toUnit A := toUnit_unique _ _
  suffices IsIso ((toUnit A ≫ x) * 𝟙 A) from inferInstanceAs (IsIso ((Over.forget S).map ((toUnit A ≫ x) * 𝟙 A)))
  refine ⟨(toUnit A ≫ x)⁻¹ * 𝟙 A, ?_, ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hu, Category.comp_id, inv_mul_cancel_left,
      mul_inv_cancel_left]

theorem locallyQuasiFinite_of_quasiFiniteAt {K : Type} [Field K] [IsAlgClosed K]
    {A B : Over (Spec (CommRingCat.of K))} [GrpObj A] [GrpObj B] [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [IsMonHom f] [LocallyOfFiniteType f.left] (x : A.left) (hx : f.left.QuasiFiniteAt x) :
    LocallyQuasiFinite f.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : A.left) (hy : IsClosed ({y} : Set A.left)) : ∃ u : 𝟙_ _ ⟶ A, u.left pt = y :=
    ⟨Over.homMk (pointOfClosedPoint (K := K) A.hom y hy) (pointOfClosedPoint_comp (K := K) A.hom y hy),
      pointOfClosedPoint_apply (K := K) A.hom y hy pt⟩
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints (Z := (f.left.quasiFiniteLocus : Set A.left)) ⟨x, hx⟩
    f.left.quasiFiniteLocus.isOpen.isLocallyClosed
  obtain ⟨u, rfl⟩ := hpt a hac
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  by_contra hne
  obtain ⟨b, hb, hbc⟩ := nonempty_inter_closedPoints (Z := (f.left.quasiFiniteLocus : Set A.left)ᶜ)
    (Set.nonempty_compl.2 fun h => hne (SetLike.coe_injective h))
    f.left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨v, rfl⟩ := hpt b hbc
  have := isIso_transl (v * u⁻¹)
  have := isIso_transl ((v * u⁻¹) ≫ f)
  have e : ((toUnit A ≫ (v * u⁻¹)) * 𝟙 A) ≫ f = f ≫ ((toUnit B ≫ (v * u⁻¹) ≫ f) * 𝟙 B) := by
    rw [MonObj.mul_comp, MonObj.comp_mul f, ← Category.assoc f, toUnit_unique (f ≫ toUnit B) (toUnit A)]
    simp only [Category.assoc, Category.id_comp, Category.comp_id]
  have e₂ : u ≫ ((toUnit A ≫ (v * u⁻¹)) * 𝟙 A) = v := by
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (𝟙 _)]
    simp
  apply hb
  have h₁ : (f.left ≫ ((toUnit B ≫ (v * u⁻¹) ≫ f) * 𝟙 B).left).QuasiFiniteAt (u.left pt) :=
    Scheme.Hom.quasiFiniteAt_comp_iff.2 ha
  rw [← Over.comp_left, ← e, Over.comp_left, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
    ← Scheme.Hom.comp_apply, ← Over.comp_left, e₂] at h₁
  exact h₁

theorem isFinite_of_surjective {K : Type} [Field K] {A B : Over (Sp K)} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g : ℕ} (dA : SmoothOfRelativeDimension g A.hom)
    (dB : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [Surjective f.left] : IsFinite f.left := by
  have := hA.proper
  have := hB.proper
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := .of_comp _ B.hom
  let t : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
  have gA := isGrpPullback_pullback A t
  have gB := isGrpPullback_pullback B t
  have geomIntegralPullback (C : Over (Sp K)) [GrpObj C] (hC : IsAbelianScheme C) :
      GeometricallyIntegral ((Over.pullback t).obj C).hom := by
    have sqC := (isGrpPullback_pullback C t).1
    exact forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _
      (MorphismProperty.of_isPullback (P := @Smooth) sqC hC.smooth)
      (MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqC hC.geomConnected)
  let f' := (Over.pullback t).map f
  have sq : IsPullback (pullback.fst A.hom t) f'.left f.left (pullback.fst B.hom t) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm gB.1
    rw [Over.w, Over.w]
    exact gA.1
  have : Surjective f'.left := MorphismProperty.of_isPullback (P := @Surjective) sq ‹_›
  have : IsProper f'.left := MorphismProperty.of_isPullback (P := @IsProper) sq ‹_›
  have : Surjective t := ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Surjective (pullback.fst B.hom t) := inferInstance
  have iA := geomIntegralPullback A hA
  have iB := geomIntegralPullback B hB
  have : IsIntegral ((Over.pullback t).obj A).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj A).hom
  have : IsIntegral ((Over.pullback t).obj B).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton ((Over.pullback t).obj B).hom
  have : IsProper ((Over.pullback t).obj A).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) gA.1 hA.proper
  have hq := quasiFiniteAt_genericPoint ((Over.pullback t).obj B).hom f'.left g
    (by rw [Over.w]; exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback gA.1 dA)
    ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback gB.1 dB)
  have : LocallyQuasiFinite f.left := Unif.locallyQuasiFinite_of_isPullback_surjective _ _ _ _ _ _ _ _ sq ‹_›
    inferInstance inferInstance (locallyQuasiFinite_of_quasiFiniteAt f' _ hq)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.OntoFinite
end
end

