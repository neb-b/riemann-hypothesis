module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfIsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleOfEtaleAtPrime
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IndEtaleAtPrime

theorem isIndEtale_of_etale_atPrime (R C : Type) [CommRing R] [CommRing C] (P : Ideal R) [P.IsPrime]
    [Algebra (Localization.AtPrime P) C] [Algebra.Etale (Localization.AtPrime P) C] :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap (Localization.AtPrime P) C).comp
      (algebraMap R (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let M := P.primeCompl
  let D0 := (Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)
  let s0 : D0 ⟶ (Functor.const _).obj (CommRingCat.of R) := 𝟙 _
  have hs0 : IsColimit (Cocone.mk _ s0) := GlobalTheory.IndEtFactorLoc.constColim R
  obtain ⟨j, Aj, _, instA, hAj, ⟨e⟩⟩ := GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit
    (GlobalTheory.IndEtaleLoc.Idx D0 s0 M) (GlobalTheory.IndEtaleLoc.diag D0 s0 M)
    (Cocone.mk _ (GlobalTheory.IndEtaleLoc.toLoc (s := s0) (M := M) L))
    (GlobalTheory.IndEtaleLoc.isColimitToLoc L hs0) C
  let Re : Type := Localization.Away j.e
  letI : Algebra R Re := (inferInstance : Algebra (D0.obj j.j) (Localization.Away j.e))
  letI : Algebra Re L := (GlobalTheory.IndEtaleLoc.leg L j).toAlgebra
  letI : Algebra Re Aj := instA
  haveI : Algebra.Etale Re Aj := hAj
  let e0 : R := j.e
  have he0 : e0 ∈ M := j.mem
  haveI : IsLocalization (Submonoid.powers e0) Re :=
    (inferInstance : IsLocalization (Submonoid.powers j.e) (Localization.Away j.e))
  haveI : IsScalarTower R Re L := IsScalarTower.of_algebraMap_eq (fun r =>
    (GlobalTheory.IndEtaleLoc.leg_algebraMap (s := s0) (M := M) L j r).symm)
  haveI hLoc : IsLocalization (M.map (algebraMap R Re)) L :=
    IsLocalization.isLocalization_of_submonoid_le Re L (Submonoid.powers e0) M
      (Submonoid.powers_le.2 he0)
  let e' : L ⊗[Re] Aj ≃ₐ[L] C := e
  letI rA : Algebra Aj (L ⊗[Re] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI hT : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re)))
      (L ⊗[Re] Aj) := IsLocalization.tensorRight _ _
  letI : Algebra Aj C := (e'.toRingHom.comp (algebraMap Aj (L ⊗[Re] Aj))).toAlgebra
  let eA : L ⊗[Re] Aj ≃ₐ[Aj] C := AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun _ => rfl)
  haveI hCloc : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) C :=
    IsLocalization.isLocalization_of_algEquiv _ eA
  letI : Algebra R Aj := ((algebraMap Re Aj).comp (algebraMap R Re)).toAlgebra
  haveI : IsScalarTower R Re Aj := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale R Re :=
    (Algebra.Etale.of_isLocalizationAway j.e : Algebra.Etale (D0.obj j.j) (Localization.Away j.e))
  haveI : Algebra.Etale R Aj := Algebra.Etale.comp R Re Aj
  letI : Algebra R C := ((algebraMap L C).comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R Aj C := IsScalarTower.of_algebraMap_eq (fun r => by
    have key : ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r)) =
        algebraMap L (L ⊗[Re] Aj) (algebraMap R L r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R Re L]
      generalize algebraMap R Re r = c
      rw [Algebra.algebraMap_eq_smul_one (A := Aj) c, Algebra.algebraMap_eq_smul_one (A := L) c,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    show algebraMap L C (algebraMap R L r) = e' ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r))
    rw [key, AlgEquiv.commutes])
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization R Aj C
      (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) (GlobalTheory.EtC.indEt_of_etale R Aj)

theorem indEt_of_indEt_atPrime : ∀ (B O : Type) [CommRing B] [CommRing O] (P : Ideal B) [P.IsPrime]
    [Algebra (Localization.AtPrime P) O] [Algebra B O] [IsScalarTower B (Localization.AtPrime P) O],
    IndEt (Localization.AtPrime P) O → IndEt B O := by
  intro B O _ _ P _ _ _ _ h
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  unfold IndEt GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := h
  refine ⟨J, inferInstance, inferInstance, D,
    (Functor.const J).map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime P))) ≫ t, s, hs,
    fun i => ⟨?_, ?_⟩⟩
  · letI : Algebra (Localization.AtPrime P) (D.obj i) := (t.app i).hom.toAlgebra
    haveI : Algebra.Etale (Localization.AtPrime P) (D.obj i) := (hj i).1
    exact isIndEtale_of_etale_atPrime B (D.obj i) P
  · have h2 := (hj i).2
    show CommRingCat.ofHom (algebraMap B (Localization.AtPrime P)) ≫ t.app i ≫ s.app i = _
    rw [h2]
    ext x
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime P) O x).symm

end GlobalTheory.IndEtaleAtPrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntProdRename
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.CharBound

noncomputable section

variable {C : Type} [Field C]

theorem isIntV_add' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x + y) :=
  le_trans (le_min hx hy) (v.map_add x y)

theorem isIntV_mul' {v : AddValuation C (WithTop ℝ)} {x y : C} (hx : IsIntV v x) (hy : IsIntV v y) :
    IsIntV v (x * y) := by
  unfold IsIntV at *
  rw [v.map_mul]
  exact add_nonneg hx hy

theorem isIntV_zero' {v : AddValuation C (WithTop ℝ)} : IsIntV v 0 := by
  unfold IsIntV; rw [v.map_zero]; exact le_top

theorem isIntV_one' {v : AddValuation C (WithTop ℝ)} : IsIntV v 1 := by
  unfold IsIntV; rw [v.map_one]

theorem mvIsInt_mul' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F G : MvPowerSeries σ C}
    (hF : MvIsInt v F) (hG : MvIsInt v G) : MvIsInt v (F * G) := by
  classical
  intro α
  rw [coeff_mul]
  exact Finset.sum_induction _ (IsIntV v) (fun _ _ => isIntV_add') isIntV_zero'
    fun p _ => isIntV_mul' (hF _) (hG _)

theorem mvIsInt_one' {v : AddValuation C (WithTop ℝ)} {σ : Type} : MvIsInt v (1 : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_one]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_X' {v : AddValuation C (WithTop ℝ)} {σ : Type} (s : σ) :
    MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  rw [coeff_X]
  split_ifs
  exacts [isIntV_one', isIntV_zero']

theorem mvIsInt_pow' {v : AddValuation C (WithTop ℝ)} {σ : Type} {F : MvPowerSeries σ C}
    (hF : MvIsInt v F) (n : ℕ) : MvIsInt v (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact mvIsInt_one'
  | succ n ih => rw [pow_succ]; exact mvIsInt_mul' ih hF

theorem mvIsInt_subst' {v : AddValuation C (WithTop ℝ)} {σ τ : Type} {a : σ → MvPowerSeries τ C}
    (ha : HasSubst a) (hai : ∀ s, MvIsInt v (a s)) {F : MvPowerSeries σ C} (hF : MvIsInt v F) :
    MvIsInt v (subst a F) := by
  intro β
  rw [coeff_subst ha]
  refine finsum_induction (IsIntV v) isIntV_zero' (fun _ _ => isIntV_add') fun e => ?_
  rw [smul_eq_mul]
  refine isIntV_mul' (hF e) ?_
  exact Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    (fun s _ => mvIsInt_pow' (hai s) _) β

theorem isInt_prod_rename (v : AddValuation C (WithTop ℝ)) (i d : ℕ)
    (χ : Fin i → MvPowerSeries (Fin d) C) (h : ∀ b, MvIsInt v (χ b)) :
    MvIsInt v (∏ b, subst (fun e : Fin d =>
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) :=
  Finset.prod_induction _ (MvIsInt v) (fun _ _ => mvIsInt_mul') mvIsInt_one'
    fun b _ => mvIsInt_subst' (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => mvIsInt_X' _) (h b)

variable [CharZero C]

theorem coeff_mvExp_lin {σ : Type} [Fintype σ] (c : σ → C) (α : σ →₀ ℕ) :
    coeff α (Formalism.L2.Th1.C.mvExp (∑ s, c s • (X s : MvPowerSeries σ C))) =
      α.prod fun s n => c s ^ n / (n.factorial : C) := by
  classical
  set L : MvPowerSeries σ C := ∑ s, c s • (X s : MvPowerSeries σ C) with hLdef
  have hL : constantCoeff L = 0 := by simp [hLdef]
  have hnL : constantCoeff (-L) = 0 := by rw [map_neg, hL, neg_zero]
  let g : MvPowerSeries σ C := fun β => β.prod fun s n => c s ^ n / (n.factorial : C)
  have hg : ∀ β, coeff β g = ∏ s, c s ^ β s / ((β s).factorial : C) := fun β => by
    show (β.prod fun s n => c s ^ n / (n.factorial : C)) = _
    exact Finsupp.prod_fintype _ _ (fun s => by simp)
  have hpL : ∀ i, pderiv i L = c i • (1 : MvPowerSeries σ C) := fun i => by
    simp [hLdef, pderiv_X, Pi.single_apply]
  have hpg : ∀ i, pderiv i g = c i • g := fun i => by
    ext β
    rw [coeff_pderiv, hg, coeff_smul, hg, Fintype.prod_eq_mul_prod_compl i,
      Fintype.prod_eq_mul_prod_compl i (fun s => c s ^ β s / ((β s).factorial : C))]
    have hrest : ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ (β + Finsupp.single i 1 : σ →₀ ℕ) s /
        (((β + Finsupp.single i 1 : σ →₀ ℕ) s).factorial : C) =
        ∏ s ∈ ({i}ᶜ : Finset σ), c s ^ β s / ((β s).factorial : C) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      have hs' : s ≠ i := by simpa using hs
      simp [Finsupp.single_apply, Ne.symm hs']
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorial_succ]
    have h0 : ((β i).factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h1 : ((β i : C) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    push_cast
    field_simp
    ring
  have hcg : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hg]
    simp
  have key : g * Formalism.L2.Th1.C.mvExp (-L) = 1 := by
    refine pderiv.ext (fun i => ?_) ?_
    · rw [Derivation.leibniz, Formalism.L2.Th1.C.pderiv_mvExp hnL, map_neg, hpL, hpg, pderiv_one]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring
    · rw [map_mul, hcg, Formalism.L2.Th1.C.constantCoeff_mvExp hnL, map_one, mul_one]
  have hE : Formalism.L2.Th1.C.mvExp L = g := by
    calc Formalism.L2.Th1.C.mvExp L = (g * Formalism.L2.Th1.C.mvExp (-L)) * Formalism.L2.Th1.C.mvExp L := by
          rw [key, one_mul]
      _ = g := by rw [mul_assoc, Formalism.L2.Th1.C.mvExp_neg hL, mul_one]
  rw [hE]
  rfl

theorem derivAt0_eq_eval {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) (w : σ → C)
    (hg : ∀ α, coeff α g = α.prod fun s n => w s ^ n / (n.factorial : C)) :
    derivAt0 P g = MvPolynomial.eval w P := by
  rw [MvPolynomial.eval_eq, derivAt0]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hg, mfact, mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  have : (((α s).factorial : ℕ) : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem eval_detPow (i c : ℕ) (H : Matrix (Fin i) (Fin i) C) :
    MvPolynomial.eval (fun x : (Σ _ : Fin i, Fin i) => H x.2 x.1) (detPow C i c) = H.det ^ c := by
  rw [detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]


open Formalism.L2.Th1.C in
theorem subst_col (v : AddValuation C (WithTop ℝ)) {i d : ℕ} (G : LogFGL v d) (u : Fin i → Fin d → C)
    (b : Fin i) (w : Fin d → C) (χ : MvPowerSeries (Fin d) C)
    (hχ : ∀ α, coeff α (subst (expOf G) χ) = α.prod fun e n => w e ^ n / (n.factorial : C)) :
    subst (expAlong (fun _ : Fin i => G) (fun _ => u))
        (subst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) χ) =
      mvExp (∑ e, w e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
  have hexp := (_root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v d G).1
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hexp.1
  have hL : ∀ b' : Fin i, HasSubst (fun e : Fin d => ∑ a, u a e • (X (⟨b', a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
    fun b' => hasSubst_of_constantCoeff_zero fun e => by simp
  have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero (hL x.1) (fun e => by simp) (hexp.1 x.2)
  have hR : HasSubst (fun e : Fin d => (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) :=
    hasSubst_of_constantCoeff_zero fun e => by simp
  have h1 : subst (expOf G) χ = mvExp (∑ e, w e • (X e : MvPowerSeries (Fin d) C)) := by
    ext α; rw [hχ, coeff_mvExp_lin]
  rw [subst_comp_subst_apply hR hEA]
  have h2 : (fun e : Fin d => subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) =
      fun e => subst (fun e : Fin d => ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (expOf G e) := by
    funext e; rw [subst_X hEA]; rfl
  rw [h2, ← subst_comp_subst_apply hE (hL b), h1, mvSubst_mvExp (by simp) (hL b)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom (hL b), map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_smul, coe_substAlgHom, subst_X (hL b)]

theorem lin_sum {i d : ℕ} (l : Fin i → Fin d → C) (u : Fin i → Fin d → C) :
    (∑ b, ∑ e, l b e • ∑ a, u a e • (X (⟨b, a⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C)) =
      ∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_smul]

theorem detDepth_le_char : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ)
    (G : LogFGL v d) (u : Fin i → Fin d → C) (l : Fin i → Fin d → C), (∀ b, IsCharLog G (l b)) →
    detDepth G u c ≤ toE (v ((Matrix.det (Matrix.of fun a b => ∑ e, l b e * u a e)) ^ c)) := by
  intro C _ _ v i d c G u l hl
  choose χ hχi hχc using hl
  have hf := isInt_prod_rename v i d χ hχi
  have key : subst (expAlong (fun _ : Fin i => G) (fun _ => u))
      (∏ b, subst (fun e : Fin d =>
        (X (⟨b, e⟩ : Σ _ : Fin i, Fin d) : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (χ b)) =
      Formalism.L2.Th1.C.mvExp (∑ x : (Σ _ : Fin i, Fin i), (∑ e, l x.1 e * u x.2 e) • (X x : MvPowerSeries (Σ _ : Fin i, Fin i) C)) := by
    have hexp := (_root_.GlobalTheory.FGDepth.expOf_twoSided_unique C v d G).1
    have hEA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
      hasSubst_of_constantCoeff_zero fun x => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun e => by simp) (fun e => by simp) (hexp.1 x.2)
    rw [← coe_substAlgHom hEA, map_prod, ← lin_sum, Formalism.L2.Th1.C.mvExp_sum _ _ (fun b _ => by simp)]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [coe_substAlgHom, subst_col v G u b (l b) (χ b) (hχc b)]
  unfold detDepth depth
  refine le_trans (iInf_le _ ⟨_, hf⟩) (le_of_eq ?_)
  dsimp only
  rw [key, derivAt0_eq_eval _ _ (fun x : (Σ _ : Fin i, Fin i) => (Matrix.of fun a b => ∑ e, l b e * u a e) x.2 x.1)
    (fun α => by rw [coeff_mvExp_lin]; rfl), eval_detPow]

end

end GlobalTheory.FGDepth.CharBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPow
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)

namespace GlobalTheory.QFam

theorem isIntegral_value_div (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ) (hN : 0 < N) (hact : ActBij act)
    (hf : IsFam act w f) (hq : ∀ i, QAll (· ∈ R) N (f i)) (hj : IsIntegral R (jT τ₀))
    (hΩ : Ω ^ 12 = DD τ₀) (i : ι) : IsIntegral R (f i τ₀ / Ω ^ w) := by
  have hq' : ∀ i, QAll (· ∈ (integralClosure R ℂ).toSubring) N (f i) := fun i => by
    obtain ⟨a, ha, haR⟩ := hq i
    exact ⟨a, ha, fun n => (integralClosure R ℂ).algebraMap_mem ⟨a n, haR n⟩⟩
  have hs := _root_.GlobalTheory.QFam.esymm_pow_twelve_div_mem ι act w N f (integralClosure R ℂ).toSubring τ₀ hN hact hf hq' hj
  have h1 : IsIntegral (integralClosure R ℂ) (f i τ₀ ^ 12 / DD τ₀ ^ w) :=
    GlobalTheory.T.isIntegral_of_esymm_mem_subring ι (integralClosure R ℂ).toSubring (fun i => f i τ₀ ^ 12 / DD τ₀ ^ w) hs i
  have h2 : IsIntegral R (f i τ₀ ^ 12 / DD τ₀ ^ w) := isIntegral_trans _ h1
  have h3 : (f i τ₀ / Ω ^ w) ^ 12 = f i τ₀ ^ 12 / DD τ₀ ^ w := by
    rw [div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm]
  exact IsIntegral.of_pow (n := 12) (by norm_num) (h3 ▸ h2)

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeets
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SeqFirst

theorem isIso_restrict_of_le {X Y : Scheme.{0}} (s : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (s ∣_ U)] : IsIso (s ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsIso ((s ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict s U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq s e)).1 h1

theorem exists_preimage {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {y : Y} (hy : y ∈ U) :
    ∃ x ∈ s ⁻¹ᵁ U, s x = y := by
  obtain ⟨z, hz⟩ := (s ∣_ U).homeomorph.surjective ⟨y, hy⟩
  refine ⟨z.1, z.2, ?_⟩
  have := congrArg Subtype.val hz
  rw [← morphismRestrict_base_coe]
  exact this

theorem injOn {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {a b : X}
    (ha : a ∈ s ⁻¹ᵁ U) (hb : b ∈ s ⁻¹ᵁ U) (h : s a = s b) : a = b := by
  obtain ⟨za, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨zb, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = b := ⟨⟨b, hb⟩, rfl⟩
  have : (s ∣_ U) za = (s ∣_ U) zb :=
    Subtype.ext ((morphismRestrict_base_coe s U za).trans (h.trans (morphismRestrict_base_coe s U zb).symm))
  exact congrArg Subtype.val ((s ∣_ U).homeomorph.injective this)

theorem isOpen_image {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {A : Set X}
    (hA : IsOpen A) : IsOpen (s '' (A ∩ s ⁻¹ᵁ U)) := by
  have h1 : IsOpenMap (fun z : (s ⁻¹ᵁ U) => s z.1) := by
    have : (fun z : (s ⁻¹ᵁ U) => s z.1) = (fun w : U => w.1) ∘ (s ∣_ U) := by
      funext z; exact (morphismRestrict_base_coe s U z).symm
    rw [this]
    exact U.isOpenEmbedding'.isOpenMap.comp (s ∣_ U).homeomorph.isOpenMap
  have h2 : s '' (A ∩ s ⁻¹ᵁ U) = (fun z : (s ⁻¹ᵁ U) => s z.1) '' ((fun z : (s ⁻¹ᵁ U) => z.1) ⁻¹' A) := by
    ext y; constructor
    · rintro ⟨x, ⟨hxA, hxU⟩, rfl⟩; exact ⟨⟨x, hxU⟩, hxA, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.1, ⟨hz, z.2⟩, rfl⟩
  rw [h2]
  exact h1 _ (hA.preimage continuous_subtype_val)

end GlobalTheory.SeqFirst


open GlobalTheory.SeqFirst in
theorem GlobalTheory.isIso_near_or_centre_meets : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  intro S Y f B y Y' s h
  induction h with
  | id => exact Or.inl ⟨⊤, trivial, inferInstance⟩
  | @step Y₁ Y₂ s J π hs h₁ h₂ h₃ ih =>
    rcases ih with ⟨U, hyU, hU⟩ | hr
    · obtain ⟨y', hy'U, hy'⟩ := exists_preimage s hyU
      by_cases hJ : y' ∈ J.support
      · exact Or.inr ⟨Y₁, s, J, U, y', hs, h₁, h₂, hyU, hU, hJ, hy'⟩
      · left
        have hA : IsOpen ((J.support : Set Y₁)ᶜ) := J.support.isClosed.isOpen_compl
        let V : Y.Opens := ⟨s '' ((J.support : Set Y₁)ᶜ ∩ s ⁻¹ᵁ U), isOpen_image s hA⟩
        have hVU : V ≤ U := by
          rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
        have hyV : y ∈ V := ⟨y', ⟨hJ, hy'U⟩, hy'⟩
        refine ⟨V, hyV, ?_⟩
        have : IsIso (s ∣_ V) := isIso_restrict_of_le s hVU
        have hπ : IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
          refine Principalise.isIso_restrict_of_blowup h₃ _ ?_
          intro x hx hxJ
          have hxU : x ∈ s ⁻¹ᵁ U := hVU hx
          obtain ⟨w, ⟨hwA, hwU⟩, hw⟩ := (hx : s x ∈ V)
          exact hwA (injOn s hwU hxU hw ▸ hxJ)
        rw [morphismRestrict_comp]
        exact IsIso.comp_isIso' hπ this
    · right; exact hr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGeneric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem isIso_restrict_of_closedImmersion_near_generic :
    ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W)
      (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ →
      i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) →
      ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  intro W W' Y Y₁ _ _ i _ h c _ s₁ U hiso hcomm hη hw
  obtain ⟨w', hw'⟩ := hw
  refine ⟨i ⁻¹ᵁ U, ⟨genericPoint W, hη⟩, ?_⟩
  have hi : IsClosedImmersion (i ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› U
  have hc : IsClosedImmersion (c ∣_ (s₁ ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) ‹_› _
  have h1 : IsClosedImmersion ((c ≫ s₁) ∣_ U) := by
    rw [morphismRestrict_comp]
    have hs : IsClosedImmersion (s₁ ∣_ U) := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hc hs
  have h2 : IsClosedImmersion ((h ≫ i) ∣_ U) := by
    rw [hcomm]; exact h1
  rw [morphismRestrict_comp] at h2
  have h3 : IsClosedImmersion (h ∣_ (i ⁻¹ᵁ U)) :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ (i ∣_ U) hi h2
  have hw'U : w' ∈ h ⁻¹ᵁ (i ⁻¹ᵁ U) := by
    show h w' ∈ i ⁻¹ᵁ U
    rw [hw']; exact hη
  have h4 : Surjective (h ∣_ (i ⁻¹ᵁ U)) := by
    constructor
    intro x
    have hcl : IsClosed (Set.range (h ∣_ (i ⁻¹ᵁ U))) := (h ∣_ (i ⁻¹ᵁ U)).isClosedEmbedding.isClosed_range
    let p : (h ⁻¹ᵁ (i ⁻¹ᵁ U) : Scheme) := ⟨w', hw'U⟩
    have hp : ((h ∣_ (i ⁻¹ᵁ U)) p).1 = genericPoint W := by
      rw [morphismRestrict_base_coe]; exact hw'
    have hsp : (h ∣_ (i ⁻¹ᵁ U)) p ⤳ x := by
      rw [← (i ⁻¹ᵁ U).ι.isOpenEmbedding.toIsInducing.specializes_iff]
      have : (i ⁻¹ᵁ U).ι ((h ∣_ (i ⁻¹ᵁ U)) p) = genericPoint W := hp
      rw [this]
      exact (genericPoint_spec W).specializes (Set.mem_univ _)
    exact hsp.mem_closed hcl ⟨p, rfl⟩
  exact isIso_of_isClosedImmersion_of_surjective _

end GlobalTheory
end

