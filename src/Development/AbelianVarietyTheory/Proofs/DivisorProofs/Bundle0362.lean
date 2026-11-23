module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveEventuallyFilteredColimitAlgebra
section
open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.ProjColim

noncomputable def sysPoly {R : Type} [CommRing R] (n m : ℕ) (r : Fin m → Fin n → R) :
    (Fin m × Fin n) ⊕ (Fin n × Fin n) → MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin m)) R
  | .inl (b, l) => ∑ a, MvPolynomial.C (r b a) * MvPolynomial.X (.inl (a, l))
  | .inr (a, l) => MvPolynomial.X (.inl (a, l)) - (if a = l then 1 else 0) -
      ∑ b, MvPolynomial.X (.inr (a, b)) * MvPolynomial.C (r b l)

theorem eval₂_sysPoly_eq_zero_iff {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (n m : ℕ)
    (r : Fin m → Fin n → R) (x : (Fin n × Fin n) ⊕ (Fin n × Fin m) → B) :
    (∀ i, MvPolynomial.eval₂ φ x (sysPoly n m r i) = 0) ↔
      (∀ b l, ∑ a, φ (r b a) * x (.inl (a, l)) = 0) ∧
      (∀ a l, x (.inl (a, l)) = (if a = l then 1 else 0) + ∑ b, x (.inr (a, b)) * φ (r b l)) := by
  have key : ∀ a l, MvPolynomial.eval₂ φ x (sysPoly n m r (.inr (a, l))) =
      x (.inl (a, l)) - ((if a = l then 1 else 0) + ∑ b, x (.inr (a, b)) * φ (r b l)) := by
    intro a l
    by_cases h : a = l <;> simp [sysPoly, MvPolynomial.eval₂_sum, h, sub_sub]
  constructor
  · intro h
    refine ⟨fun b l => ?_, fun a l => ?_⟩
    · simpa [sysPoly, MvPolynomial.eval₂_sum] using h (.inl (b, l))
    · have := h (.inr (a, l))
      rw [key] at this
      exact sub_eq_zero.mp this
  · rintro ⟨h1, h2⟩ (⟨b, l⟩ | ⟨a, l⟩)
    · simpa [sysPoly, MvPolynomial.eval₂_sum] using h1 b l
    · rw [key, sub_eq_zero]
      exact h2 a l

theorem projective_eventually_of_finitePresentation : ∀ (J : Type) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{0}) (c : Cocone F), IsColimit c → ∀ (j : J) (M : Type) [AddCommGroup M]
    [Module (F.obj j) M] [Module.FinitePresentation (F.obj j) M],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Projective c.pt (c.pt ⊗[F.obj j] M)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] M) := by
  intro J _ _ F c hc j M _ _ _ hproj
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin (F.obj j) M
  obtain ⟨m, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let π : (Fin n → F.obj j) →ₗ[F.obj j] M := e.symm.toLinearMap ∘ₗ K.mkQ
  have hπ : Function.Surjective π := e.symm.surjective.comp K.mkQ_surjective
  have hker : Submodule.span (F.obj j) (Set.range r) = LinearMap.ker π := by
    rw [hr, LinearMap.ker_comp, LinearEquiv.ker]
    exact (Submodule.ker_mkQ K).symm
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨v, w, h1, h2⟩ := GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange (F.obj j) c.pt M n m π hπ r hker hproj
  obtain ⟨k₀, f₀, hk⟩ := GlobalTheory.T.polynomial_system_eventually_solvable_colimit J F c hc j _ _ (sysPoly n m r)
    (Sum.elim (fun p => v p.1 p.2) (fun p => w p.1 p.2))
    ((eval₂_sysPoly_eq_zero_iff _ n m r _).mpr ⟨h1, h2⟩)
  refine ⟨k₀, f₀, fun k f => ?_⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra
  obtain ⟨y, hy⟩ := hk k f
  obtain ⟨h1', h2'⟩ := (eval₂_sysPoly_eq_zero_iff _ n m r y).mp hy
  exact GlobalTheory.T.projective_baseChange_of_presentation_matrix_split (F.obj j) (F.obj k) M n m π hπ r hker (fun a l => y (.inl (a, l)))
    (fun a b => y (.inr (a, b))) h1' h2'

theorem projective_eventually : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A],
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Module.Finite c.pt (c.pt ⊗[F.obj j] A) ∧ Module.Projective c.pt (c.pt ⊗[F.obj j] A)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Module.Projective (F.obj k) (F.obj k ⊗[F.obj j] A) := by
  intro J _ _ F c hc j A _ _ _ hfp
  obtain ⟨hfin, hproj⟩ := hfp
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  obtain ⟨k₁, g₁, hk₁⟩ := GlobalTheory.T.eventually_finite_baseChange_filtered_colimit J F c hc j A hfin
  letI : Algebra (F.obj j) (F.obj k₁) := (F.map (g₁ ≫ 𝟙 k₁)).hom.toAlgebra
  haveI : Module.Finite (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) := hk₁ k₁ (𝟙 k₁)
  haveI : Module.FinitePresentation (F.obj k₁) (F.obj k₁ ⊗[F.obj j] A) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  letI : Algebra (F.obj k₁) c.pt := (c.ι.app k₁).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) c.pt := IsScalarTower.of_algebraMap_eq (fun x => by
    change (c.ι.app j).hom x = (c.ι.app k₁).hom ((F.map (g₁ ≫ 𝟙 k₁)).hom x)
    rw [← c.w (g₁ ≫ 𝟙 k₁)]; rfl)
  haveI : Module.Projective c.pt (c.pt ⊗[F.obj j] A) := hproj
  have hproj₁ : Module.Projective c.pt (c.pt ⊗[F.obj k₁] (F.obj k₁ ⊗[F.obj j] A)) :=
    Module.Projective.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (F.obj j) (F.obj k₁) c.pt c.pt A).symm
  obtain ⟨k₀, g₀, hk₀⟩ :=
    projective_eventually_of_finitePresentation J F c hc k₁ (F.obj k₁ ⊗[F.obj j] A) hproj₁
  refine ⟨k₀, (g₁ ≫ 𝟙 k₁) ≫ g₀, fun k f => ?_⟩
  letI : Algebra (F.obj k₁) (F.obj k) := (F.map (g₀ ≫ f)).hom.toAlgebra
  haveI : Module.Projective (F.obj k) (F.obj k ⊗[F.obj k₁] (F.obj k₁ ⊗[F.obj j] A)) := hk₀ k f
  letI : Algebra (F.obj j) (F.obj k) := (F.map (((g₁ ≫ 𝟙 k₁) ≫ g₀) ≫ f)).hom.toAlgebra
  haveI : IsScalarTower (F.obj j) (F.obj k₁) (F.obj k) := IsScalarTower.of_algebraMap_eq (fun x => by
    change (F.map (((g₁ ≫ 𝟙 k₁) ≫ g₀) ≫ f)).hom x = (F.map (g₀ ≫ f)).hom ((F.map (g₁ ≫ 𝟙 k₁)).hom x)
    rw [Category.assoc, F.map_comp (g₁ ≫ 𝟙 k₁)]; rfl)
  exact Module.Projective.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (F.obj j) (F.obj k₁) (F.obj k) (F.obj k) A)

end GlobalTheory.ProjColim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ConjExp


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.ConjExp.qConj_torsion : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wp N x) (_root_.GlobalTheory.WpFam.wp N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wpd N x) (_root_.GlobalTheory.WpFam.wpd N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ (x ≠ 0 → _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wB N x) (_root_.GlobalTheory.WpFam.wB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)))) := by
  intro N _ g a hg x
  have hc := _root_.GlobalTheory.WpFam.CoeffConj.main N g a hg x
  refine ⟨⟨_, _root_.GlobalTheory.WpFam.ExpP.main N x, ?_⟩,
    ⟨_, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, ?_⟩, fun hx => ⟨_,
      _root_.GlobalTheory.WpFam.ExpansionB.main N x hx, ?_⟩⟩
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cP N x n)) = _root_.GlobalTheory.WpFam.cP N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.2.2]
    exact _root_.GlobalTheory.WpFam.ExpP.main N _
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cD N x n)) = _root_.GlobalTheory.WpFam.cD N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.1]
    exact _root_.GlobalTheory.WpFam.DerivExpansion.main N _
  · have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
    rw [show (fun n => g (_root_.GlobalTheory.WpFam.cB N x n)) = _root_.GlobalTheory.WpFam.cB N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).1]
    exact _root_.GlobalTheory.WpFam.ExpansionB.main N _ fun h => hx (hzero.1 h)

end GlobalTheory.WpFam.ConjExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecompositionStatement
section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_stack_decomposition : ∀ (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k), Y.rank ≤ Fintype.card R → (Y.submatrix Sum.inl τ).det ≠ 0 → ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  first | exact @GlobalTheory.RankChart.exists_eq_stack | exact GlobalTheory.RankChart.exists_eq_stack | (intros; apply GlobalTheory.RankChart.exists_eq_stack <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFunctionalVanishesOnOmegaForms
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.ResVan

variable {F : Type} [Field F] {d : ℕ}

theorem prod_zpow_add (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (m n : Fin (d + 1) → ℤ) :
    ∏ j, x j ^ (m j + n j) = (∏ j, x j ^ m j) * ∏ j, x j ^ n j := by
  first
  | exact @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add
  | (apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProductZpowAdd.prod_zpow_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProductZpowAdd.prod_zpow_add ..)

def monoA (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (I : Finset (Fin (d + 1))) : Submonoid F where
  carrier := {f | ∃ m : Fin (d + 1) → ℤ, ∑ j, m j = 0 ∧ (∀ j ∉ I, 0 ≤ m j) ∧ f = ∏ j, x j ^ m j}
  one_mem' := ⟨0, by simp, fun _ _ => le_rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm, hm', rfl⟩ ⟨n, hn, hn', rfl⟩
    refine ⟨m + n, ?_, fun j hj => add_nonneg (hm' j hj) (hn' j hj), ?_⟩
    · simp [Finset.sum_add_distrib, hm, hn]
    · simp only [Pi.add_apply]; exact (prod_zpow_add x hx m n).symm

theorem prod_single_sub (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i j : Fin (d + 1)) :
    ∏ l, x l ^ ((Pi.single j 1 : Fin (d + 1) → ℤ) l - (Pi.single i 1 : Fin (d + 1) → ℤ) l) = x j / x i := by
  simp_rw [zpow_sub₀ (hx _)]
  rw [Finset.prod_div_distrib]
  congr 1
  · rw [Fintype.prod_eq_single j (fun l hl => by simp [Pi.single_apply, hl])]; simp
  · rw [Fintype.prod_eq_single i (fun l hl => by simp [Pi.single_apply, hl])]; simp

theorem prod_exp (x : Fin (d + 1) → F) (hx : ∀ i, x i ≠ 0) (i0 : Fin (d + 1)) :
    (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ∏ j, x i0 / x j = 1 := by
  simp_rw [zpow_sub₀ (hx _), zpow_one]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hq : ∏ j, x j ^ (if j = i0 then ((d : ℤ) + 1) else 0) = x i0 ^ (d + 1) := by
    rw [Fintype.prod_eq_single i0 (fun l hl => by simp [hl])]
    rw [if_pos rfl, show ((d : ℤ) + 1) = ((d + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rw [hq]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : ∏ j, x j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hx j
  have h1 := hx i0
  field_simp

theorem resvan : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x →
    ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∀ (i : Fin (d + 1)) (I : Finset (Fin (d + 1))), I.Nonempty → i ∉ I →
    ∀ y ∈ omA k x I, ρ y = 0 := by
  intro k _ F _ _ d x hx ρ hρ i I hI hi y hy
  obtain ⟨i0, hi0⟩ := hI
  have hne := hx.ne
  have hii0 : i ≠ i0 := fun h => hi (h ▸ hi0)
  have h1 : (∏ j, x i0 / x j) * y ∈ rA k x I := by
    have h2 := (Submodule.mem_iInf _).1 hy i0
    have h3 := (Submodule.mem_iInf _).1 h2 hi0
    simpa using h3
  have hz : (∏ j, x i0 / x j) * y ∈ Submodule.span k (monoA x hne I : Set F) := by
    rw [rA, ← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h1
    refine Submodule.span_mono (Submonoid.closure_le.2 ?_) h1
    rintro _ ⟨i', hi', j, rfl⟩
    refine ⟨(Pi.single j 1 : Fin (d + 1) → ℤ) - Pi.single i' 1, by simp, fun l hl => ?_,
      (prod_single_sub x hne i' j).symm⟩
    have hl' : l ≠ i' := fun h => hl (h ▸ hi')
    simp only [Pi.sub_apply, Pi.single_apply, hl', if_false, sub_zero]
    split_ifs <;> omega
  have hP := prod_exp x hne i0
  have hy' : y = (∏ j, x j ^ ((1 : ℤ) - if j = i0 then ((d : ℤ) + 1) else 0)) * ((∏ j, x i0 / x j) * y) := by
    rw [← mul_assoc, hP, one_mul]
  rw [hy']
  generalize (∏ j, x i0 / x j) * y = z at hz
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, hm, hm', rfl⟩ := hf
    rw [← prod_zpow_add x hne]
    refine hρ.2 _ ?_ ?_
    · rw [Finset.sum_add_distrib, hm, add_zero, Finset.sum_sub_distrib]
      simp
    · intro h0
      have := congrFun h0 i
      simp only [hii0, if_false, Pi.zero_apply] at this
      have := hm' i hi
      omega
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, map_add (f := _), ha, hb, add_zero]
  | smul c a _ ha => rw [mul_smul_comm, map_smul, ha, smul_zero]

end GlobalTheory.PD.ResVan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory

namespace GlobalTheory

namespace PDiv

section Lift

variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]

def liftSemi (f : M →ₛₗ[algebraMap R R'] N) : R' ⊗[R] M →ₗ[R'] N :=
  letI : Module R N := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' N := ⟨fun a b w => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  LinearMap.liftBaseChange R'
    { toFun := f, map_add' := map_add f, map_smul' := fun r m => map_smulₛₗ f r m }

@[simp] theorem liftSemi_tmul (f : M →ₛₗ[algebraMap R R'] N) (r : R') (m : M) :
    liftSemi f (r ⊗ₜ m) = r • f m := rfl

end Lift

section Level

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']

def SemiBialgHom.prim (f : SemiBialgHom σ A A') :
    LinearMap.ker (cobOne R A) →ₛₗ[σ] LinearMap.ker (cobOne R' A') where
  toFun b := ⟨f b.1, by
    have hb : cobOne R A b.1 = 0 := b.2
    have hone : SemiBialgHom.lin f 1 = 1 := f.toRingHom.map_one
    have h := congrArg (SemiBialgHom.two f) hb
    simpa only [LinearMap.mem_ker, cobOne_apply, map_sub, SemiBialgHom.two_comul,
      TensorProduct.map_tmul, hone, SemiBialgHom.lin_apply, map_zero] using h⟩
  map_add' _ _ := Subtype.ext (f.toRingHom.map_add _ _)
  map_smul' _ _ := Subtype.ext (f.smul_map _ _)

@[simp] theorem SemiBialgHom.prim_val (f : SemiBialgHom σ A A') (b : LinearMap.ker (cobOne R A)) :
    (f.prim b).1 = f b.1 := rfl

theorem isPrimitiveElem_of_mem_ker {b : A} (hb : b ∈ LinearMap.ker (cobOne R A)) :
    IsPrimitiveElem R b := by
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero] at hb
  exact hb

theorem evalAt_mul [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ ψ : CartierDual R A) :
    CartierDual.evalAt R A b.1 (φ * ψ) =
      counitAlgHom R (CartierDual R A) φ • CartierDual.evalAt R A b.1 ψ +
        counitAlgHom R (CartierDual R A) ψ • CartierDual.evalAt R A b.1 φ :=
  (CartierDual.isPrimitiveElem_iff_mul b.1).1 (isPrimitiveElem_of_mem_ker b.2) φ ψ


variable (R A) in
def primTangent [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    LinearMap.ker (cobOne R A) →ₗ[R] Module.Dual R (Cot R (CartierDual R A)) where
  toFun b := AugCot.lift _ (CartierDual.evalAt R A b.1) (evalAt_mul b)
  map_add' b b' := AugCot.hom_ext fun φ => by simp
  map_smul' r b := AugCot.hom_ext fun φ => by simp

@[simp] theorem primTangent_d [Module.Finite R A] [Module.Projective R A] [IsCocomm R A]
    (b : LinearMap.ker (cobOne R A)) (φ : CartierDual R A) :
    primTangent R A b (dUnit (R := R) φ) = φ b.1 := AugCot.lift_d _ _ (evalAt_mul b) φ

variable [IsCocomm R A] [IsCocomm R' A']




end Level

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

def resOne (n : ℕ) : G.A (n + 1) →ₐc[R] G.A 1 :=
  Nat.rec (motive := fun n => G.A (n + 1) →ₐc[R] G.A 1) (BialgHom.id R _)
    (fun n f => f.comp (G.res (n + 1))) n

@[simp] theorem resOne_zero (a : G.A 1) : G.resOne 0 a = a := rfl

@[simp] theorem resOne_succ (n : ℕ) (a : G.A (n + 2)) :
    G.resOne (n + 1) a = G.resOne n (G.res (n + 1) a) := rfl

theorem resOne_surjective (n : ℕ) : Function.Surjective (G.resOne n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (G.res_surjective (n + 1))

theorem resOne_funs (B : G.funs) (n : ℕ) : G.resOne n (B.1 (n + 1)) = B.1 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [resOne_succ, B.2, ih]

theorem resOne_mulBy (n : ℕ) (a : G.A (n + 1)) :
    G.resOne n (mulBy R _ p a) = algebraMap R _ (counit a) := by
  have h := G.mulBy_pow_self 1 (G.resOne n a)
  rw [pow_one, CoalgHomClass.counit_comp_apply] at h
  rw [map_mulBy, h]

theorem resOne_mulP (n : ℕ) (a : G.A n) :
    G.resOne n (G.mulP n a) = algebraMap R _ (counit a) := by
  obtain ⟨b, rfl⟩ := G.res_surjective n a
  rw [mulP_res, resOne_mulBy, CoalgHomClass.counit_comp_apply]

def transl (n : ℕ) : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1 :=
  (Algebra.TensorProduct.map (AlgHom.id R _) (G.resOne n : G.A (n + 1) →ₐ[R] G.A 1)).comp
    (comulAlgHom R _)

theorem transl_apply (n : ℕ) (a : G.A (n + 1)) :
    G.transl n a = (G.resOne n : G.A (n + 1) →ₗ[R] G.A 1).lTensor _ (comul a) := rfl

theorem transl_res (n : ℕ) (a : G.A (n + 2)) :
    G.transl n (G.res (n + 1) a) =
      (G.res (n + 1) : G.A (n + 2) →ₗ[R] G.A (n + 1)).rTensor _ (G.transl (n + 1) a) := by
  rw [transl_apply, transl_apply, ← pullTwo_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul x y => simp

theorem transl_mulP (n : ℕ) (a : G.A n) : G.transl n (G.mulP n a) = G.mulP n a ⊗ₜ 1 := by
  rw [transl_apply, ← pullTwo_comul]
  conv_rhs => rw [← (TensorProduct.rid R _).apply_symm_apply a, TensorProduct.rid_symm_apply,
    ← Coalgebra.lTensor_counit_comul]
  generalize comul (R := R) a = t
  induction t with
  | add x y hx hy => simp only [map_add (f := _), add_tmul, hx, hy]
  | tmul x y => simp [resOne_mulP, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem pullbackTwo_mulP_injective (n : ℕ) : Function.Injective (pullbackTwo (G.mulP n)) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Test.mulP_injective G n) (Test.mulP_injective G n)

theorem res_eq_zero_of_cobOne_eq_zero (hp : (p : R) = 0) (n : ℕ) {b : G.A (n + 1)}
    (hb : cobOne R _ b = 0) : G.res n b = 0 :=
  Test.mulP_injective G n (by
    rw [mulP_res, (mulBy_of_cobOne_eq_zero hb p).1, ← Nat.cast_smul_eq_nsmul R, hp, zero_smul,
      map_zero])

theorem eq_zero_of_cob_eq_zero (hp : (p : R) = 0) {B : G.funs} (hB : G.cob B = 0) : B = 0 :=
  Subtype.ext (funext fun n => (B.2 n).symm.trans (G.res_eq_zero_of_cobOne_eq_zero hp n
    (congrArg (fun c : G.cocycles => c.1 (n + 1)) hB)))

theorem rigOfOmega_injective_of_eq_zero (hp : (p : R) = 0) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero hp (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

theorem omegaLevel_one_bijective (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun w hw => ?_, G.omegaLevel_surjective 1⟩
  obtain ⟨v, rfl⟩ := (G.omega_val_eq_zero_iff 1 w).1 hw
  rw [pow_one, hp, zero_smul]

def primLie : LinearMap.ker (cobOne R (G.A 1)) →ₗ[R] G.dual.Lie :=
  (G.dual.omegaLevel 1).dualMap ∘ₗ primTangent R (G.A 1)

theorem primLie_apply (b : LinearMap.ker (cobOne R (G.A 1))) (w : G.dual.omega)
    (φ : CartierDual R (G.A 1)) (h : w.1 1 = dUnit (R := R) φ) : G.primLie b w = φ b.1 :=
  (congrArg (primTangent R (G.A 1) b) h).trans (primTangent_d b φ)

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecSigmaBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_sigma_res_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  first | (exact @GlobalTheory.EtC.sec_sigma_bijective) | (exact GlobalTheory.EtC.sec_sigma_bijective) | (intros; apply GlobalTheory.EtC.sec_sigma_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionInverseIntoSliceStatement
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_inverse_into_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  first | exact @GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | exact GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquivStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i ↦ Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  first | exact @GlobalTheory.EtC.spec_pi_cofan_isColimit | exact GlobalTheory.EtC.spec_pi_cofan_isColimit | (intros; apply GlobalTheory.EtC.spec_pi_cofan_isColimit <;> assumption)
end

