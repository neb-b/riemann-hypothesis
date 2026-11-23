module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactTypeInCompactStableSubmodule
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilated
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.ExtKill

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X w = dRep σ (P * X * P⁻¹) w := by
  unfold dRep
  simp only [exp_smul_conj hP]

theorem smoothVec_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem kill_and_weight : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ v : M.Vec, IsExtVec M v → ∀ (ρ : D.what₂.Tau) (p : ℕ) (s : Bool), (∀ a : Fin V.rank, M.ε ρ a = if (a : ℕ) < p then s else !s) → (∀ a b, KillPair (M.ε ρ) a b → RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (T v) = 0) ∧ ∀ (t : Fin V.rank → ℝ) (g : GA D V), T v (g * atTau θ V ρ ((M.fr ρ)⁻¹ * Matrix.diagonal (fun a => Complex.exp ((t a : ℂ) * Complex.I)) * M.fr ρ)) = Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) * T v g := by
  intro D θ V S M J χ T hθ hT v hv ρ p s hε
  have hP := M.fr_unit ρ
  have hG := M.fr_gram ρ
  obtain ⟨-, hlow, hwt⟩ := hv ρ
  have hlow' : (v ρ : M.H ρ) ∈ lowKSub (M.ε ρ) (M.lam ρ) (M.σ ρ) := hlow
  refine ⟨fun a b hab => ?_, fun t g => ?_⟩
  · obtain ⟨hs, hd⟩ := _root_.GlobalTheory.HolRead.MultDer.rder_eq D θ V S M J χ T hθ hT v ρ
    have hs' := smoothVec_conj (σ := M.σ ρ) hP hG hs
    set Z := (M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ with hZ
    obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V ρ Z
    have hXY := GlobalTheory.SmoothAutCheck.parts_sum V ρ Z
    unfold RderC
    generalize (1 / 2 : ℂ) • (Z + conjAt V ρ Z) = X at hX hXY ⊢
    generalize (1 / (2 * Complex.I)) • (Z - conjAt V ρ Z) = Y at hY hXY ⊢
    obtain ⟨u, hu, eu⟩ := hd X hX
    obtain ⟨u', hu', eu'⟩ := hd Y hY
    have hX' := lie_conj hP hG hX
    have hY' := lie_conj hP hG hY
    have hE : M.fr ρ * X * (M.fr ρ)⁻¹ + Complex.I • (M.fr ρ * Y * (M.fr ρ)⁻¹) = Matrix.single a b 1 := by
      rw [← conj_cancel hP (Matrix.single a b 1), ← hZ, ← hXY]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have key : dRep (M.σ ρ) (M.fr ρ * X * (M.fr ρ)⁻¹) (v ρ : M.H ρ) +
        Complex.I • dRep (M.σ ρ) (M.fr ρ * Y * (M.fr ρ)⁻¹) (v ρ : M.H ρ) = 0 := by
      rcases hab with h | h | h
      · exact _root_.GlobalTheory.HolRead.KCpt.extremal_killed_compact _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inl h) _ hX' _ hY' hE
      · exact _root_.GlobalTheory.HolRead.KCpt.extremal_killed_compact _ _ _ _ _ (M.ds ρ).2.2.1 _ hlow' hs' hwt a b (Or.inr h) _ hX' _ hY' hE
      · exact _root_.GlobalTheory.LowestKilled.lowK_killed _ _ _ _ _ p s hε (M.enum ρ).1 (M.ds ρ) _ hlow' hs' a b h.1 h.2 _ hX' _ hY' hE
    have h0 : u + Complex.I • u' = 0 := by
      apply Subtype.ext
      show (u : M.H ρ) + Complex.I • (u' : M.H ρ) = 0
      rw [hu, hu', ← key, ← dRep_conj hP, ← dRep_conj hP]
      rfl
    have hsmul : T (Function.update v ρ (Complex.I • u')) = Complex.I • T (Function.update v ρ u') := by
      simpa only [RingHom.id_apply] using T.map_update_smul v ρ Complex.I u'
    rw [eu, eu', ← hsmul, ← T.map_update_add, h0, T.map_update_zero]
  · have hK := Formalism.IndefR.FWT.diag_mem (ε := M.ε ρ) t
    have hg := GlobalTheory.HolDict.ModelRep.conj_mem_inv hP hG (kset_uj hK)
    have h := hT.equiv ρ _ hg v (Complex.exp (((∑ a, extWt M ρ a * t a : ℝ) : ℂ) * Complex.I) • v ρ) (by
      unfold DSModel.rep
      rw [conj_cancel hP, hwt t hK]
      rfl)
    rw [T.map_update_smul, Function.update_eq_self] at h
    exact (congrFun h g).symm

end GlobalTheory.HolRead.ExtKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCoeffCharpolyRevNegEqSum
section
open Polynomial Matrix

namespace GlobalTheory.GoodTop

theorem sum_det_submatrix_image_eq {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) (n : ℕ) (s : Finset r) (hs : s.card = n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n → r => Finset.univ.image p = s),
      (M.submatrix p p).det =
    (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
  classical
  have hc : Fintype.card (Fin n) = Fintype.card s := by simp [hs]
  have h1 : ∑ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
      (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
    have : ∀ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
        (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
      intro e
      rw [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]
  rw [← h1]
  symm
  refine Finset.sum_bij (fun e _ => Subtype.val ∘ e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · intro e _ e' _ h
    ext i
    exact congrFun h i
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let f : Fin n → s := fun i => ⟨p i, hp ▸ Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [← hp] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a, rfl⟩
    have hb : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩
    exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩

theorem factorial_mul_coeff_charpolyRev_neg {A : Type} [CommRing A] {r : Type} [Fintype r]
    [DecidableEq r] (M : Matrix r r A) (n : ℕ) :
    (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  classical
  have hrev : (-M).charpolyRev = det (1 + (X : A[X]) • M.map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M, smul_neg, neg_neg]
  have hdet : ∀ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) = (M.submatrix p p).det := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hrev, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
  simp only [hdet]
  rw [← Finset.sum_filter_of_ne (s := Finset.univ)
    (p := fun p : Fin n → r => Finset.univ.image p ∈ (Finset.univ : Finset r).powersetCard n)]
  · rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset r).powersetCard n)
      (g := fun p : Fin n → r => Finset.univ.image p) (fun p hp => (Finset.mem_filter.mp hp).2)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← sum_det_submatrix_image_eq M n s (Finset.mem_powersetCard.mp hs).2]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hs, h⟩, fun h => h.2⟩
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact hp (Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]))
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    simp

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDimStableIsSumOfKTypes
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace Matrix

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sumTypes_conjT_mem {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : gᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu), ?_⟩
  have h := congrArg Matrix.conjTranspose hc
  simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at h
  exact h.symm

theorem sumTypes_mul_conjT {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g * gᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 hg.1

theorem sumTypes_inner {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) (r v : H) :
    ⟪r, σ g v⟫_ℂ = ⟪σ gᴴ r, v⟫_ℂ := by
  have hK := Formalism.REAL.kFacts n ε
  have hgU : g ∈ UJset ε := hK.1 g hg
  have hgU' : gᴴ ∈ UJset ε := hK.1 _ (sumTypes_conjT_mem hg)
  let f : H →ₗᵢ[ℂ] H := { (σ g : H →ₗ[ℂ] H) with norm_map' := hσ.2.1 g hgU }
  have e : σ g (σ gᴴ r) = r := by
    have h1 := hσ.1.2 g hgU gᴴ hgU'
    rw [sumTypes_mul_conjT hg, hσ.1.1] at h1
    have := congrArg (fun T : H →L[ℂ] H => T r) h1
    simpa using this.symm
  calc ⟪r, σ g v⟫_ℂ = ⟪f (σ gᴴ r), f v⟫_ℂ := by
        show ⟪r, σ g v⟫_ℂ = ⟪σ g (σ gᴴ r), σ g v⟫_ℂ
        rw [e]
    _ = ⟪σ gᴴ r, v⟫_ℂ := f.inner_map_map _ _

theorem finDimStable_isSumOfKTypes : SumTypes := by
  intro n ε H _ _ σ hσ S hSfd hSK
  set R : Submodule ℂ H := sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} with hR
  have hRS : R ≤ S := sSup_le fun S' hS' => hS'.1
  have : FiniteDimensional ℂ R := Submodule.finiteDimensional_of_le hRS
  have hRK : Formalism.MainNotions.S.IsKStableOn ε σ R := by
    intro g hg v hv
    have hle : R ≤ Submodule.comap (σ g : H →ₗ[ℂ] H) R := sSup_le fun S' hS' x hx => by
      obtain ⟨μ, hμ⟩ := hS'.2
      exact Submodule.mem_sSup_of_mem hS' (hμ.2.1 g hg x hx)
    exact hle hv
  have hRoK : Formalism.MainNotions.S.IsKStableOn ε σ Rᗮ := by
    intro g hg v hv r hr
    rw [sumTypes_inner hσ hg]
    exact hv _ (hRK _ (sumTypes_conjT_mem hg) r hr)
  set T : Submodule ℂ H := S ⊓ Rᗮ
  have hT : T = ⊥ := by
    by_contra h0
    have : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨μ, S', hS'T, hS'⟩ := GlobalTheory.KTypeExists.exists_kType n ε H σ hσ T inferInstance
      (fun g hg v hv => Submodule.mem_inf.2 ⟨hSK g hg v (Submodule.mem_inf.1 hv).1, hRoK g hg v (Submodule.mem_inf.1 hv).2⟩) h0
    obtain ⟨v, hv, hv0, -⟩ := hS'.2.2.2.1
    have hvR : v ∈ R := Submodule.mem_sSup_of_mem (show S' ∈ {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'} from ⟨hS'T.trans inf_le_left, μ, hS'⟩) hv
    have hvRo : v ∈ Rᗮ := (hS'T hv).2
    exact hv0 (inner_self_eq_zero.1 (hvRo v hvR))
  intro v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := R.exists_add_mem_mem_orthogonal v
  have hzS : z ∈ S := by
    have := sub_mem hv (hRS hy)
    simpa using this
  have hz0 : z ∈ T := ⟨hzS, hz⟩
  rw [hT, Submodule.mem_bot] at hz0
  rw [hz0, add_zero]
  exact hy

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEqStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_eq_of_section_components_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ x y : finU (E := E) (n := n), (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  first | exact @GlobalTheory.BCT.finU_eq_of_loc | exact GlobalTheory.BCT.finU_eq_of_loc | (intros; apply GlobalTheory.BCT.finU_eq_of_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUnStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (x : finU (E := E) (n := n)), cLoc w (x : UA E n) ∈ UL n w := by
  first | exact @GlobalTheory.BCT.cLoc_mem_UL | exact GlobalTheory.BCT.cLoc_mem_UL | (intros; apply GlobalTheory.BCT.cLoc_mem_UL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosedRingStableSubgroupAbelianNoTorsion
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.OStableAbelian

theorem restrict : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (B N : Over (Sp k)) [GrpObj B] [GrpObj N] (act : OAct O B) (ν : N ⟶ B), IsMonHom ν → IsClosedImmersion ν.left → IsReduced N.left → (∀ a : O, Set.range (ν ≫ act.act a).left ⊆ Set.range ν.left) → ∃ act' : OAct O N, ∀ a, act'.act a ≫ ν = ν ≫ act.act a := by
  intro k _ O _ B N _ _ act ν hν hνc hred h
  have : Mono ν := Over.mono_of_mono_left _
  have hl : ∀ a : O, ∃ l : N ⟶ N, l ≫ ν = ν ≫ act.act a := fun a => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (ν ≫ act.act a).left ν.left (h a)
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, Over.comp_left, Category.assoc, (act.act a).w, ν.w]
  choose l hl using hl
  have hm : ∀ a, IsMonHom (l a) := fun a => by
    have := act.hom a
    constructor
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hl, IsMonHom.mul_hom_assoc, IsMonHom.mul_hom,
        Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc, hl]
  refine ⟨⟨l, hm, ?_, ?_, ?_⟩, hl⟩
  · rw [← cancel_mono ν, hl, act.one, Category.id_comp, Category.comp_id]
  · intro a b
    rw [← cancel_mono ν, hl, act.mul, Category.assoc, hl, reassoc_of% (hl a)]
  · intro a b
    rw [← cancel_mono ν, hl, act.add, MonObj.comp_mul, MonObj.mul_comp, hl, hl]

theorem range_comp_subset : ∀ (k : Type) [Field k] (N₀ N : Over (Sp k)) [GrpObj N₀] [GrpObj N] (ν₀ : N₀ ⟶ N) (f : N ⟶ N), IsMonHom ν₀ → IsMonHom f → IsOpenImmersion ν₀.left → IsClosedImmersion ν₀.left → ConnectedSpace N₀.left → Set.range (ν₀ ≫ f).left ⊆ Set.range ν₀.left := by
  intro k _ N₀ N _ _ ν₀ f hν₀ hf ho hc hconn
  haveI := ho
  haveI := hc
  have hcl : IsClopen (Set.range ν₀.left) :=
    ⟨ν₀.left.isClosedEmbedding.isClosed_range, ν₀.left.isOpenEmbedding.isOpen_range⟩
  have hpre : _root_.IsPreconnected (Set.range (ν₀ ≫ f).left) :=
    isPreconnected_range (ν₀ ≫ f).left.continuous
  let t : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  have e2 : η[N₀] ≫ ν₀ ≫ f = η[N₀] ≫ ν₀ := by
    rw [IsMonHom.one_hom_assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  have he : (η[N₀] ≫ ν₀ ≫ f).left t ∈ Set.range (ν₀ ≫ f).left ∩ Set.range ν₀.left := by
    refine ⟨⟨η[N₀].left t, rfl⟩, ?_⟩
    rw [e2]
    exact ⟨η[N₀].left t, rfl⟩
  exact hpre.subset_isClopen hcl ⟨_, he⟩

theorem finite_of_isClosed_of_no_torsion : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (B : Over (Sp k)) [GrpObj B] (act : OAct (𝓞 E) B) (π : 𝓞 E), IsAbelianScheme B → π ≠ 0 → ¬ IsUnit π → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ (a : 𝓞 E), ∀ x ∈ C, x ≫ act.act a ∈ C) → (∀ x ∈ C, x ≫ act.act π = 1 → x = 1) → Finite C := by
  intro E _ _ k _ _ _ B _ act π hB hπ0 hπu C Z hZ hC hstab htor
  have := hB.smooth
  have := hB.proper
  have := hB.comm
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    GlobalTheory.ReducedSubgroup.exists_smooth_closed_subgroup k B inferInstance C Z hZ hC
  have hNp : IsProper N.hom := by rw [← ν.w]; infer_instance
  obtain ⟨N₀, _, ν₀, g, hν₀, hν₀o, hν₀c, hgc, hg, -⟩ :=
    GlobalTheory.exists_neutralComponent k N hNs inferInstance
  have : IsClosedImmersion (ν₀ ≫ ν).left := by rw [Over.comp_left]; infer_instance
  have : Mono (ν₀ ≫ ν) := Over.mono_of_mono_left _
  have : Mono ν := Over.mono_of_mono_left _
  have hA : IsAbelianScheme N₀ :=
    { comm := GlobalTheory.AbelianSubgroupFinite.isCommMonObj_of_mono (ν₀ ≫ ν)
      smooth := SmoothOfRelativeDimension.smooth g N₀.hom
      proper := by rw [← ν₀.w]; infer_instance
      geomConnected := hgc }
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ ν ∈ C := fun x => by
    rw [hC, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  have : IsReduced (𝟙_ (Over (Sp k))).left := inferInstanceAs (IsReduced (Sp k))
  have hlift : ∀ x ∈ C, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x := fun x hx => by
    obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset x.left ν.left
      (hr ▸ (hC x).1 hx)
    exact ⟨Over.homMk l (by rw [← ν.w, ← Category.assoc, hl, x.w]), Over.OverMorphism.ext hl⟩
  have hNred : IsReduced N.left := isReduced_of_smooth N.hom
  obtain ⟨actN, hactN⟩ := restrict k (𝓞 E) B N act ν hν hνc hNred fun a => by
    rw [hr]
    refine GlobalTheory.ReducedSubgroup.range_subset_of_points (ν ≫ act.act a) hZ fun x => ?_
    rw [← Category.assoc, ← hC]
    exact hstab a _ (hmem x)
  have : Smooth N₀.hom := SmoothOfRelativeDimension.smooth g N₀.hom
  have hN₀red : IsReduced N₀.left := isReduced_of_smooth N₀.hom
  have hconn : ConnectedSpace N₀.left := GeometricallyConnected.connectedSpace_of_subsingleton N₀.hom
  obtain ⟨act₀, hact₀⟩ := restrict k (𝓞 E) N N₀ actN ν₀ hν₀ hν₀c hN₀red fun a =>
    range_comp_subset k N₀ N ν₀ (actN.act a) hν₀ (actN.hom a) hν₀o hν₀c hconn
  have h1 : Finite (𝟙_ (Over (Sp k)) ⟶ N₀) := by
    refine _root_.GlobalTheory.NoPiTorsion.finite_points E k N₀ act₀ π g hA hg hπ0 hπu fun x hx => ?_
    have h2 : x ≫ ν₀ ≫ ν = 1 := by
      refine htor _ (by rw [← Category.assoc]; exact hmem _) ?_
      have e : (x ≫ ν₀ ≫ ν) ≫ act.act π = (x ≫ act₀.act π) ≫ ν₀ ≫ ν := by
        simp only [Category.assoc, ← hactN, reassoc_of% (hact₀ π)]
      rw [e, hx, MonObj.one_comp]
    rw [← cancel_mono (ν₀ ≫ ν), h2, MonObj.one_comp]
  have := GlobalTheory.TorsionDense.finite_points_of_isOpenImmersion ν₀
  refine Finite.of_surjective (fun x : 𝟙_ (Over (Sp k)) ⟶ N => (⟨x ≫ ν, hmem x⟩ : C)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hlift x hx
  exact ⟨y, Subtype.ext hy⟩

end GlobalTheory.OStableAbelian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegularStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  first | (exact @GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular) | (exact GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular) | (intros; apply GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProductsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ m) → (∀ τ, p τ ≤ n ∧ q τ ≤ n) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) → Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) = ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  first | exact @GlobalTheory.LowRowFock.fock_delta | exact GlobalTheory.LowRowFock.fock_delta | (intros; apply GlobalTheory.LowRowFock.fock_delta <;> assumption)
end

