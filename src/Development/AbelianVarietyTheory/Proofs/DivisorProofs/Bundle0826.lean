module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.SmoothCyclic

open Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GardingVec GlobalTheory.LowTypeRestriction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section Conj
variable {n : ℕ}

theorem conj_lie {J G A B X : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (h : Bᴴ * J * B = G)
    (hX : Xᴴ * J + J * X = 0) : (A * X * B)ᴴ * G + G * (A * X * B) = 0 := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hBA' : Aᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  calc (A * X * B)ᴴ * G + G * (A * X * B)
      = Bᴴ * (Xᴴ * (Aᴴ * Bᴴ) * J + J * (B * A) * X) * B := by
        rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_of_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (A * X * B)) = A * NormedSpace.exp (t • X) * B := by
  have hB : B = A⁻¹ := (Matrix.inv_eq_right_inv hAB).symm
  rw [hB, ← Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ hAB)]
  simp

theorem list_prod_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun a => A * a * B).prod = A * l.prod * B := by
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  induction l with
  | nil => simp [hAB]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc A * a * B * (A * l.prod * B) = A * a * (B * A) * l.prod * B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem expProd_conj {A B : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * B))).prod
      = A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * B := by
  rw [← list_prod_conj hAB, List.map_ofFn]
  simp only [exp_conj_of_mul hAB, Function.comp_def]

end Conj

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def lieJ (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exp_memJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) (t : ℝ) : NormedSpace.exp (t • X) ∈ UJset ε :=
  exp_mem (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hX t

theorem expProd_memJ {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ} (hX : ∀ i, Xs i ∈ lieJ ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε :=
  list_prod_mem (G := Formalism.REAL.Jm ε) _ fun g hg => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact exp_memJ (hX i) _

theorem rep_mul (hσ : IsURepOn (UJset ε) σ) {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε)
    (v : H) : σ a (σ b v) = σ (a * b) v := by
  rw [hσ.1.2 _ ha _ hb]; rfl

def smSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {w | SmoothVec (lieJ ε : Set _) σ w}
  add_mem' := fun ha hb k Xs hX => by simpa only [map_add (f := _)] using (ha k Xs hX).add (hb k Xs hX)
  zero_mem' := fun k Xs _ => by simpa only [map_zero] using contDiff_const
  smul_mem' := fun c w hw k Xs hX => by simpa only [map_smul] using (hw k Xs hX).const_smul c

theorem hasDerivAt_dRep {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieJ ε) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) w) (dRep σ X w) 0 := by
  have h := (hw 1 (fun _ => X) fun _ => hX).comp (contDiff_pi.2 fun _ : Fin 1 => (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)))
  have h2 : ContDiff ℝ ∞ fun t : ℝ => σ (NormedSpace.exp (t • X)) w := by
    simpa [Function.comp_def] using h
  exact (h2.differentiable (by simp) 0).hasDerivAt

theorem dRep_mem (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smSub ε σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieJ ε) : dRep σ X w ∈ smSub ε σ := by
  intro k Xs hXs
  have h := hw (k + 1) (Fin.snoc Xs X) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hX
    · simpa using hXs j)
  have hs : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ => (Fin.snoc z.1 z.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simpa [Function.comp_def] using (contDiff_apply ℝ (fun _ => ℝ) j).comp (contDiff_fst (F := ℝ))
  have h2 : ContDiff ℝ ∞ fun z : (Fin k → ℝ) × ℝ =>
      σ ((List.ofFn fun i => NormedSpace.exp (z.1 i • Xs i)).prod) (σ (NormedSpace.exp (z.2 • X)) w) := by
    convert h.comp hs using 2 with z
    rw [rep_mul hσ (expProd_memJ hXs _) (exp_memJ hX _)]
    simp only [Function.comp_def, List.ofFn_succ_last, Fin.snoc_castSucc, Fin.snoc_last, List.prod_append,
      List.prod_singleton]
  have h3 := ContDiff.fderiv (𝕜 := ℝ) (m := ∞) (n := ∞) (f := fun (t : Fin k → ℝ) (s : ℝ) =>
      σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ (NormedSpace.exp (s • X)) w))
      (g := fun _ => 0) h2 contDiff_const (by simp)
  convert h3.clm_apply (contDiff_const (c := (1 : ℝ))) using 2 with t
  exact (((σ _).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_dRep hw hX)).deriv.symm

variable {φ : Matrix (Fin n) (Fin n) ℂ → ℝ}

section Transport
variable {P G : Matrix (Fin n) (Fin n) ℂ}

theorem smoothVec_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) (w : H) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w ↔ w ∈ smSub ε σ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  constructor
  · intro hw k Xs hX
    have := hw k (fun i => P⁻¹ * Xs i * P) fun i => conj_lie h2 h (hX i)
    convert this using 2 with t
    rw [expProd_conj h2]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro hw k Xs hX
    simpa only [expProd_conj h1] using hw k (fun i => P * Xs i * P⁻¹) fun i => conj_lie h1 h' (hX i)

theorem sobCont_transport (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) ℓ) : Sobolev₂ (lieJ ε : Set _) σ ℓ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h' : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  obtain ⟨S, C, hS, hb⟩ := hℓ
  have e : dRep (fun g => σ (P * g * P⁻¹)) = fun X w => dRep σ (P * X * P⁻¹) w := by
    funext X w
    simp only [dRep, exp_conj_of_mul h1]
  refine ⟨S.map fun l => l.map fun X => P * X * P⁻¹, C, fun l hl X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact conj_lie h1 h' (hS l' hl' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using
      hb w ((smoothVec_transport hP h w).2 hw)

end Transport

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_eq {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ = smSub (M.ε τ) (M.σ τ) := by
  rw [← Submodule.span_eq (smSub (M.ε τ) (M.σ τ))]
  exact congrArg (Submodule.span ℂ) (Set.ext fun w => smoothVec_transport (M.fr_unit τ) (M.fr_gram τ) w)

end GlobalTheory.SmoothCyclic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCompactCharacterVanishing
section
open MeasureTheory Matrix

namespace GlobalTheory

theorem typeFunction_unip_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : ℕ} (e : ι ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → K) → GL ι K)
    (hu : ∀ X, (u X : Matrix ι ι K) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (X Y : Fin a → Fin b → K) : u (Y + X) = u X * u Y := by
  apply Units.ext
  rw [Units.val_mul, hu, hu, hu]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.of_add_of]

theorem typeFunction_constantTerm_eq_zero :
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro K _ _ _ _ _ _ ι _ _ J hJo hJc χ hχ hnt f hf1 hf0
  have hR : ∀ g j (hj : j ∈ J), f (g * j) = f g * (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hg hj), hf1 g hg]
      have : (⟨g * j, J.mul_mem hg hj⟩ : J) = ⟨g, hg⟩ * ⟨j, hj⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_right hj).1 h)), zero_mul]
  have hL : ∀ g j (hj : j ∈ J), f (j * g) = (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * f g := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hj hg), hf1 g hg]
      have : (⟨j * g, J.mul_mem hj hg⟩ : J) = ⟨j, hj⟩ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_left hj).1 h)), mul_zero]
  have hRk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (g * y) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hR g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, mul_one] at this
    exact this
  have hLk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (y * g) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hL g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, one_mul] at this
    exact this
  have hNo : IsOpen ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)),
      hNo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Subgroup.one_mem _
    · intro x hx
      have := hRk _ hx g
      rwa [mul_inv_cancel_left] at this
  · exact HasCompactSupport.intro' hJc (J.isClosed_of_isOpen hJo) (fun g hg => hf0 g hg)
  · intro x hx y hy g
    rw [hRk y hy, hLk x hx]
  · intro a b e ha hb μ hμ u hu g h
    obtain ⟨Y, hY, hne⟩ := hnt a b e ha hb u hu h
    have key : ∀ X, f (g * (h⁻¹ * u (Y + X) * h)) =
        f (g * (h⁻¹ * u X * h)) * (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) := by
      intro X
      rw [← hR _ _ hY, typeFunction_unip_add e u hu]
      congr 1
      group
    have h1 := integral_add_left_eq_self (μ := μ) (fun X => f (g * (h⁻¹ * u X * h))) Y
    simp only [key] at h1
    rw [integral_mul_const] at h1
    have hc : (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      intro hc
      exact hne (inv_eq_one.1 (Units.val_eq_one.1 hc))
    by_contra hI
    exact hc (mul_left_cancel₀ hI (h1.trans (mul_one _).symm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartIndependentClosedField
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DepthField

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth

section Monomials

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem toE_mono {x y : WithTop ℝ} (h : x ≤ y) : toE x ≤ toE y := WithBot.coe_le_coe.2 h

theorem le_toE_sum {ι : Type} (S : Finset ι) (g : ι → C) {r : EReal} (h : ∀ i ∈ S, r ≤ toE (v (g i))) :
    r ≤ toE (v (∑ i ∈ S, g i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, v.map_zero]; exact le_top
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine le_trans ?_ (toE_mono (v.map_add _ _))
    rcases min_choice (v (g a)) (v (∑ i ∈ S, g i)) with e | e <;> rw [e] <;> assumption

theorem derivAt0_subst {σ τ : Type} {E : σ → MvPowerSeries τ C} (hE : HasSubst E) (P : MvPolynomial τ C)
    (f : MvPowerSeries σ C) : ∃ S : Finset (σ →₀ ℕ),
      derivAt0 P (subst E f) = ∑ β ∈ S, coeff β f * derivAt0 P (subst E (monomial β (1 : C))) := by
  classical
  refine ⟨P.support.biUnion fun α => (coeff_subst_finite hE f α).toFinset, ?_⟩
  simp only [derivAt0, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_subst hE, finsum_eq_sum_of_support_subset (s := P.support.biUnion
    fun α => (coeff_subst_finite hE f α).toFinset) _ fun β hβ => by
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨α, hα, (Set.Finite.mem_toFinset _).2 hβ⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [subst_monomial hE, map_one, one_mul, smul_eq_mul]
  ring

variable {κ : Type} {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]

theorem hasSubst_lin (u : ∀ b, ι b → Fin (d b) → C) (b : κ) :
    ∀ e : Fin (d b), constantCoeff (∑ a, u b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := by
  intro e
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum]

theorem hasSubst_expAlong [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C) :
    HasSubst (expAlong G u) :=
  hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)) (hasSubst_lin u x.1)
      ((isExp_expOf (G x.1)).1 x.2)

theorem depth_eq_iInf_monomial [Finite κ] (G : ∀ b, LogFGL v (d b)) (u : ∀ b, ι b → Fin (d b) → C)
    (P : MvPolynomial (Σ b, ι b) C) :
    depth G u P = ⨅ β : (Σ b, Fin (d b)) →₀ ℕ,
      toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  classical
  refine le_antisymm (le_iInf fun β => iInf_le_of_le ⟨monomial β 1, fun α => ?_⟩ le_rfl) (le_iInf fun f => ?_)
  · rw [IsIntV, coeff_monomial]
    split_ifs <;> simp
  · obtain ⟨S, hS⟩ := derivAt0_subst (hasSubst_expAlong G u) P f.1
    rw [hS]
    refine le_toE_sum S _ fun β _ => iInf_le_of_le β (toE_mono ?_)
    rw [v.map_mul]
    exact le_add_of_nonneg_left (f.2 β)

end Monomials

section Map

variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {v : AddValuation C (WithTop ℝ)}
  {w : AddValuation K (WithTop ℝ)}

theorem derivAt0_map {σ : Type} (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.map φ P) (MvPowerSeries.map φ g) = φ (derivAt0 P g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [derivAt0, MvPolynomial.support_map_of_injective _ φ.injective, map_sum, map_mul,
    MvPolynomial.coeff_map, coeff_map, mfact, Finsupp.prod, map_prod, map_natCast]

theorem expOf_map {d : ℕ} (G : LogFGL w d) (G' : LogFGL v d)
    (h : ∀ a, G'.lg a = MvPowerSeries.map φ (G.lg a)) (a : Fin d) :
    expOf G' a = MvPowerSeries.map φ (expOf G a) := by
  have he := isExp_expOf G
  have : IsExp G' fun a => MvPowerSeries.map φ (expOf G a) := by
    refine ⟨fun a => by simp [he.1 a], fun a => ?_⟩
    rw [h, ← map_subst (hasSubst_of_constantCoeff_zero he.1), he.2, map_X]
  rw [← isExp_unique G' this]

theorem depth_map {κ : Type} [Finite κ] {d : κ → ℕ} {ι : κ → Type} [∀ b, Fintype (ι b)]
    (hv : ∀ x, v (φ x) = w x) (G : ∀ b, LogFGL w (d b)) (G' : ∀ b, LogFGL v (d b))
    (h : ∀ b a, (G' b).lg a = MvPowerSeries.map φ ((G b).lg a)) (u : ∀ b, ι b → Fin (d b) → K)
    (P : MvPolynomial (Σ b, ι b) K) :
    depth G' (fun b a e => φ (u b a e)) (MvPolynomial.map φ P) = depth G u P := by
  have hE : expAlong G' (fun b a e => φ (u b a e)) = fun x => MvPowerSeries.map φ (expAlong G u x) := by
    funext x
    simp only [expAlong]
    rw [map_subst (hasSubst_of_constantCoeff_zero (hasSubst_lin u x.1)), expOf_map φ _ _ (h x.1)]
    congr 1
    funext e
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, smul_eq_C_mul]
  rw [depth_eq_iInf_monomial, depth_eq_iInf_monomial, hE]
  refine iInf_congr fun β => ?_
  rw [← hv, ← derivAt0_map, map_subst (hasSubst_expAlong G u), map_monomial, φ.map_one]

theorem detPow_map (i c : ℕ) : MvPolynomial.map φ (detPow K i c) = detPow C i c := by
  rw [detPow, detPow, map_pow, RingHom.map_det]
  congr 2
  ext a b
  simp

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv i f) = MvPowerSeries.pderiv i (MvPowerSeries.map φ f) := by
  ext α
  simp [MvPowerSeries.coeff_pderiv]

theorem om_map {d : ℕ} (G : FGLaw K d) :
    Om (GlobalTheory.FBMap.mapLaw φ G) = (Om G).map (MvPowerSeries.map φ) := by
  have hJ : JM (GlobalTheory.FBMap.mapLaw φ G) = (JM G).map (MvPowerSeries.map φ) := by
    ext1 i b
    simp only [JM, Jac, Matrix.map_apply, Matrix.of_apply]
    rw [GlobalTheory.FBMap.map_ev2 φ (GlobalTheory.FBMap.nc_pt _) GlobalTheory.FBMap.nc_zero, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_zero,
      map_pderiv]
    rfl
  refine Matrix.inv_eq_left_inv ?_
  rw [hJ, ← Matrix.map_mul, om_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem logOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (a : Fin d) :
    logOf (GlobalTheory.FBMap.mapLaw φ G) a = MvPowerSeries.map φ (logOf G a) := by
  rw [← sub_eq_zero, eq_C_of_pderiv_zero (g := logOf (GlobalTheory.FBMap.mapLaw φ G) a - MvPowerSeries.map φ (logOf G a))]
  · simp [logOf, constantCoeff_prim]
  · rintro ⟨j, b⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [map_sub, ← map_pderiv, pderiv_logOf, pderiv_logOf, om_map, Matrix.map_apply, sub_self]

theorem lg_logFGLOf_map [CharZero K] [CharZero C] {d : ℕ} (G : FGLaw K d) (hG) (hG') (a : Fin d) :
    (logFGLOf v (GlobalTheory.FBMap.mapLaw φ G) hG').lg a = MvPowerSeries.map φ ((logFGLOf w G hG).lg a) := by
  show subst (oneVar C d) (logOf (GlobalTheory.FBMap.mapLaw φ G) a) = MvPowerSeries.map φ (subst (oneVar K d) (logOf G a))
  rw [logOf_map, map_subst hs_oneVar]
  congr 1
  funext q
  simp [oneVar]

end Map

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth

theorem nuFacC_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X X' : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC Ch X f k = nuFacC Ch X' f k := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X X' f k
  letI := io.toAlgebra
  haveI : CharZero T.Fr := X.ιF.charZero
  let w : AddValuation T.Fr (WithTop ℝ) := (vX_vp X).comap X.ιF
  have hw : ∀ (Y : ValExt T p) x, vX_vp Y (Y.ιF x) = w x := by
    intro Y x
    show _ = vX_vp X (X.ιF x)
    by_cases hx : x = 0
    · rw [hx, Y.ιF.map_zero, X.ιF.map_zero, AddValuation.map_zero, AddValuation.map_zero]
    · rw [vX_vp_ιF Y hx, vX_vp_ιF X hx]
  have hG : ∀ a, MvIsInt w (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
    intro a α
    have h := (fgl Ch X).F_int a α
    have e : (fgl Ch X).F a = MvPowerSeries.map X.ιF (subst (twoVars T.Fr _) (Ch.ch.B.G.F a)) := by
      rw [map_subst hs_twoVars]
      show subst (twoVars X.C _) (MvPowerSeries.map X.ιF (Ch.ch.B.G.F a)) = _
      congr 1
      funext q
      simp [twoVars]
    rw [e, coeff_map] at h
    exact h
  have key : ∀ Y : ValExt T p, nuFacC Ch Y f k = detDepth (logFGLOf w Ch.ch.B.G hG)
      (fun (a : Fin (rk f)) e => algebraMap T.V T.Fr (Ch.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩ e)) k := by
    intro Y
    rw [nuFacC, detDepth, detDepth, ← detPow_map Y.ιF]
    exact depth_map Y.ιF (hw Y) _ _ (fun _ a => lg_logFGLOf_map Y.ιF _ hG _ a) _ _
  rw [key, key]

end GlobalTheory.DepthField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equiv_of_stalkwise_base_change : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  first
  | exact @GlobalTheory.EtC.LocGlobSp.main
  | exact GlobalTheory.EtC.LocGlobSp.main
  | (intros; apply GlobalTheory.EtC.LocGlobSp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAxisUnitGeneratorsPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_axis_unit_generators_pullback : ∀ (A₀ A₀' X X' : Scheme.{0}) (ψ : A₀ ⟶ A₀') (e : A₀ ⟶ X) (e' : A₀' ⟶ X') (π : X ⟶ X'), e ≫ π = ψ ≫ e' → ∀ (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ (ρ₁ : LB.Gen (Q₁.pull e')) (ρ₂ : LB.Gen (Q₂.pull e')), ρ₁.IsGen → ρ₂.IsGen → ∃ g : Γ(A₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₀) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), e (r z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ e) z _ (w.s k) * gm (r ≫ ψ) z _ (ρ₁.s k.2) = gm r z ⊤ g * gm (r ≫ ψ) z _ (ρ₂.s k.1) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.axis_unit  <;> assumption)
end

