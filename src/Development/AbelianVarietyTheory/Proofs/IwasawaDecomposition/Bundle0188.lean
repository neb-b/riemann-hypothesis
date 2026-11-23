module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.DataRRMetric
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
public import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquare
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColStableDisjoint
section
noncomputable section

open MvPolynomial GlobalTheory.MvPoly GlobalTheory.Harm Matrix

namespace GlobalTheory.DefLift

namespace Compl

theorem exists_sub_perp {E : Type*} [AddCommGroup E] [Module ℂ E] (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ)
    (hB : ∀ x, B x x = 0 → x = 0) (W : Submodule ℂ E) [FiniteDimensional ℂ W] (P : E) :
    ∃ Q ∈ W, ∀ w ∈ W, B (P - Q) w = 0 := by
  let b := Module.finBasis ℂ W
  let L : E →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearMap.pi fun i => B.flip (b i)
  have hL (P) (h : L P = 0) (w) (hw : w ∈ W) : B P w = 0 := by
    have := congrArg W.subtype (b.sum_repr ⟨w, hw⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.subtype_apply] at this
    change _ = w at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, map_smulₛₗ]
    exact smul_eq_zero_of_right _ (congrFun h i)
  have hinj : Function.Injective (L ∘ₗ W.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hB _ (hL x hx x x.2))
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
    (L P)
  exact ⟨x, x.2, hL _ (by rw [map_sub, ← hx]; simp)⟩

theorem totalDegree_aeval_le {σ : Type*} (f : σ → MvPolynomial σ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeBound.main
  | exact _root_.GlobalTheory.AevalTotalDegreeBound.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeBound.main ..)

variable {ι : Type} {m n : ℕ}

theorem totalDegree_subst_le (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ) (P : Pol ι m n) :
    (subst a b P).totalDegree ≤ P.totalDegree := by
  refine totalDegree_aeval_le _ (fun v => ?_) P
  refine totalDegree_finsetSum_le fun i _ => totalDegree_finsetSum_le fun c _ => ?_
  exact (totalDegree_smul_le _ _).trans (totalDegree_X _).le

theorem totalDegree_colSub_le (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P : Pol ι m n) :
    (colSub m τ g P).totalDegree ≤ P.totalDegree := by
  unfold colSub
  rw [AlgHom.toLinearMap_apply]
  exact totalDegree_subst_le _ _ _

theorem fockInner_subst [Fintype ι] (a : ι → Matrix (Fin n) (Fin n) ℂ) (b : ι → Matrix (Fin m) (Fin m) ℂ)
    (P Q : Pol ι m n) :
    fockInner (subst a b P) Q = fockInner P (subst (fun τ => star (a τ)) (fun τ => star (b τ)) Q) := by
  classical
  refine fockInner_algHom_of_linear _ _
    (fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0) ?_ ?_ P Q
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type]
  · rintro ⟨t, i, k⟩
    simp [subst, Fintype.sum_prod_type, apply_ite star, mul_comm]

theorem fockInner_colSub [Fintype ι] (τ : ι) (g : Matrix.unitaryGroup (Fin n) ℂ) (P Q : Pol ι m n) :
    fockInner (colSub m τ g P) Q = fockInner P (colSub m τ g⁻¹ Q) := by
  unfold colSub
  simp only [AlgHom.toLinearMap_apply]
  rw [fockInner_subst]
  congr 3
  · funext ρ
    split_ifs
    · rfl
    · simp
  · funext ρ
    simp

end Compl


open Compl in
theorem exists_colStable_disjoint (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U W : Submodule ℂ (X →ₗ[ℂ] Pol ι m n))
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) (hW : ∀ Φ ∈ W, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ W) (hlt : U < W) :
    ∃ U' : Submodule ℂ (X →ₗ[ℂ] Pol ι m n), U' ≠ ⊥ ∧ U' ≤ W ∧ U ⊓ U' = ⊥ ∧
      ∀ Φ ∈ U', ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U' := by
  classical
  let b := Module.finBasis ℂ X
  let B : (X →ₗ[ℂ] Pol ι m n) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ Ψ => ∑ i, fockInner (Φ (b i)) (Ψ (b i)))
      (fun _ _ _ => by simp [fockInner_add_left, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_left, Finset.mul_sum])
      (fun _ _ _ => by simp [fockInner_add_right, Finset.sum_add_distrib])
      (fun _ _ _ => by simp [fockInner_smul_right, Finset.mul_sum])
  have hBa (Φ Ψ) : B Φ Ψ = ∑ i, fockInner (Φ (b i)) (Ψ (b i)) := rfl
  have hB (Φ) (h : B Φ Φ = 0) : Φ = 0 := by
    rw [hBa] at h
    simp only [fockInner_self] at h
    have h' : ∑ i, fockNormSq (Φ (b i)) = 0 := by
      rw [← RCLike.ofReal_sum] at h
      exact RCLike.ofReal_eq_zero.mp h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => fockNormSq_nonneg _] at h'
    exact b.ext fun i => fockNormSq_eq_zero.mp (h' i (Finset.mem_univ i))
  have hadj (Φ Ψ τ g) : B (colSub m τ g ∘ₗ Φ) Ψ = B Φ (colSub m τ g⁻¹ ∘ₗ Ψ) := by
    simp only [hBa, LinearMap.comp_apply, fockInner_colSub]
  clear hBa
  clear_value B
  obtain ⟨β, hβW, hβU⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ∀ i, (β (b i)).totalDegree ≤ d :=
    ⟨_, fun i => Finset.le_sup (f := fun i => (β (b i)).totalDegree) (Finset.mem_univ i)⟩
  obtain ⟨R, hRf, hR⟩ : ∃ R : Submodule ℂ (Pol ι m n), FiniteDimensional ℂ R ∧ ∀ P, P ∈ R ↔ P.totalDegree ≤ d :=
    ⟨restrictTotalDegree (ι × Fin m × Fin n) ℂ d, inferInstance, fun P => mem_restrictTotalDegree _ _ _⟩
  let ψ : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n) :=
    { toFun := fun Ψ => R.subtype ∘ₗ Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let D : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range ψ
  have hD (Φ) : Φ ∈ D ↔ ∀ x, Φ x ∈ R := by
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  haveI : FiniteDimensional ℂ D := inferInstance
  clear_value D
  have hDs (Φ) (h : Φ ∈ D) (τ g) : colSub m τ g ∘ₗ Φ ∈ D := by
    rw [hD] at h ⊢
    intro x
    have := h x
    rw [hR] at this ⊢
    rw [LinearMap.comp_apply]
    exact (totalDegree_colSub_le τ g _).trans this
  have hβD : β ∈ D := by
    rw [hD]
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine R.sum_mem fun i _ => ?_
    rw [map_smul]
    exact R.smul_mem _ ((hR _).2 (hd i))
  haveI : FiniteDimensional ℂ (U ⊓ D : Submodule ℂ _) := Submodule.finiteDimensional_inf_right _ _
  let T : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := ⨅ w ∈ U ⊓ D, LinearMap.ker (B.flip w)
  have hT (Φ) : Φ ∈ T ↔ ∀ w ∈ U ⊓ D, B Φ w = 0 := by simp [T, Submodule.mem_iInf]
  obtain ⟨Q, hQ, hperp⟩ := exists_sub_perp B hB (U ⊓ D) β
  refine ⟨W ⊓ D ⊓ T, ?_, inf_le_left.trans inf_le_left, ?_, ?_⟩
  · intro h
    have hm : β - Q ∈ W ⊓ D ⊓ T :=
      ⟨⟨W.sub_mem hβW (hlt.le hQ.1), D.sub_mem hβD hQ.2⟩, (hT _).2 hperp⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at hm
    exact hβU (hm ▸ hQ.1)
  · rw [Submodule.eq_bot_iff]
    rintro Φ ⟨h1, ⟨-, h2⟩, h3⟩
    exact hB Φ ((hT Φ).1 h3 Φ ⟨h1, h2⟩)
  · rintro Φ ⟨⟨h1, h2⟩, h3⟩ τ g
    refine ⟨⟨hW Φ h1 τ g, hDs Φ h2 τ g⟩, (hT _).2 fun w hw => ?_⟩
    rw [hadj]
    exact (hT Φ).1 h3 _ ⟨hU w hw.1 τ _, hDs w hw.2 τ _⟩

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_eq_const_mul_prod_inner_of_positionwise (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (B : (∀ i, Hs i) → (∀ i, Hs i) → ℂ)
    (h : ∀ i v v', ∃ c : ℂ, ∀ w w' : Hs i,
      B (Function.update v i w) (Function.update v' i w') = c * ⟪w, w'⟫_ℂ) :
    ∃ c : ℂ, ∀ v v', B v v' = c * ∏ i, ⟪v i, v' i⟫_ℂ := by
  by_cases h0 : ∃ i, ∀ w : Hs i, w = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun v v' => ?_⟩
    obtain ⟨c, hc⟩ := h i v v'
    have h1 := hc (v i) (v' i)
    rw [Function.update_eq_self, Function.update_eq_self, hi (v i)] at h1
    simpa using h1
  · have h1 : ∀ i, ∃ e : Hs i, ⟪e, e⟫_ℂ = 1 := by
      intro i
      have : ∃ w : Hs i, w ≠ 0 := by
        by_contra hn
        exact h0 ⟨i, fun w => by_contra fun hw => hn ⟨w, hw⟩⟩
      obtain ⟨w, hw⟩ := this
      refine ⟨((‖w‖ : ℂ))⁻¹ • w, ?_⟩
      have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
      rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp only [map_inv₀, Complex.conj_ofReal]
      change ((‖w‖ : ℂ))⁻¹ * (((‖w‖ : ℂ))⁻¹ * (‖w‖ : ℂ) ^ 2) = 1
      field_simp
    choose e he using h1
    have step : ∀ i v v', B v v' =
        B (Function.update v i (e i)) (Function.update v' i (e i)) * ⟪v i, v' i⟫_ℂ := by
      intro i v v'
      obtain ⟨c, hc⟩ := h i v v'
      have h2 := hc (v i) (v' i)
      rw [Function.update_eq_self, Function.update_eq_self] at h2
      rw [h2, hc, he, mul_one]
    have key : ∀ (s : Finset ι) v v', B v v' =
        B (s.piecewise e v) (s.piecewise e v') * ∏ i ∈ s, ⟪v i, v' i⟫_ℂ := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro v v'; simp
      | insert a s ha ih =>
        intro v v'
        rw [ih v v', step a (s.piecewise e v) (s.piecewise e v'), Finset.prod_insert ha,
          Finset.piecewise_insert, Finset.piecewise_insert,
          Finset.piecewise_eq_of_notMem _ _ _ ha, Finset.piecewise_eq_of_notMem _ _ _ ha,
          mul_assoc]
    refine ⟨B e e, fun v v' => ?_⟩
    have := key Finset.univ v v'
    rwa [Finset.piecewise_univ, Finset.piecewise_univ] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
section
noncomputable section

open Module NumberField IsDedekindDomain Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions
open scoped Matrix InnerProductSpace ComplexOrder

namespace GlobalTheory.Mem.RowSides

section Semi

variable {K : Type} [Field K] {σ : K →+* ℂ} {U V W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]

theorem semi_injective_of_basis {ι : Type} [Fintype ι] (b : Basis ι K U) (g : U →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun i => g (b i)) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h (fun i => σ (b.repr x i)) hx
  refine b.repr.injective (Finsupp.ext fun i => σ.injective ?_)
  simpa using this i

end Semi

section Polar

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem majAt_expand {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + a • y) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 + Formalism.HermitianLatticesTheory.normAt b X v (a • y) ^ 2 +
      2 * (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  have hs : Formalism.HermitianLatticesTheory.fcoord b X v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v y := by
    have : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    rw [Formalism.HermitianLatticesTheory.fcoord, this, Matrix.mulVec_smul]; rfl
  simp only [normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, hs, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Complex.star_def, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_eq_of_normAt [_root_.NumberField.IsTotallyComplex K] {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (e : V →ₗ[K] W)
    (h : ∀ x, Formalism.HermitianLatticesTheory.normAt b' X' v (e x) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have key : ∀ a : K, (v.embedding a * Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y)).re =
      (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := fun a => by
    have h1 := majAt_expand b X v a x y
    have h2 := majAt_expand b' X' v a (e x) (e y)
    rw [← map_smul, ← map_add (f := _), h, h, h] at h2
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hn
    push Not at hn
    have hc := IsTotallyComplex.isComplex v
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (hn x)
  have h1 := key 1
  have h2 := key a
  simp only [map_one, one_mul] at h1
  simp only [Complex.mul_re, h1] at h2
  refine Complex.ext h1 (mul_left_cancel₀ ha ?_)
  linarith

end Polar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

variable {B ℓ} {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)




end Block

end GlobalTheory.Mem.RowSides

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_finiteDimensional_kStable_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → (∃ Λ S, IsKTypeOf ε σ Λ S) → ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ W ≤ smSub G (trRep σ P) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W := by
  rintro n ε H _ _ _ σ P G hP h hU ⟨Λ, S, hS⟩
  obtain ⟨w, hwS, hw, -⟩ := hS.2.2.2.1
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := (1 : Formalism.REAL.UJ ε).2
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hU.2.2 w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [hU.1.1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hUn, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, hinv⟩ := GlobalTheory.LowTypeRestriction.exists_bump hUn
  have hT : IsTest φ := ⟨hφ, hφc⟩
  have hne := GlobalTheory.LowTypeRestriction.garding_ne_zero hU hT.continuous hφc hφ0 hφ1 hw
    fun g hg h0 => hUs ⟨hφU g h0, hg⟩
  have hK := GlobalTheory.LowTypeRestriction.isKTypeOf_map hS (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc)
    (fun k hk w => GlobalTheory.LowTypeRestriction.garding_comm hU hT.continuous hφc hinv hk w) hwS hne
  refine ⟨S.map (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc), hK.1,
    (Submodule.ne_bot_iff _).2 ⟨_, ⟨w, hwS, rfl⟩, hne⟩, ?_, fun k hk v hv => hK.2.1 k hk v hv⟩
  rintro _ ⟨v, -, rfl⟩
  exact gard_mem hP h hU hT v

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsoPolarisedOfCompatibleThickeningsSquareStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_polarised_of_compatible_thickenings_square : SecBaseChangeSt → AmpleSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (P P' : PolAV (Spec (CommRingCat.of R))) (β : ∀ e : ℕ, thickObj R I e P'.A ≅ thickObj R I e P.A)
    (v : ∀ e : ℕ, LB.Iso ((LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2)).pull (fstG I e P'.A).left)
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull ((β e).hom.left ≫ (fstG I e P.A).left))),
    (∀ e, (v e).IsGen) →
    (∀ e, thickMap R I e P'.A ≫ (β (e + 1)).hom.left = (β e).hom.left ≫ thickMap R I e P.A) →
    (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
      (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
      gw (v (e + 1)) (r ≫ thickMap R I e P'.A) z (fun _ => j) (fun _ => fun _ => j') =
        gw (v e) r z (fun _ => j) (fun _ => fun _ => j')) →
    ∃ (Φ : P'.A ≅ P.A) (w : LB.Iso (LB.LinComb P'.L (K := Fin 1) (fun _ => 𝟙 P'.A.left) (fun _ => 2))
      ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen ∧
    ∀ e : ℕ, (fstG I e P'.A).left ≫ Φ.hom.left = (β e).hom.left ≫ (fstG I e P.A).left ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P'.A).left) (z : Z) (j : P.L.ι) (j' : P'.L.ι),
        (fstG I e P.A).left ((β e).hom.left (r z)) ∈ P.L.U j → (fstG I e P'.A).left (r z) ∈ P'.L.U j' →
        gw w (r ≫ (fstG I e P'.A).left) z (fun _ => j) (fun _ => j') = gw (v e) r z (fun _ => j) (fun _ => fun _ => j') := by
  first | exact @GlobalTheory.exists_iso_of_compatible_thickenings_sq | exact GlobalTheory.exists_iso_of_compatible_thickenings_sq | (intros; apply GlobalTheory.exists_iso_of_compatible_thickenings_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem AllPlus.finite_smooth_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), AllPlus M → ∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro D V S M h τ
  obtain ⟨h1, h2, -, -, -, h3, -⟩ := GlobalTheory.CompactModel.model_allPos D V S M τ (funext fun a => h τ a)
  exact ⟨h1, h2, fun U hU => h3 U le_top fun g hg => hU ⟨g, hg.1⟩⟩

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjointStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialAction_one_mul_adjoint : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), fact (n := n) ε x₁ x₂ x₃ 1 1 = 1 ∧ (∀ (k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u u' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, k' τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → (∀ τ, IsUnit (u' τ)) → fact ε x₁ x₂ x₃ (k * k') (u * u') = fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ k' u') ∧ ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → ∀ F F' : PolF D m n, fockL (fact ε x₁ x₂ x₃ k u F) F' = fockL F (fact ε x₁ x₂ x₃ (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) F') := by
  first | exact @GlobalTheory.JointHarm.fact_one_mul_adj | exact GlobalTheory.JointHarm.fact_one_mul_adj | (intros; apply GlobalTheory.JointHarm.fact_one_mul_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_gaussianVectors_fockSpace : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  first | exact @GlobalTheory.GaussInner.inner_gauss_gauss | exact GlobalTheory.GaussInner.inner_gauss_gauss | (intros; apply GlobalTheory.GaussInner.inner_gauss_gauss <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeightStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (π' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P') (x y : P) (x' y' : P'), IsHolRep ε B π → IsHolRep ε B' π' → IsBottom ε π μ x → IsBottom ε π μ y → IsBottom ε π' μ x' → IsBottom ε π' μ y' → ∀ k ∈ Formalism.REAL.Kset ε, B x (π k y) * B' x' y' = B x y * B' x' (π' k y') := by
  first | exact @GlobalTheory.JointHarm.Sph.coeff_eq | exact GlobalTheory.JointHarm.Sph.coeff_eq | (intros; apply GlobalTheory.JointHarm.Sph.coeff_eq <;> assumption)
end

