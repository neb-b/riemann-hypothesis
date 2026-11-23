module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.ExchangeSupport

section Algebra
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def rowM (c p : ℕ) (u : n → k) : Matrix (Fin c) n k :=
  Matrix.of fun l s => if l.val + 1 = p then u s else 0

def colM (c p : ℕ) (β : n → k) : Matrix n (Fin c) k :=
  Matrix.of fun r i => if i.val + 1 = p then β r else 0

theorem rowE_val (u : n → k) : (rowE c p u).val = fromBlocks 1 0 (rowM c p u) 1 := rfl
theorem colE_val (u : n → k) : (colE c p u).val = fromBlocks 1 (colM c p u) 0 1 := rfl
theorem rowE_inv_val (u : n → k) : ((rowE c p u)⁻¹).val = fromBlocks 1 0 (-rowM c p u) 1 := rfl
theorem colE_inv_val (u : n → k) : ((colE c p u)⁻¹).val = fromBlocks 1 (-colM c p u) 0 1 := rfl

omit [DecidableEq n] [Fintype n] in
theorem colM_mul_rowM (u β : n → k) : colM c (p + 1) β * rowM c p u = 0 := by
  ext r s
  simp only [colM, rowM, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h1 h2
  · omega
  all_goals simp

omit [DecidableEq n] in
theorem rowM_mul_colM (u β : n → k) (i j : Fin c) :
    (rowM c p u * colM c (p + 1) β) i j = if i.val + 1 = p ∧ j.val = p then u ⬝ᵥ β else 0 := by
  simp only [colM, rowM, Matrix.mul_apply, Matrix.of_apply, dotProduct]
  by_cases h1 : i.val + 1 = p <;> by_cases h2 : j.val = p <;> simp [h1, h2]

theorem rowE_add (u w : n → k) : rowE c p (u + w) = rowE c p u * rowE c p w := by
  apply Units.ext
  rw [Units.val_mul, rowE_val, rowE_val, rowE_val]
  have : rowM c p (u + w) = rowM c p u + rowM c p w := by
    ext i j; simp only [rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp
  simp [fromBlocks_multiply, this]

theorem colE_add (u w : n → k) : colE c p (u + w) = colE c p u * colE c p w := by
  apply Units.ext
  rw [Units.val_mul, colE_val, colE_val, colE_val]
  have : colM c p (u + w) = colM c p w + colM c p u := by
    ext i j; simp only [colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp [add_comm]
  simp [fromBlocks_multiply, this]

theorem rowE_zero : rowE c p (0 : n → k) = 1 := by
  have := rowE_add (c := c) (p := p) (0 : n → k) 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem colE_zero : colE c p (0 : n → k) = 1 := by
  have := colE_add (c := c) (p := p) (0 : n → k) 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem simpleSum_eq (hp : 1 ≤ p) (hc : p < c) (g : GL (n ⊕ Fin c) k) (t : k)
    (h : ∀ i j : Fin c, g.val (Sum.inr i) (Sum.inr j) =
      (1 : Matrix (Fin c) (Fin c) k) i j + if i.val + 1 = p ∧ j.val = p then t else 0) :
    simpleSum g = t := by
  unfold simpleSum
  rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin c), Finset.sum_eq_single (⟨p, hc⟩ : Fin c)]
  · have h1 : p - 1 + 1 = p := by omega
    have h2 : (⟨p - 1, by omega⟩ : Fin c) ≠ ⟨p, hc⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    simp [h, h1, Matrix.one_apply_ne h2]
  · intro j _ hj
    have : j.val ≠ p - 1 + 1 := fun e => hj (Fin.ext (by simp only; omega))
    simp [this]
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj
    · have h1 : i.val + 1 ≠ p := fun e => hi (Fin.ext (by simp only; omega))
      have h2 : i ≠ j := fun e => by subst e; omega
      simp [h, h1, Matrix.one_apply_ne h2]
    · rfl
  · simp

theorem conj_col (hp : 1 ≤ p) (hc : p < c) (u β : n → k) :
    rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹ ∈ N k n c p ∧
      simpleSum (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹) = u ⬝ᵥ β := by
  have hv : (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹).val =
      fromBlocks 1 (colM c (p + 1) β) 0 (1 + rowM c p u * colM c (p + 1) β) := by
    rw [Units.val_mul, Units.val_mul, rowE_val, colE_val, rowE_inv_val]
    simp [fromBlocks_multiply, Matrix.add_mul, Matrix.mul_assoc, colM_mul_rowM, add_comm]
  refine ⟨Subgroup.subset_closure ?_, simpleSum_eq hp hc _ _ ?_⟩
  · intro r s hrs
    rw [hv, ← fromBlocks_one]
    rcases r with r | r <;> rcases s with s | s
    · rfl
    · have : s.val ≠ p := by simp [lev] at hrs; omega
      simp [colM, this]
    · rfl
    · have : ¬ (r.val + 1 = p ∧ s.val = p) := by simp [lev] at hrs; omega
      simp [rowM_mul_colM, this]
  · intro i j
    rw [hv]; simp [rowM_mul_colM]

theorem conj_row (hp : 1 ≤ p) (hc : p < c) (u β : n → k) :
    colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹ ∈ N k n c (p + 1) ∧
      simpleSum (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹) = -(u ⬝ᵥ β) := by
  have hv : (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 0 (rowM c p u) (1 - rowM c p u * colM c (p + 1) β) := by
    rw [Units.val_mul, Units.val_mul, rowE_val, colE_val, colE_inv_val]
    simp [fromBlocks_multiply, colM_mul_rowM, sub_eq_add_neg, add_comm]
  refine ⟨Subgroup.subset_closure ?_, simpleSum_eq hp hc _ _ ?_⟩
  · intro r s hrs
    rw [hv, ← fromBlocks_one]
    rcases r with r | r <;> rcases s with s | s
    · rfl
    · rfl
    · have : r.val + 1 ≠ p := by simp [lev] at hrs; omega
      simp [rowM, this]
    · have : ¬ (r.val + 1 = p ∧ s.val = p) := by simp [lev] at hrs; omega
      simp [rowM_mul_colM, this]
  · intro i j
    rw [hv]; simp only [fromBlocks_apply₂₂, Matrix.sub_apply, rowM_mul_colM]
    split_ifs <;> simp [sub_eq_add_neg]

end Algebra

section Top
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

omit [Fintype n] [DecidableEq n] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_rowM : Continuous fun u : n → k => rowM c p u := by
  refine continuous_matrix fun i j => ?_
  simp only [rowM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

omit [Fintype n] [DecidableEq n] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_colM : Continuous fun u : n → k => colM c p u := by
  refine continuous_matrix fun i j => ?_
  simp only [colM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

theorem continuous_rowE : Continuous fun u : n → k => rowE c p u := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_rowM continuous_const
  · exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_rowM.neg continuous_const

theorem continuous_colE : Continuous fun u : n → k => colE c p u := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_fromBlocks continuous_const continuous_colM continuous_const continuous_const
  · exact Continuous.matrix_fromBlocks continuous_const continuous_colM.neg continuous_const continuous_const

theorem mem_SB_of {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (f : (n → k) → ℂ)
    (h1 : ∀ᶠ w in 𝓝 (0 : n → k), ∀ u, f (u + w) = f u)
    (h2 : ∀ᶠ β in 𝓝 (0 : n → k), ∀ u, f u = (ψ (u ⬝ᵥ β) : ℂ) * f u) : f ∈ SB (n → k) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have ht : Tendsto (fun y : n → k => y - x) (𝓝 x) (𝓝 0) := by
      have : Continuous fun y : n → k => y - x := by fun_prop
      simpa using this.tendsto x
    filter_upwards [ht.eventually h1] with y hy
    simpa using hy x
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ x₀ ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ (by ext x; simp [h])
    have h3 : ∀ᶠ y in 𝓝 (0 : k), ∀ i : n, ∀ u, f u = (ψ (u ⬝ᵥ Pi.single i y) : ℂ) * f u := by
      rw [eventually_all]
      intro i
      have : Continuous fun y : k => (Pi.single i y : n → k) := continuous_single (A := fun _ : n => k) i
      have ht := this.tendsto 0
      rw [Pi.single_zero] at ht
      exact ht.eventually h2
    obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp h3
    refine HasCompactSupport.intro
      (isCompact_univ_pi fun _ : n =>
        IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k x₀ / γ)) ?_
    intro u hu
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall, Set.mem_ofPred_eq, not_le] at hu
    obtain ⟨i, hi⟩ := hu
    have hu0 : u i ≠ 0 := by
      intro e; rw [e] at hi; simp at hi
    have hv0 : 0 < valuation k (u i) := lt_of_le_of_lt zero_le hi
    have hγ0 : 0 < γ := zero_lt_iff.2 hγ
    have hy : valuation k (x₀ / u i) < γ := by
      rw [map_div₀, div_lt_iff₀ hv0]
      rw [div_lt_iff₀ hγ0] at hi
      rwa [mul_comm]
    have := hs hy i u
    rw [dotProduct_single, mul_div_cancel₀ _ hu0] at this
    by_contra hf
    apply hx₀
    have h4 : (ψ x₀ : ℂ) = 1 := by
      have h5 : (ψ x₀ : ℂ) * f u = 1 * f u := by rw [one_mul]; exact this.symm
      exact mul_right_cancel₀ hf h5
    exact Circle.ext (by simpa using h4)

end Top

theorem exchange_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → (fun u : n → k => l (σ (rowE c p u) v)) ∈ SB (n → k) ∧ (∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) = (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v)) ∧ ∀ β : n → k, exUp ν p σ l (σ (colE c (p + 1) β) v) = ∫ u : n → k, (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)) ∧ (IsNEquiv ψ (p + 1) σ l → (fun β : n → k => l (σ (colE c (p + 1) β) v)) ∈ SB (n → k) ∧ ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) = (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v)) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hc ψ _ hψ ν _ A _ _ σ hσ l v
  have hrow : ∀ᶠ w in 𝓝 (0 : n → k), σ (rowE c p w) v = v :=
    continuous_rowE.continuousAt.eventually_mem ((hσ v).mem_nhds (by simp [rowE_zero]))
  have hcol : ∀ᶠ w in 𝓝 (0 : n → k), σ (colE c (p + 1) w) v = v :=
    continuous_colE.continuousAt.eventually_mem ((hσ v).mem_nhds (by simp [colE_zero]))
  have hmul : ∀ (a b : GL (n ⊕ Fin c) k), σ a (σ b v) = σ (a * b * a⁻¹) (σ a v) := by
    intro a b
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · have key : ∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) =
        (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) := by
      intro u β
      rw [hmul, hl _ (conj_col hp hc u β).1, (conj_col hp hc u β).2]
    refine ⟨mem_SB_of hψ _ ?_ ?_, key, fun β => ?_⟩
    · filter_upwards [hrow] with w hw u
      rw [rowE_add, map_mul, Module.End.mul_apply, hw]
    · filter_upwards [hcol] with w hw u
      rw [← key, hw]
    · simp only [exUp, key]
  · have key : ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) =
        (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v) := by
      intro u β
      rw [hmul, hl _ (conj_row hp hc u β).1, (conj_row hp hc u β).2]
    refine ⟨mem_SB_of hψ _ ?_ ?_, key⟩
    · filter_upwards [hcol] with w hw u
      rw [colE_add, map_mul, Module.End.mul_apply, hw]
    · have hneg : Tendsto (fun w : n → k => -w) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg (G := n → k)).tendsto 0
      filter_upwards [hneg.eventually hrow] with w hw u
      have := key (-w) u
      rwa [hw, neg_dotProduct, neg_neg, dotProduct_comm] at this

end GlobalTheory.RootEx.ExchangeSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
section
open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory

theorem supLattice_localisation_of_unitBall (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK)
    (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s : 𝓞 Ks, s ∉ la.asIdeal ∧ s • (f : WL) ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | (apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryCharacterKillsUnitaryTransvections
section
open scoped Matrix

namespace GlobalTheory.UTrans.TvKill

open GlobalTheory.UTrans GlobalTheory.UTrans.Calc

variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

def rk (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun a b => x a * ∑ e, G b e * σ (y e)

theorem rk_mulVec (x y v : Fin n → E) : rk σ G x y *ᵥ v = hf σ G v y • x := by
  funext a
  simp only [rk, Matrix.mulVec, dotProduct, Matrix.of_apply, hf, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem exists_dual (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0) : ∃ y, hf σ G x y = 1 := by
  have h1 : Matrix.vecMul x G ≠ 0 := fun h => hx (Matrix.eq_zero_of_vecMul_eq_zero hG.det_ne h)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp h1
  refine ⟨Pi.single b (σ (Matrix.vecMul x G b)⁻¹), ?_⟩
  have : hf σ G x (Pi.single b (σ (Matrix.vecMul x G b)⁻¹)) =
      Matrix.vecMul x G b * (Matrix.vecMul x G b)⁻¹ := by
    simp only [hf, Pi.single_apply, apply_ite σ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hG.invol, ← Finset.sum_mul]
    rfl
  rw [this, mul_inv_cancel₀ hb]

theorem exists_dual_iso [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ y, hf σ G x y = 1 ∧ hf σ G y y = 0 := by
  obtain ⟨y, hy⟩ := exists_dual hG hx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(hf σ G y y / 2)) = -(hf σ G y y / 2) := by
    rw [map_neg, map_div₀, hf_conj σ G hG.invol hG.herm, map_ofNat]
  refine ⟨y + (-(hf σ G y y / 2)) • x, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hxx, hy]; ring
  · simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx]
    ring

theorem exists_double [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ γ, IsU σ G γ ∧ γ *ᵥ x = (2 : E) • x := by
  obtain ⟨y, hy, hyy⟩ := exists_dual_iso hG hx hxx
  have hyx : hf σ G y x = 1 := by rw [← hf_conj σ G hG.invol hG.herm, hy, map_one]
  have hc : σ (-(1 / 2)) = -(1 / 2) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  have hm : ∀ v, (1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x) *ᵥ v =
      v + hf σ G v y • x + (-(1 / 2) : E) • hf σ G v x • y := by
    intro v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, rk_mulVec,
      rk_mulVec]
  refine ⟨1 + rk σ G x y + (-(1 / 2) : E) • rk σ G y x, ?_, ?_⟩
  · intro v w
    rw [hm, hm]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxx, hy, hyx, hyy,
      hf_conj σ G hG.invol hG.herm]
    ring
  · rw [hm, hy, hxx, zero_smul, smul_zero, add_zero, one_smul, two_smul]

theorem char_tvGen : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → ∀ (A : Type) [CommGroup A] (X : Matrix (Fin n) (Fin n) E → A), (∀ a b, GlobalTheory.UTrans.IsU σ G a → GlobalTheory.UTrans.IsU σ G b → X (a * b) = X a * X b) → ∀ m ∈ GlobalTheory.UTrans.TvGen σ G, X m = 1 := by
  intro E _ _ n σ G hG A _ X hX
  have hU1 : IsU σ G 1 := fun x y => by simp
  have hX1 : X 1 = 1 := by
    have := hX 1 1 hU1 hU1
    rw [mul_one] at this
    exact mul_eq_left.mp this.symm
  have key : ∀ m ∈ TvGen σ G, IsU σ G m ∧ X m = 1 := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem m hm =>
      obtain ⟨x, t, hx, ht, rfl⟩ := hm
      have hUq : ∀ q : ℚ, IsU σ G (tv σ G x (q * t)) := by
        intro q
        refine isU_tv σ G hG.invol hG.herm x _ ?_
        rw [hx, map_mul, map_ratCast]
        linear_combination (q : E) * ht
      have hUt : IsU σ G (tv σ G x t) := by simpa using hUq 1
      refine ⟨hUt, ?_⟩
      by_cases hx0 : x = 0
      · subst hx0
        have : tv σ G 0 t = 1 := by
          ext a b
          simp [tv]
        rw [this, hX1]
      · obtain ⟨γ, hγ, hγx⟩ := exists_double hG hx0 hx
        have h3 : IsU σ G (tv σ G x (1 / 3 * t)) := by
          have := hUq (1 / 3)
          push_cast at this
          exact this
        have hc := conj_tv σ G γ x (1 / 3 * t) hγ
        have he : tv σ G (γ *ᵥ x) (1 / 3 * t) = tv σ G x (1 / 3 * t) * tv σ G x t := by
          rw [hγx, tv_smul, tv_mul, hx, map_ofNat]
          congr 1
          ring
        rw [he] at hc
        have h4 := congrArg X hc
        rw [hX _ _ hγ h3, hX _ _ (isU_mul σ G _ _ h3 hUt) hγ, hX _ _ h3 hUt, mul_comm (X γ)] at h4
        exact mul_eq_left.mp (mul_right_cancel h4).symm
    | one => exact ⟨hU1, hX1⟩
    | mul a b _ _ ha hb =>
      exact ⟨isU_mul σ G _ _ ha.1 hb.1, by rw [hX _ _ ha.1 hb.1, ha.2, hb.2, mul_one]⟩
  exact fun m hm => (key m hm).2

end GlobalTheory.UTrans.TvKill
end

