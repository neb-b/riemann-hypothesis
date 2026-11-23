module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbXMul
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.Unram
open GlobalTheory.StepData

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}



open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_not_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : ¬ _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = _root_.GlobalTheory.RootEx.basePt c x₀ r s := by
  simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply, dif_neg hf, add_zero]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = e ⟨(r, s), hf⟩ := by
  simp only [_root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, Matrix.add_apply,
    Matrix.of_apply, dif_pos hf]
  have hf' := hf
  rcases r with i | l <;> rcases s with j | m <;> simp only [_root_.GlobalTheory.RootEx.Free] at hf' <;>
    simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    omega

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem intM_basePt_of_intM {x₀ : Matrix n n' k}
    (hx : _root_.GlobalTheory.StepData.IntM x₀) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.basePt c x₀) := by
  unfold _root_.GlobalTheory.RootEx.basePt
  refine _root_.GlobalTheory.StepData.intM_fromBlocks.mpr
    ⟨hx, _root_.GlobalTheory.StepData.intM_zero, _root_.GlobalTheory.StepData.intM_zero, fun l i => ?_⟩
  simp only [Matrix.of_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.Unram.intM_affPt {p : ℕ} (x₀ : Matrix n n' k) (e) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ↔
      _root_.GlobalTheory.StepData.IntM x₀ ∧ ∀ rs, e rs ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun rs => ?_⟩
    · have hij := h (Sum.inl i) (Sum.inl j)
      rwa [affPt_apply_of_not_free x₀ e (by simp [_root_.GlobalTheory.RootEx.Free]),
        _root_.GlobalTheory.RootEx.basePt, Matrix.fromBlocks_apply₁₁] at hij
    · obtain ⟨⟨r, s⟩, hf⟩ := rs
      have hrs := h r s
      rwa [affPt_apply_of_free x₀ e hf] at hrs
  · rintro ⟨hx, he⟩ r s
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · rw [affPt_apply_of_free x₀ e hf]
      exact he _
    · rw [affPt_apply_of_not_free x₀ e hf]
      exact intM_basePt_of_intM hx r s


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
theorem _root_.GlobalTheory.RootEx.Unram.psi_eq_one {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k} (hx : x ∈ 𝒪[k]) : ψ x = 1 := by
  have h1 := (hψ x).mpr (by
    rw [Units.val_one, map_one]
    exact (Valuation.mem_integer_iff _ _).mp hx)
  exact h1 x le_rfl

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
theorem _root_.GlobalTheory.RootEx.Unram.mem_of_psi {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k}
    (hx : ∀ t ∈ 𝒪[k], ψ (t * x) = 1) : x ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff]
  have hmain := (hψ x).mp ?_
  · simpa using hmain
  intro y hy
  by_cases hx0 : x = 0
  · subst hx0
    have hy0 : y = 0 := by simpa using hy
    simp [hy0]
  · have hv : valuation k (y / x) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have hyx := hx (y / x) ((Valuation.mem_integer_iff _ _).mpr hv)
    rwa [div_mul_cancel₀ y hx0] at hyx

variable [MeasurableSpace k] [BorelSpace k]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem ch_affPt_mem_of_integral {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) (he : ∀ rs, e rs ∈ 𝒪[k]) :
    _root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ∈ 𝒪[k] := by
  unfold _root_.GlobalTheory.RootEx.ch
  refine sum_mem fun i _ => ?_
  have hf : _root_.GlobalTheory.RootEx.Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by
    simp [_root_.GlobalTheory.RootEx.Free]
  rw [affPt_apply_of_free x₀ e hf]
  exact he _

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [MeasurableSpace k] [BorelSpace k] in
omit [DecidableEq n] [DecidableEq n'] in
open Classical in
theorem _root_.GlobalTheory.RootEx.Unram.opE_of_ite {p : ℕ} {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {ν : Measure k} (hν : _root_.GlobalTheory.SplitWeil.IsUnitVol ν)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (P : Prop)
    (h : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) = if P ∧ ∀ rs, e rs ∈ 𝒪[k] then 1 else 0) :
    _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ = if P then 1 else 0 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI := hν.1
  set S : Set ({ rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k) :=
    Set.univ.pi fun _ => (𝒪[k] : Set k) with hS
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => (_root_.GlobalTheory.SplitWeil.isOpen_int k).measurableSet
  have hint : ∀ e : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k,
      Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) *
          ((ψ (-_root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt p x₀ e)) : Circle) : ℂ) =
        if P then S.indicator (fun _ => (1 : ℂ)) e else 0 := by
    intro e
    rw [h e]
    by_cases hP : P
    · by_cases he : ∀ rs, e rs ∈ 𝒪[k]
      · have heS : e ∈ S := fun rs _ => he rs
        rw [if_pos ⟨hP, he⟩, if_pos hP, Set.indicator_of_mem heS,
          _root_.GlobalTheory.RootEx.Unram.psi_eq_one hψ
            (neg_mem (ch_affPt_mem_of_integral x₀ e he))]
        simp
      · have heS : e ∉ S := fun heS => he fun rs => heS rs (Set.mem_univ _)
        rw [if_neg (fun h' => he h'.2), if_pos hP, Set.indicator_of_notMem heS, zero_mul]
    · rw [if_neg (fun h' => hP h'.1), if_neg hP, zero_mul]
  unfold _root_.GlobalTheory.RootEx.opE
  simp_rw [hint]
  split_ifs with hP
  · rw [integral_indicator_const _ hSm, Measure.real_def, hS, Measure.pi_pi]
    simp [hν.2]
  · simp


open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [MeasurableSpace k] [BorelSpace k] in
omit [DecidableEq n] [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.Unram.psi_ch_eq_one {p : ℕ} (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure]
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (h : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ ≠ 0)
    (D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hD : ∀ r s, ¬ _root_.GlobalTheory.RootEx.Free p (r, s) → D r s = 0)
    (hΨ : ∀ x, Ψ (x + D) = Ψ x) : ψ (-_root_.GlobalTheory.RootEx.ch D) = 1 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  set d : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k :=
    fun rs => D rs.1.1 rs.1.2 with hd
  have haff : ∀ e, _root_.GlobalTheory.RootEx.affPt p x₀ (e + d) = _root_.GlobalTheory.RootEx.affPt p x₀ e + D := by
    intro e
    ext r s
    simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply]
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · simp only [dif_pos hf, Pi.add_apply, hd]
      ring
    · simp only [dif_neg hf, hD r s hf, add_zero]
  have hch : ∀ A B : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (A + B) =
        _root_.GlobalTheory.RootEx.ch A + _root_.GlobalTheory.RootEx.ch B := by
    intro A B
    simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib]
  have key : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ =
      ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ := by
    unfold _root_.GlobalTheory.RootEx.opE
    rw [← integral_const_mul, ← integral_add_right_eq_self _ d]
    congr 1
    ext e
    rw [haff, hΨ, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have h1 : ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) = 1 :=
    mul_right_cancel₀ h (key.symm.trans (one_mul _).symm)
  exact Circle.ext (h1.trans Circle.coe_one.symm)

end GlobalTheory.RootEx.Unram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRank
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInvariantForm
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.DualAverage

theorem isLocallyConstant_orbit {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W} (hσ : IsSmooth σ) (u : W) :
    IsLocallyConstant fun g : G => σ g u := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_
  have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' {x : G | σ x u = u}) := (hσ u).preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simp)] with x hx
  have hx' : σ (g⁻¹ * x) u = u := hx
  conv_rhs => rw [← hx']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_invariant_form (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) (l₀ : Module.Dual ℂ W) :
    ∃ l : Module.Dual ℂ W, (∀ h ∈ H, ∀ w, l (σ h w) = l w) ∧
      ∀ w, (∀ h ∈ H, σ h w = w) → l w = l₀ w := by
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH
  borelize ↥H
  let η : Measure H := Measure.haar
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  have hint : ∀ w, Integrable (fun h : H => l₀ (σ ((h : G)⁻¹) w)) η := by
    intro w
    have hc : Continuous fun h : H => l₀ (σ ((h : G)⁻¹) w) :=
      (((isLocallyConstant_orbit hσ w).comp_continuous
        (continuous_subtype_val.inv : Continuous fun h : H => (h : G)⁻¹)).comp l₀).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : Module.Dual ℂ W :=
    { toFun := fun w => ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η
      map_add' := fun v w => by
        simp only [map_add (f := _)]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have ha : ∀ w, a w = ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η := fun _ => rfl
  refine ⟨((η.real Set.univ : ℝ) : ℂ)⁻¹ • a, fun h₀ hh₀ w => ?_, fun w hw => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, ha, ha,
      ← integral_mul_left_eq_self (μ := η) (fun h : H => l₀ (σ ((h : G)⁻¹) (σ h₀ w))) ⟨h₀, hh₀⟩]
    congr 2
    funext h
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [LinearMap.smul_apply, ha]
    have : (fun h : H => l₀ (σ ((h : G)⁻¹) w)) = fun _ => l₀ w :=
      funext fun h => by rw [hw _ (inv_mem h.2)]
    rw [this, integral_const, Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.SmGL.DualAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsBorelSphRevInv
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix

namespace GlobalTheory.SatakeFlip

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

theorem revT_mul (A B : Matrix (Fin n) (Fin n) R) :
    Aᵀ.submatrix Fin.rev Fin.rev * Bᵀ.submatrix Fin.rev Fin.rev = (B * A)ᵀ.submatrix Fin.rev Fin.rev := by
  rw [transpose_mul]
  exact submatrix_mul_equiv Aᵀ Bᵀ Fin.rev Fin.revPerm Fin.rev

theorem revT_one : (1 : Matrix (Fin n) (Fin n) R)ᵀ.submatrix Fin.rev Fin.rev = 1 := by
  rw [transpose_one]
  exact submatrix_one_equiv Fin.revPerm

def invRevT : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨(g⁻¹).valᵀ.submatrix Fin.rev Fin.rev, g.valᵀ.submatrix Fin.rev Fin.rev,
    by rw [revT_mul, Units.mul_inv, revT_one], by rw [revT_mul, Units.inv_mul, revT_one]⟩
  map_one' := Units.ext (by simp only [inv_one, Units.val_one]; exact revT_one)
  map_mul' g h := Units.ext (by simp only [_root_.mul_inv_rev, Units.val_mul]; rw [revT_mul])

theorem invRevT_apply (g : GL (Fin n) R) (i j : Fin n) :
    (invRevT g).val i j = (g⁻¹).val j.rev i.rev := rfl

theorem invRevT_invRevT (g : GL (Fin n) R) : invRevT (invRevT g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invRevT_apply, ← map_inv, invRevT_apply, inv_inv, Fin.rev_rev, Fin.rev_rev]

theorem invRevT_mem_borel {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) :
    invRevT b ∈ GlobalTheory.SmGL.borel R (Fin n) :=
  (mem_borel R).2 fun _ _ h => (mem_borel R).1 (inv_mem hb) _ _ (Fin.rev_lt_rev.2 h)

theorem inv_diag_mul {b : GL (Fin n) R} (hb : b ∈ GlobalTheory.SmGL.borel R (Fin n)) (i : Fin n) :
    (b⁻¹).val i i * b.val i i = 1 := by
  have h := congrFun (congrFun (Units.inv_mul b) i) i
  change ((b⁻¹).val * b.val) i i = (1 : Matrix (Fin n) (Fin n) R) i i at h
  rw [Matrix.mul_apply, one_apply_eq, Finset.sum_eq_single i] at h
  · exact h
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h' | h'
    · rw [(mem_borel R).1 (inv_mem hb) _ _ h', zero_mul]
    · rw [(mem_borel R).1 hb _ _ h', mul_zero]
  · simp

end Ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem invRevT_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : invRevT g ∈ KO k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  refine (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => h2 _ _, fun i j => ?_⟩
  rw [← map_inv, invRevT_apply, inv_inv]
  exact h1 _ _

theorem ord_inv_eq_neg (x : kˣ) : ord k x⁻¹ = -ord k x := by
  have h := ord_mul k x⁻¹ x
  rw [inv_mul_cancel, ord_eq_zero (k := k) (x := 1) (by simp)] at h
  omega

def cosetMap : GL (Fin n) k ⧸ KO k (Fin n) → GL (Fin n) k ⧸ KO k (Fin n) :=
  Quotient.map' invRevT fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [← map_inv, ← map_mul]
    exact invRevT_mem_KO h

theorem cosetMap_mk (g : GL (Fin n) k) :
    cosetMap (g : GL (Fin n) k ⧸ KO k (Fin n)) = (invRevT g : GL (Fin n) k) := rfl

theorem cosetMap_cosetMap (c : GL (Fin n) k ⧸ KO k (Fin n)) : cosetMap (cosetMap c) = c := by
  induction c using QuotientGroup.induction_on with
  | H g => rw [cosetMap_mk, cosetMap_mk, invRevT_invRevT]

theorem cosetMap_smul (x : GL (Fin n) k) (c : GL (Fin n) k ⧸ KO k (Fin n)) :
    cosetMap (x • c) = invRevT x • cosetMap c := by
  induction c using QuotientGroup.induction_on with
  | H g =>
    rw [MulAction.Quotient.smul_mk, cosetMap_mk, cosetMap_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      smul_eq_mul, map_mul]

theorem exists_isBorelSph_rev_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ)
    (h : IsBorelSph k γ φ) (hS : HasBoundedSums k φ) :
    ∃ ψ : GL (Fin n) k → ℂ, IsBorelSph k (fun i => (γ (Fin.rev i))⁻¹) ψ ∧ HasBoundedSums k ψ := by
  classical
  refine ⟨fun g => φ (invRevT g), ⟨fun g x hx => ?_, fun b hb t ht => ?_⟩, fun S hK => ?_⟩
  · show φ (invRevT (g * x)) = φ (invRevT g)
    rw [map_mul, h.1 _ _ (invRevT_mem_KO hx)]
  · show φ (invRevT b) = _
    rw [h.2 _ (invRevT_mem_borel hb) (fun i => (t i.rev)⁻¹) fun i => ?_]
    · refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, ord_inv_eq_neg, _root_.zpow_neg, _root_.inv_zpow]
    · rw [invRevT_apply, Units.val_inv_eq_inv_val, ← ht]
      exact eq_inv_of_mul_eq_one_left (inv_diag_mul hb _)
  · have hinj : Function.Injective (cosetMap (k := k) (n := n)) :=
      Function.LeftInverse.injective cosetMap_cosetMap
    have h1 := hS (S.image cosetMap) fun x hx c hc => by
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
      refine Finset.mem_image.2 ⟨invRevT x • d, hK _ (invRevT_mem_KO hx) _ hd, ?_⟩
      rw [cosetMap_smul, invRevT_invRevT]
    rw [Finset.card_image_of_injective _ hinj, Finset.sum_image fun _ _ _ _ e => hinj e] at h1
    refine le_of_eq_of_le (congrArg _ (Finset.sum_congr rfl fun c _ => ?_)) h1
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (invRevT c.out)
    rw [← cosetMap_mk, QuotientGroup.out_eq'] at hx
    show φ (invRevT c.out) = _
    rw [hx, h.1 _ _ x.2]

end GlobalTheory.SatakeFlip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRepsOfFg
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_isReps_of_fg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (M : Submodule 𝒪[k] (ι → k)) (hM : M.FG) :
    ∃ T : Finset (ι → k), IsReps ϖ M T := by
  classical
  have h1 : Finite (𝒪[k] ⧸ Ideal.span {ϖ}) := by
    rw [← hϖ.maximalIdeal_eq]
    exact (inferInstance : Finite 𝓀[k])
  have hfin : Module.Finite 𝒪[k] M := Module.Finite.iff_fg.mpr hM
  set N : Submodule 𝒪[k] M := Ideal.span {ϖ} • ⊤ with hN
  have h2 : Finite (M ⧸ N) := by
    have : Finite (M ⧸ (⊤ : Submodule 𝒪[k] M)) := by
      have : Subsingleton (M ⧸ (⊤ : Submodule 𝒪[k] M)) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      infer_instance
    exact Submodule.finite_quotient_smul _ Module.Finite.fg_top
  have hmem : ∀ x : M, x ∈ N ↔ (x : ι → k) ∈ ϖ • M := by
    intro x
    rw [hN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
    · rintro ⟨b, hb, h⟩
      exact ⟨⟨b, hb⟩, trivial, Subtype.ext h⟩
  have := Fintype.ofFinite (M ⧸ N)
  choose s hs using Submodule.Quotient.mk_surjective N
  refine ⟨Finset.univ.image fun q => (s q : ι → k), ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (s q).2
  · intro v hv
    have key : ∀ q, v - (s q : ι → k) ∈ ϖ • M ↔ Submodule.Quotient.mk (⟨v, hv⟩ : M) = q := by
      intro q
      conv_rhs => rw [← hs q, Submodule.Quotient.eq, hmem]
      rfl
    refine ⟨s (Submodule.Quotient.mk ⟨v, hv⟩), ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp h]

end GlobalTheory.RootEx.UnfoldShape
end

