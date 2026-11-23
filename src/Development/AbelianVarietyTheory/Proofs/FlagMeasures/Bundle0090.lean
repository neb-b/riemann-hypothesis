module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassOrbitClass
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassOrbit

theorem mass_orbit_class {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d₁ : S.Datum) (Λ₁ : Submodule L.O S.V)
    (h₁ : S.IsTerm d₁ Λ₁) (d : S.Datum) :
    (S.mass d fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • S.Fr d₁ Λ₁) =
      ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ := by
  have act := @GlobalTheory.FrameAct.stabiliser_acts_on_terms F _ _ _ _ _ E _ _ _ L r k S
  have trm := @GlobalTheory.HL.TermBasic.term_basic F _ _ _ _ _ E _ _ _ L r k S
  have vol := (@GlobalTheory.HL.volSt F _ _ _ _ _ E _ _ _ L r k S).2
  have hT : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.IsTerm d (h • Λ) := fun d Λ H h hh => (act d Λ H h hh).1
  have hF : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, S.Fr d (h • Λ) = h • S.Fr d Λ :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.1
  have hB : ∀ d Λ, S.IsTerm d Λ → ∀ h ∈ S.St, (S.BBzero d (h • Λ) ↔ S.BBzero d Λ) :=
    fun d Λ H h hh => (act d Λ H h hh).2.2.2.2.2.2.2.1
  have hI : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ H => (trm d Λ H).2.2.2.2.2.2.1
  rw [GlobalTheory.HL.mass_eq_sumCls L r k S d _ (by
    rintro h hh Λ H ⟨hb, s, hs, e⟩
    refine ⟨(hB d Λ H h hh).2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
    rw [hF d Λ H h hh, e, mul_smul])]
  set C₁ := S.Fr d₁ Λ₁ with hC
  unfold Frames.sumCls
  rw [tsum_eq_single (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁)]
  · have hrel : (MulAction.orbitRel S.St (Set S.FrP))
        (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out C₁ := Quotient.mk_out C₁
    obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrel
    have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out = h • C₁ := e.symm
    have hint : S.IsIntCls (h • C₁) := by
      rw [hC, ← hF d₁ Λ₁ h₁ h hh]
      exact hI _ _ (hT _ _ h₁ h hh)
    change (if S.IsIntCls (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out then
      ENNReal.ofReal (S.wC (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out) *
        S.nT d (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₁).out _ else 0) = _
    rw [e', if_pos hint, (vol C₁ (hI _ _ h₁).1).2.2.2 h hh]
    congr 1
    unfold Frames.nT
    congr 1
    have hset : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = h • C₁} =
        (fun Λ : Submodule L.O S.V => h • Λ) '' {Λ | S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C₁} := by
      ext Λ
      constructor
      · rintro ⟨H, ⟨hb, -⟩, e⟩
        have hi := S.St.inv_mem hh
        refine ⟨h⁻¹ • Λ, ⟨hT _ _ H _ hi, (hB _ _ H _ hi).2 hb, ?_⟩, smul_inv_smul h Λ⟩
        rw [hF _ _ H _ hi, e, inv_smul_smul]
      · rintro ⟨Λ', ⟨H, hb, e⟩, rfl⟩
        have e2 : S.Fr d (h • Λ') = h • C₁ := by rw [hF _ _ H _ hh, e]
        exact ⟨hT _ _ H _ hh, ⟨(hB _ _ H _ hh).2 hb, h, hh, e2⟩, e2⟩
    rw [hset]
    exact (MulAction.injective h).encard_image _
  · intro o ho
    have h0 : S.nT d o.out (fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) = 0 := by
      unfold Frames.nT
      have : {Λ : Submodule L.O S.V | S.IsTerm d Λ ∧
        (S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • C₁) ∧ S.Fr d Λ = o.out} = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, ⟨-, s, hs, e⟩, e2⟩
        apply ho
        rw [← Quotient.out_eq o]
        apply Quotient.sound
        exact MulAction.orbitRel_apply.2 ⟨⟨s, hs⟩, by rw [← e2, e]; rfl⟩
      rw [this]
      simp
    simp only [h0, mul_zero, ite_self]

end GlobalTheory.HL.MassOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTrace
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameMass

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [TopologicalSpace E] in
theorem rmul_comp {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem hf_sum_left (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • x i) y = ∑ i, c i * hf L Hm (x i) y := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hf_sum_right (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm y (∑ i, c i • x i) = ∑ i, L.cj (c i) * hf L Hm y (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gram_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, hf_sum_right, Matrix.mul_apply, cT,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (cT L A).det = L.cj A.det := by
  have h : cT L A = (L.cj.toRingEquiv.toRingHom.mapMatrix A).transpose := by
    ext i j; rfl
  rw [h, Matrix.det_transpose, ← RingHom.map_det]
  rfl

omit [TopologicalSpace E] in
theorem span_rmul {n m : ℕ} (x : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (hB : IsUnit B.det) :
    Submodule.span E (Set.range x) ≤ Submodule.span E (Set.range (rmul x B)) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h : rmul (rmul x B) B⁻¹ = x := by
    rw [rmul_comp, Matrix.mul_nonsing_inv _ hB]
    funext j
    simp [rmul, Matrix.one_apply]
  have h2 : x j = ∑ i, B⁻¹ i j • rmul x B i := (congrFun h j).symm
  rw [SetLike.mem_coe, h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

theorem mass_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 2 * r + 6 ≤ k → (∃ Λ, IsSD L S.Hm Λ) → ∃ κ : ℝ, 0 < κ ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (∀ x ∈ Mh, x ∈ S.ME) → (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) → ENNReal.ofReal (κ / 2 * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) ≤ S.massSig Mh ∧ S.massSig Mh ≤ ENNReal.ofReal (2 * κ * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk ⟨Λs, hΛs⟩
  obtain ⟨x, hx, hME, -, hlat, hmass, hcls⟩ := GlobalTheory.HL.FrameTuple.main L r k S
  obtain ⟨κ, hκ, hU⟩ := _root_.GlobalTheory.HL.Unfold.mass_bounds L S.ϖ S.ϖ_irr S.Hm S.herm Λs hΛs (2 * r + 2) x hx
    (by omega) _ hlat
  refine ⟨κ, hκ, fun C hC p hp Mh hle hin hint => ?_⟩
  obtain ⟨y, B, hB, hy, hM⟩ := hcls C hC p hp
  have hBu : IsUnit B.det := IsUnit.of_mul_eq_one _ hB
  have hBc : IsUnit (L.cj B.det) := hBu.map L.cj
  have hyu : IsUnit (gramT L S.Hm y).det := by
    rw [hy, gram_rmul, Matrix.det_mul, Matrix.det_mul, det_cT]
    exact (hBc.mul hx).mul hBu
  obtain ⟨-, A, hAi, hAu, hMh, hli, hA⟩ := GlobalTheory.HL.OverBasis.exists_basis_overlattice L S.Hm S.herm
    (2 * r + 2) y hyu Mh (hM ▸ hle)
    (fun v hv => by rw [hy]; exact span_rmul x B hBu (hME ▸ hin v hv)) hint
  obtain ⟨hv, hidx⟩ := GlobalTheory.MatrixIndex.index_rmul L S.ϖ S.ϖ_irr _ hli A hAi hAu
  rw [hA, ← hM, ← hMh] at hidx
  have hinv : (A * B⁻¹)⁻¹ = B * A⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hBu]
  have hr : rmul x (A * B⁻¹)⁻¹ = rmul y A⁻¹ := by rw [hinv, hy, rmul_comp]
  have hBB : B⁻¹.det * B.det = 1 := Matrix.det_nonsing_inv_mul_det _ hBu
  have hdet : (A * B⁻¹).det * L.cj (A * B⁻¹).det = A.det * L.cj A.det := by
    have h1 : L.cj B⁻¹.det * L.cj B.det = 1 := by rw [← map_mul, hBB, map_one]
    rw [Matrix.det_mul, map_mul]
    linear_combination (-(A.det * L.cj A.det * B⁻¹.det * L.cj B⁻¹.det)) * hB
      + (A.det * L.cj A.det * L.cj B⁻¹.det * L.cj B.det) * hBB + (A.det * L.cj A.det) * h1
  have hu : IsUnit (A * B⁻¹).det := by
    rw [Matrix.det_mul]; exact hAu.mul (IsUnit.of_mul_eq_one _ hBB)
  have hI : IsIntM L (gramT L S.Hm (rmul x (A * B⁻¹)⁻¹)) := by
    rw [hr]
    intro a b
    refine hint _ ?_ _ ?_ <;> rw [hMh] <;> exact Submodule.subset_span ⟨_, rfl⟩
  have key := hU (A * B⁻¹) hu hI
  rw [hr, ← hMh, hdet, hME, ← hmass] at key
  have hpow : (resQ S.ϖ : ℝ) ^ (-(vE L S.ϖ (A.det * L.cj A.det) *
        (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)))) =
      (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹ := by
    rw [hidx, zpow_neg]
    congr 1
    have e : (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)) = ((k - 1 : ℕ) : ℤ) := by omega
    rw [e]
    conv_lhs => rw [← Int.toNat_of_nonneg hv]
    rw [← Nat.cast_mul, zpow_natCast, pow_mul]
    push_cast
    rfl
  rw [hpow] at key
  exact key

end GlobalTheory.HL.FrameMass
end

