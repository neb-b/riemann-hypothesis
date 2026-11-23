module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmLiftOfMultilinearTprod
section
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RowReal

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

def omLiftOfMultilinear
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) : OM P →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    ((TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ).comp
      (((LinearMap.llcomp ℂ _ _ _ (TensorProduct.uncurry (RingHom.id ℂ) _ _ ℂ)).comp
        PiTensorProduct.lift.toLinearMap).comp (PiTensorProduct.lift Φ)))

theorem omLiftOfMultilinear_tprod
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) (x y v φ) :
    omLiftOfMultilinear P Φ (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) =
      Φ x y v φ := by
  simp only [omLiftOfMultilinear, TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.uncurry_apply,
    LinearMap.llcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]

theorem invFun_of_multilinear : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
    (Φ : MultilinearMap (RingHom.id ℂ) (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap (RingHom.id ℂ) (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ)))
    (hΦ : ∀ g x y v φ, Φ (fun j => rowFock P j g (x j)) (fun i => colFock P i g (y i)) (psiRep P g v)
      ((baseRep P).dual g φ) = Φ x y v φ), ∃ l ∈ invFun (omRep P), ∀ x y v φ,
      l (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) = Φ x y v φ := by
  intro ι _ _ S P Φ hΦ
  refine ⟨omLiftOfMultilinear P Φ, ?_, omLiftOfMultilinear_tprod P Φ⟩
  intro g z
  have key : (omLiftOfMultilinear P Φ).comp (omRep P g) = omLiftOfMultilinear P Φ := by
    ext x y v φ
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.restrictScalars_apply]
    rw [omRep, Representation.tprod_apply, TensorProduct.map_tmul, Representation.tprod_apply,
      TensorProduct.map_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
    simp only [piTprod, MonoidHom.comp_apply, PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod,
      Pi.monoidHom_apply, omLiftOfMultilinear_tprod]
    exact hΦ g x y v φ
  exact LinearMap.congr_fun key z

end GlobalTheory.RowReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodicThetaNormMeanFactorLe
section
open MeasureTheory

namespace GlobalTheory.PeriodicMean

theorem mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  intro g Λ Λ' Fd Fd' h u u' p n v T hΛc hΛ'c hF hF' hp hh hu hu' hpu hpu' hm hm' hT

  have hV : 0 < (volume Fd).toReal := by
    rcases (ENNReal.toReal_nonneg (a := volume Fd)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, div_zero] at hm; exact absurd hm zero_ne_one
  have hVt : volume Fd ≠ ⊤ := fun h0 => by simp [h0] at hV

  have hA1 : IntegrableOn (fun z => u' (h z) ^ 2) Fd volume ∧
      (∫ z in Fd, u' (h z) ^ 2) / (volume Fd).toReal = 1 := by
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ'.comap (h.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨h x, x.2⟩ : Λ')) := fun x y hxy =>
        Subtype.ext (h.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := _root_.GlobalTheory.AffineMean.affine_fundamentalDomain_mean g Λ' Λ₁ Fd' h 0 (fun z => u' z ^ 2) hΛ'c (fun z => Iff.rfl) hF'
      (fun a ha z => by simp only [hpu' a ha z]) hm'
    exact _root_.GlobalTheory.mean_fundamentalDomain_of_le g Λ Λ₁ Fd _ (fun z => u' (h z) ^ 2) hc (fun a ha => hh a ha) hF hD hVt
      (fun a ha z => by
        have : h (z + a) = h z + h a := map_add h z a
        rw [this, hpu' (h a) ha]) (by simpa using hmD)

  have hA2 : ∀ m, IntegrableOn (fun z => u ((p : ℂ) • z + v m) ^ 2) Fd volume ∧
      (∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2) / (volume Fd).toReal = 1 := by
    intro m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    let L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ.comap (L.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨L x, x.2⟩ : Λ)) := fun x y hxy =>
        Subtype.ext (L.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := _root_.GlobalTheory.AffineMean.affine_fundamentalDomain_mean g Λ Λ₁ Fd L (v m) (fun z => u z ^ 2) hΛc (fun z => Iff.rfl) hF
      (fun a ha z => by simp only [hpu a ha z]) hm
    refine _root_.GlobalTheory.mean_fundamentalDomain_of_le g Λ Λ₁ Fd _ (fun z => u ((p : ℂ) • z + v m) ^ 2) hc ?_ hF hD hVt ?_ hmD
    · intro a ha
      change (p : ℂ) • a ∈ Λ
      have : (p : ℂ) • a = p • a := by rw [Nat.cast_smul_eq_nsmul]
      rw [this]; exact Λ.nsmul_mem ha p
    · intro a ha z
      have ha' : (p : ℂ) • a ∈ Λ := ha
      have : (p : ℂ) • (z + a) + v m = ((p : ℂ) • z + v m) + (p : ℂ) • a := by rw [smul_add]; abel
      simp only [this, hpu _ ha']
  obtain ⟨hI1, hM1⟩ := hA1
  have hE1 : ∫ z in Fd, u' (h z) ^ 2 = (volume Fd).toReal := by
    field_simp at hM1; linarith
  have hE2 : ∀ m, ∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2 = (volume Fd).toReal := fun m => by
    have := (hA2 m).2; field_simp at this; linarith
  rcases le_or_gt T 0 with hT0 | hT0
  · exact hT0.trans (Nat.cast_nonneg n)

  have hpt : ∀ z, T ^ 2 * u' (h z) ^ 2 ≤ (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    intro z
    have h0 : 0 ≤ T * u' (h z) := mul_nonneg hT0.le (hu' _)
    calc T ^ 2 * u' (h z) ^ 2 = (T * u' (h z)) ^ 2 := by ring
      _ ≤ (∑ m, u ((p : ℂ) • z + v m)) ^ 2 := pow_le_pow_left₀ h0 (hT z) 2
      _ ≤ (Finset.univ : Finset (Fin n)).card * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by simp
  have hint : ∫ z in Fd, T ^ 2 * u' (h z) ^ 2 ≤ ∫ z in Fd, (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) ?_
      (Filter.Eventually.of_forall hpt)
    exact (integrable_finsetSum _ fun m _ => (hA2 m).1).const_mul _
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun m _ => (hA2 m).1, hE1] at hint
  simp only [hE2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hint
  have hT2 : T ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hT2 (Nat.cast_nonneg n) |>.2 |> fun h => h

end GlobalTheory.PeriodicMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowSubCreationVacuumFockBoundStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_sub_creation_vacuum_fock_bound : ∀ (T H : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : T →ₗ[ℂ] H) (a c : Module.End ℂ T) (s : ℝ) (v : T), 0 ≤ s → (∀ x y, inner ℂ (Φ (c x)) (Φ y) = inner ℂ (Φ x) (Φ (a y))) → a * c - c * a = (s : ℂ) • 1 → a v = 0 → (∀ K : Submodule ℂ T, v ∈ K → (∀ x ∈ K, c x ∈ K) → ∀ k : ℕ, ((c - a) ^ k) v ∈ K) ∧ ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial := by
  first | exact @GlobalTheory.pow_vacuum_fock_bound | exact GlobalTheory.pow_vacuum_fock_bound | (intros; apply GlobalTheory.pow_vacuum_fock_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqGaussianOfFderivAddEqZeroStatement
section
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_add_eq_zero' : ∀ (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ)), (∀ (j : l) (x : EuclideanSpace ℝ l), fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0) → ∀ x, h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero | exact GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero | (intros; apply GlobalTheory.schwartz_eq_gaussian_of_fderiv_add_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClasses
section
open GlobalTheory

namespace GlobalTheory.ShuffleCount

open MvPolynomial

private theorem aeval_killCompl {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (h0 : ∀ Δ ∉ U, φ Δ = 0) (P : MvPolynomial S ℚ) :
    aeval (fun Δ : U => φ Δ) (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = aeval φ P := by
  classical
  have key : (aeval (fun Δ : U => φ Δ)).comp (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S))) = aeval φ := by
    apply MvPolynomial.algHom_ext
    intro Δ
    by_cases hΔ : Δ ∈ U
    · have hX : (X Δ : MvPolynomial S ℚ) = rename Subtype.val (X (⟨Δ, hΔ⟩ : U)) := by rw [rename_X]
      rw [AlgHom.comp_apply]
      conv_lhs => rw [hX]
      rw [killCompl_rename_app, aeval_X, aeval_X]
    · rw [AlgHom.comp_apply, aeval_X, h0 Δ hΔ, X, killCompl_monomial_eq_zero_of_not_subset, map_zero]
      intro h
      obtain ⟨⟨_, hmem⟩, rfl⟩ := h (by simp : Δ ∈ (↑(Finsupp.single Δ 1).support : Set S))
      exact hΔ hmem
  exact AlgHom.congr_fun key P

private theorem coeff_killCompl_comapDomain {S : Type*} (U : Set S) (P : MvPolynomial S ℚ) (m : S →₀ ℕ)
    (hm : ↑m.support ⊆ Set.range (Subtype.val : U → S)) :
    AddMonoidAlgebra.coeff (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P)
      (m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn) = AddMonoidAlgebra.coeff P m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n r =>
    by_cases hn : ↑n.support ⊆ Set.range (Subtype.val : U → S)
    · rw [killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hn, coeff_monomial, coeff_monomial]
      have hiff : n.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn =
          m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn ↔ n = m := by
        constructor
        · intro h
          rw [← Finsupp.mapDomain_comapDomain _ Subtype.val_injective n hn,
            ← Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hm, h]
        · rintro rfl
          rfl
      simp only [hiff]
    · rw [killCompl_monomial_eq_zero_of_not_subset _ _ hn, AddMonoidAlgebra.coeff_zero,
        coeff_monomial]
      split_ifs with h
      · subst n
        exact (hn hm).elim
      · rfl
  | add P Q hP hQ => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ]

theorem coeff_eq_zero_of_aeval_eq_zero {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ)) (h0 : ∀ Δ ∉ U, φ Δ = 0)
    (P : MvPolynomial S ℚ) (hP : aeval φ P = 0) (m : S →₀ ℕ) (hm : ∀ Δ ∈ m.support, Δ ∈ U) :
    AddMonoidAlgebra.coeff P m = 0 := by
  classical
  have hm' : ↑m.support ⊆ Set.range (Subtype.val : U → S) := fun Δ hΔ =>
    ⟨⟨Δ, hm Δ (Finset.mem_coe.1 hΔ)⟩, rfl⟩
  rw [← coeff_killCompl_comapDomain U P m hm']
  have hQ : killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 hind
    rw [map_zero, aeval_killCompl U φ h0 P, hP]
  rw [hQ]
  simp

theorem separates_of_shuffle_count : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  intro I S A _ _ Ψ M U ℓ φ hinj hU hφ0 hcnt n p c hp hne hc
  classical
  let Rh : List A → (I →₀ ℤ) →+ ℤ := fun w =>
    Finsupp.liftAddHom fun x => AddMonoidHom.mulRight ((M x w).toNat : ℤ)
  have hRs : ∀ w x a, Rh w (Finsupp.single x a) = a * ((M x w).toNat : ℤ) := fun w x a => by
    simp [Rh]
  have hRsum : ∀ w (y : I →₀ ℤ), Rh w y = y.sum fun x a => a * ((M x w).toNat : ℤ) := fun w y => by
    simp [Rh, Finsupp.liftAddHom_apply]
  have K0 : ∀ (y : I →₀ ℤ) (w : List A) (N : ℕ), 0 ≤ y →
      (y.sum fun x a => (a.toNat : ℕ∞) * M x w) = (N : ℕ∞) → Rh w y = N := by
    intro y w N hy hN
    rw [Finsupp.sum] at hN
    have hfin : ∀ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w ≠ ⊤ := by
      intro x hx htop
      have hle : ((y x).toNat : ℕ∞) * M x w ≤ ∑ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w :=
        Finset.single_le_sum (f := fun x => ((y x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx
      rw [hN, htop] at hle
      exact ENat.natCast_ne_top N (top_le_iff.1 hle)
    have h1 := congrArg ENat.toNat hN
    rw [ENat.toNat_sum hfin, ENat.toNat_natCast] at h1
    simp only [ENat.toNat_mul, ENat.toNat_natCast] at h1
    rw [hRsum, Finsupp.sum, ← h1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_mul, Int.toNat_of_nonneg (Finsupp.le_def.1 hy x)]
  have K1 : ∀ (w : List A) (P : MvPolynomial S ℤ),
      (ShuffleAlgebra.wordBasis ℚ A).repr (aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P)) w =
        ((Rh w (Ψ.symm P) : ℤ) : ℚ) := by
    intro w P
    induction P using MvPolynomial.induction_on' with
    | monomial m r =>
      obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
      have hmr : (MvPolynomial.monomial m r : MvPolynomial S ℤ) = r • MvPolynomial.monomial m 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, ← hs2, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, Lyndon.repr_sum_word, hmr, map_zsmul, map_zsmul, K0 _ w _ hpos (hs1 w),
        smul_eq_mul, smul_eq_mul]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      congr
    | add P Q hP hQ =>
      simp only [map_add (f := _), Finsupp.add_apply, hP, hQ, Int.cast_add]
  have K2 : ∀ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) →
      ∀ x, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 → ∀ w, M x w = 0 := by
    rintro m ⟨Δ, hΔ, hΔU⟩ x hx w
    obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
    have hprod : (m.prod fun Δ e => φ Δ ^ e) = 0 :=
      Finset.prod_eq_zero hΔ (by show φ Δ ^ m Δ = 0; rw [hφ0 Δ hΔU, zero_pow (Finsupp.mem_support_iff.1 hΔ)])
    have hcount : s.count w = 0 := by
      have h := Lyndon.repr_sum_word ℚ s w
      rw [hs2, hprod, map_zero, Finsupp.zero_apply] at h
      have h'' := Nat.cast_eq_zero.1 h.symm
      convert h''
    have h1 := hs1 w
    rw [hcount, Finsupp.sum, Nat.cast_zero, Finset.sum_eq_zero_iff] at h1
    have h2 := h1 x (Finsupp.mem_support_iff.2 hx)
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso
      have hnn := Finsupp.le_def.1 hpos x
      have h0 : (Ψ.symm (MvPolynomial.monomial m 1) x).toNat = 0 := by exact_mod_cast h
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hnn
      omega
    · exact h
  have hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ) := by
    have hR := Published.radfordShufflePolynomial_holds.algebraicIndependent ℚ A
    have he : Function.Injective
        (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      intro a b hab
      exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    have hcomp := hR.comp _ he
    have heq : (fun Δ : U => φ Δ) =
        (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word ℚ l.1) ∘
          (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      funext Δ
      exact (hU Δ Δ.2).2
    rw [heq]
    exact hcomp
  have K3 : ∀ k : Fin n → ℤ, (∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0) → ∀ i, k i = 0 := by
    intro k hk i
    by_contra hki
    set y : I →₀ ℤ := ∑ j, Finsupp.single (p j) (k j) with hy
    have hRy : ∀ w, Rh w y = 0 := fun w => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy, map_sum]
      simp only [hRs]
      exact hk w
    set P := Ψ y with hPdef
    have hEv : aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 := by
      apply (ShuffleAlgebra.wordBasis ℚ A).repr.injective
      rw [map_zero]
      ext w
      rw [K1, hPdef, AddEquiv.symm_apply_apply, hRy, Int.cast_zero, Finsupp.zero_apply]
    have hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0 := by
      intro m hm
      have h := coeff_eq_zero_of_aeval_eq_zero U φ hind hφ0 _ hEv m hm
      rw [MvPolynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at h
      exact h
    have hyP : y = ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1) := by
      have h : y = Ψ.symm P := by rw [hPdef, AddEquiv.symm_apply_apply]
      conv_lhs => rw [h, P.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hyi : y (p i) = k i := by
      rw [hy, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hji (hp h)
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hne0 : (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) (p i) ≠ 0 := by
      rw [← hyP, hyi]
      exact hki
    rw [Finsupp.finsetSum_apply] at hne0
    obtain ⟨m, _, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    rw [Finsupp.smul_apply, smul_eq_mul] at hm0
    have hc0 : P.coeff m ≠ 0 := left_ne_zero_of_mul hm0
    have hx0 : Ψ.symm (MvPolynomial.monomial m 1) (p i) ≠ 0 := right_ne_zero_of_mul hm0
    have hout : ∃ Δ ∈ m.support, Δ ∉ U := by
      by_contra h
      push_neg at h
      exact hc0 (hcoef m h)
    obtain ⟨w, hw⟩ := hne i
    exact hw (K2 m hout (p i) hx0 w)
  have KQ : ∀ q : Fin n → ℚ, (∀ w, ∑ j, q j * ((M (p j) w).toNat : ℚ) = 0) → ∀ i, q i = 0 := by
    intro q hq i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Fin n)) q
    choose k hk using fun j => RingHom.mem_rangeS.1 (hb j (Finset.mem_univ j))
    have hk' : ∀ j, (k j : ℚ) = ((b : ℤ) : ℚ) * q j := fun j => by
      simpa [Algebra.smul_def] using hk j
    have hkrel : ∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0 := by
      intro w
      have h : ((∑ j, k j * ((M (p j) w).toNat : ℤ) : ℤ) : ℚ) = 0 := by
        push_cast
        simp only [hk', mul_assoc, ← Finset.mul_sum, hq w, mul_zero]
      exact_mod_cast h
    have hki := K3 k hkrel i
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have h2 := hk' i
    rw [hki, Int.cast_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hb0
  intro i
  have hq : ∀ ψ : Module.Dual ℚ ℂ, ∀ j, ψ (c j) = 0 := by
    intro ψ
    apply KQ (fun j => ψ (c j))
    intro w
    have h := congrArg ψ (hc w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ψ (c j) * _ = ψ (c j * _)
    rw [mul_comm (c j), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (c i)).1 fun ψ => hq ψ i

end GlobalTheory.ShuffleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulInvariantMeasureShearedProductPairGroup
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem smulInvariantMeasure_shear_map (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (hκ : κ.IsHaarMeasure)
    (hconj : ∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) :
    SMulInvariantMeasure (pairGroup Γ N hN) (H × H) ((κ.prod ν).map (shear N)) := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  refine ⟨fun g s hs => ?_⟩
  obtain ⟨⟨u, v⟩, hu, hv, huv⟩ := g
  have hmeasg : Measurable (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) := by
    change Measurable (fun x : H × H => (u * x.1, v * x.2))
    exact (measurable_fst.const_mul u).prodMk (measurable_snd.const_mul v)
  let δ : N := ⟨u * v⁻¹, huv⟩
  let c : N → N := fun n => ⟨v * n * v⁻¹, hN v hv n n.2⟩
  have hc : MeasurePreserving c κ κ :=
    ⟨(show Continuous c from ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _).measurable,
      hconj v hv⟩
  have hf : MeasurePreserving (fun n : N => δ * c n) κ κ := (measurePreserving_mul_left κ δ).comp hc
  have hT : MeasurePreserving (Prod.map (fun n : N => δ * c n) (fun h : H => v * h)) (κ.prod ν) (κ.prod ν) :=
    hf.prod (measurePreserving_mul_left ν v)
  have hsh := (measurableEmbedding_shear (N := N) hNc)
  have key : (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) ∘ shear N
      = shear N ∘ Prod.map (fun n : N => δ * c n) (fun h : H => v * h) := by
    funext p
    change (u * (p.1 * p.2), v * p.2) = (((u * v⁻¹) * (v * p.1 * v⁻¹)) * (v * p.2), v * p.2)
    congr 1
    group
  rw [← Measure.map_apply hmeasg hs, Measure.map_map hmeasg hsh.measurable, key,
    ← Measure.map_map hsh.measurable hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOutStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_norm_coset_out' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  first | exact @GlobalTheory.summable_norm_coset_out | exact GlobalTheory.summable_norm_coset_out | (intros; apply GlobalTheory.summable_norm_coset_out <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSetIntegralFundamentalDomainEqZeroByOrbitsStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_setIntegral_fundamentalDomain_eq_zero_by_orbits : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν → IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) → ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by
  first | exact @GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | exact GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero | (intros; apply GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryExistsSkewLogStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_log_of_unitary : ∀ (n : ℕ) (k : Matrix (Fin n) (Fin n) ℂ), kᴴ * k = 1 → ∃ (X : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Xᴴ = -X ∧ NormedSpace.exp X = k ∧ X = Polynomial.aeval k p := by
  first | exact @GlobalTheory.unitary_exists_skew_log | exact GlobalTheory.unitary_exists_skew_log | (intros; apply GlobalTheory.unitary_exists_skew_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylNumberOperatorCommutationStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_number_operator_commutation_alt : ∀ (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A] [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A), (∀ x, J (J x) = -x) → (∀ u v, D (u + v) = D u + D v) → (∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v) → (∀ u v, D u * D v - D v * D u = (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1) → (∀ z, c z = D z - Complex.I • D (J z)) → (∀ z, a z = -(D z + Complex.I • D (J z))) → N = ∑ j, c (e j) * a (e j) → (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧ (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  first | exact @GlobalTheory.weyl_number_operator_commutation | exact GlobalTheory.weyl_number_operator_commutation | (intros; apply GlobalTheory.weyl_number_operator_commutation <;> assumption)
end

