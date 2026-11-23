module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
public import ReciprocityTheory.DualLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0216
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.FrameModel

theorem det_append_eq_mul_det : ∀ (C : Type) [Field C] (w : Valuation C NNReal) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → ∀ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C), GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w x (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ).mkQ (u i)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w m (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) → ∃ c : C, w c = ∏ s ∈ Finset.univ.erase τ, w ((a τ : C) - (a s : C)) ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) ∧ (Matrix.of (Fin.append u m)).det = c * (Matrix.of x).det := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q Fil τ ha hFil x u m hx hu hm
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ with hF
  have hfin : Module.finrank C F = q := by
    have hsp : F = Submodule.span C (Set.range m) := by
      rw [hF, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace, ← hm.2, Submodule.span_span_of_tower]
    rw [hsp, finrank_span_eq_card hm.1, Fintype.card_fin]
  have hd0 : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hs).symm
  have h1 := GlobalTheory.T.latticeDetRelation_herbrand_eigenspace C w ℓ hℓ0 hℓ1 S a p q Fil τ ha hFil hfin
  rw [GlobalTheory.T.piEigenSublattice_free_eq_differentScaled C w S a (p + q) τ ha] at h1
  have h2 := GlobalTheory.T.latticeDetRelation_of_lsmul_shift C w ℓ hℓ0 hℓ1 p q _ _ _ _ _ _ hd0 h1
  obtain ⟨x', u', m', c, hx', hu', hm', hmF, ⟨hc0, hcv⟩, hdet⟩ := h2
  obtain ⟨P, hP, hPdet⟩ := GlobalTheory.DetRelCompare.transition x' x _ hx' hx
  obtain ⟨A, hA, hAdet⟩ := GlobalTheory.DetRelCompare.transition _ _ _ hu' hu
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.DetRelCompare.transition m' m _ hm' hm
  have hx'0 : (Matrix.of x').det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hx'.1)).ne_zero
  have happ0 : (Matrix.of (Fin.append u' m')).det ≠ 0 := by
    intro h0
    exact hx'0 (by rw [hdet, h0, mul_zero])
  have hrel := GlobalTheory.DetRelCompare.det_append_eq F u u' m m' A B hA hB hu'.1 hmF happ0
  have hxP : (Matrix.of x).det = P.det * (Matrix.of x').det := by
    have hmat : Matrix.of x = P * Matrix.of x' := by
      ext i k
      simp [Matrix.mul_apply, hP i, Finset.sum_apply]
    rw [hmat, Matrix.det_mul]
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPdet
    exact zero_ne_one hPdet
  refine ⟨A.det * B.det * (P.det * c)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_mul, hAdet, hBdet, hPdet, one_mul, one_mul, one_mul]
    have hlam : Real.log (w ℓ : ℝ) ≠ 0 :=
      (Real.log_neg (NNReal.coe_pos.mpr hℓ0) (NNReal.coe_lt_one.mpr hℓ1)).ne
    have hds : ∀ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ) ≠ 0 := by
      intro s hs
      rw [NNReal.coe_ne_zero, Valuation.ne_zero_iff]
      exact sub_ne_zero.mpr (Subtype.coe_injective.ne (ha.ne (Finset.ne_of_mem_erase hs).symm))
    have hdiff : ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ : w.valuationSubring) : C)
        = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen]
    have hle : ∀ s, Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) ≤ p + q := fun s =>
      (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun C)
    have hlogc : Real.log (w c : ℝ) = - ∑ s ∈ Finset.univ.erase τ,
        ((p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℕ) : ℝ)
          * Real.log (w ((a τ : C) - (a s : C)) : ℝ) := by
      have e := hcv
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal] at e
      rw [hdiff, map_prod, NNReal.coe_prod, Real.log_prod hds, div_eq_iff hlam] at e
      rw [e, sub_mul, Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ hlam, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (hle s)]
      field_simp
      ring
    have hwc : 0 < ((w c : NNReal) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff w).mpr hc0))
    apply NNReal.coe_injective
    rw [NNReal.coe_inv, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    have hpos2 : 0 < ∏ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ)
        ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) :=
      Finset.prod_pos fun s hs => pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (hds s hs).symm) _
    rw [← Real.exp_log (inv_pos.mpr hwc), ← Real.exp_log hpos2, Real.log_inv, hlogc, neg_neg,
      Real.log_prod fun s hs => pow_ne_zero _ (hds s hs)]
    simp only [Real.log_pow]
  · rw [hrel, hxP, hdet]
    field_simp

end GlobalTheory.FrameModel

namespace GlobalTheory.FrameModel

section Small

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

end Small

end GlobalTheory.FrameModel

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticWeakSolWordDerivLeConstMulSup
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SupEst

variable {d : ℕ}

theorem dw_zero_fun : ∀ w : List (Fin d), dw w (fun _ : E d => (0 : ℂ)) = fun _ => 0
  | [] => rfl
  | j :: w => by
      funext x
      show fderiv ℝ (dw w (fun _ : E d => (0 : ℂ))) x (ev j) = 0
      rw [dw_zero_fun w]
      simp

theorem tr_eq_zero_of_notMem {ι : Type} (P : Sys d ι) (i : ι) {φ : E d → ℂ} {x : E d}
    (hx : x ∉ tsupport φ) : P.tr i φ x = 0 := by
  unfold Sys.tr trOp
  refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun w _ => ?_
  have hO : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  have hEq : Set.EqOn (fun y => P.a i n w y * φ y) (fun _ => (0 : ℂ)) (tsupport φ)ᶜ := by
    intro y hy
    have : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have := eqOn_dw_of_isOpen hO (List.ofFn w) _ _ hEq hx
  rw [this, dw_zero_fun]
  simp

end GlobalTheory.HCA.SupEst


open GlobalTheory.HCA.SupEst in
theorem GlobalTheory.HCA.dw_le_sup : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by
  intro d ι _ P U hU ha hell w x₀ hx₀
  obtain ⟨S, hS⟩ := (solSet_closed_submodule d ι P U hU ha).2
  obtain ⟨l, hl⟩ := _root_.GlobalTheory.HCA.dw_solSet_continuous_functional d ι P U hU ha hell S hS w x₀ hx₀
  refine ⟨‖l‖, norm_nonneg _, ?_⟩
  intro u hu hweak M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  have hcont : Continuous (U.restrict u) := continuousOn_iff_continuous_restrict.mp hu
  let u' : U →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (U.restrict u) hcont M
    (fun x => hM x.1 x.2)
  have hu'n : ‖u'‖ ≤ M := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM0 _
  have hext : Set.EqOn (ext0 U u') u U := by
    intro x hx
    simp only [ext0, hx, dif_pos, u']
    rfl
  have hmem : u' ∈ solSet P U := by
    intro i φ h1 h2 h3
    rw [← hweak i φ h1 h2 h3]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hext hx]
    · have : x ∉ tsupport φ := fun h => hx (h3 h)
      rw [tr_eq_zero_of_notMem P i this]
      simp
  have hmemS : u' ∈ S := by rw [← SetLike.mem_coe, hS]; exact hmem
  have hval : l ⟨u', hmemS⟩ = dw w u x₀ := by
    rw [hl]
    exact eqOn_dw_of_isOpen hU w _ _ hext hx₀
  rw [← hval]
  calc ‖l ⟨u', hmemS⟩‖ ≤ ‖l‖ * ‖(⟨u', hmemS⟩ : S)‖ := l.le_opNorm _
    _ = ‖l‖ * ‖u'‖ := rfl
    _ ≤ ‖l‖ * M := mul_le_mul_of_nonneg_left hu'n (norm_nonneg _)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequence
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.CoefSeq

variable {R : Type} [CommRing R]

end GlobalTheory.EtC.CoefSeq

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_comp_injective {A B C C' : Type*} [Zero C] [Zero C'] {f : A → B} {g : B → C}
    {β : C → C'} (hfg : Function.Exact f g) (hβ : Function.Injective β) (h0 : β 0 = 0) :
    Function.Exact f (β ∘ g) := by
  intro y
  rw [← hfg y, Function.comp_apply, ← h0]
  exact hβ.eq_iff

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_conj_bijection_middle {A B B' C : Type*} [Zero C] {f : A → B} {g : B → C}
    (β : B → B') (δ : B' → B) (hδβ : ∀ b, δ (β b) = b) (hβδ : ∀ b', β (δ b') = b')
    (hfg : Function.Exact f g) : Function.Exact (β ∘ f) (g ∘ δ) := by
  intro y
  rw [Function.comp_apply, hfg (δ y)]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [Function.comp_apply, hx, hβδ]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by rw [Function.comp_apply, hδβ]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma exact_comp_surjective {A A' B C : Type*} [Zero C] {f : A → B} {g : B → C}
    {γ : A' → A} (hfg : Function.Exact f g) (hγ : Function.Surjective γ) :
    Function.Exact (f ∘ γ) g := by
  intro y
  rw [hfg y, Set.range_comp, hγ.range_eq, Set.image_univ]


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.coefSeq_exact : _root_.GlobalTheory.EtC.A7 := by
  unfold _root_.GlobalTheory.EtC.A7
  intro R _ S hS
  obtain ⟨e, ⟨hom⟩⟩ := _root_.GlobalTheory.EtC.cone_resMap_homotopyEquiv R S hS
  refine ⟨_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
    (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1), fun K n => ?_⟩
  obtain ⟨ex₁, ex₂, ex₃⟩ :=
    _root_.GlobalTheory.EtC.coneSeqTgt_exact R K (_root_.GlobalTheory.EtC.resMap R S.f) n
  have hinvhom : ∀ x, _root_.GlobalTheory.EtC.cpush K e.inv n (_root_.GlobalTheory.EtC.cpush K e.hom n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyHomInvId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hhominv : ∀ x, _root_.GlobalTheory.EtC.cpush K e.hom n (_root_.GlobalTheory.EtC.cpush K e.inv n x) = x := by
    intro x
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_comp, _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K e.homotopyInvHomId,
      _root_.GlobalTheory.EtC.InjResCmp.cpush_id]
  have hg : ⇑(_root_.GlobalTheory.EtC.HK.post R K S.g n) =
      ⇑(_root_.GlobalTheory.EtC.cpush K e.hom n) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K (mappingCone.inr (_root_.GlobalTheory.EtC.resMap R S.f)) n) := by
    funext x
    show _root_.GlobalTheory.EtC.cpush K (_root_.GlobalTheory.EtC.resMap R S.g) n x = _
    rw [← _root_.GlobalTheory.EtC.InjResCmp.cpush_homotopy K hom, _root_.GlobalTheory.EtC.InjResCmp.cpush_comp]
    rfl
  have hδ : ⇑(_root_.GlobalTheory.EtC.HK.ext R K
      (_root_.GlobalTheory.EtC.zcomp (Cocycle.ofHom e.inv)
        (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) (zero_add 1)) n (n + 1) rfl) =
      ⇑(_root_.GlobalTheory.EtC.cpost K (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)) n (n + 1) rfl) ∘
        ⇑(_root_.GlobalTheory.EtC.cpush K e.inv n) := by
    funext y
    exact ((_root_.GlobalTheory.cocycle_comp_assoc_classes R (add_zero n) (zero_add 1) rfl rfl).2.2
      y (Cocycle.ofHom e.inv) (mappingCone.fst (_root_.GlobalTheory.EtC.resMap R S.f)))
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact exact_comp_injective ex₁ (Function.LeftInverse.injective hinvhom) (map_zero _)
  · rw [hg, hδ]
    exact exact_conj_bijection_middle _ _ hinvhom hhominv ex₂
  · rw [hδ]
    exact exact_comp_surjective ex₃ (Function.LeftInverse.surjective hinvhom)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscElt

variable (R : Type) [CommRing R]

theorem hkpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hkpull_single {X Y : Shv R} (g : X ⟶ Y) (F : Shv R) (n : ℤ) (t : Y ⟶ (res R F).X n)
    (ht : t ≫ (res R F).d n (n + 1) = 0) :
    HK.pull R ((CochainComplex.singleFunctor (Shv R) 0).map g) F n
      (CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)) =
      CohomologyClass.mk (Cocycle.fromSingleMk (g ≫ t) (zero_add n) (n + 1) rfl (by simp [ht])) := by
  rw [Cocycle.fromSingleMk_precomp g t (zero_add n) (n + 1) rfl ht]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cocycle.precomp]

end GlobalTheory.EtC.DiscElt

namespace GlobalTheory.EtC


open GlobalTheory.EtC.DiscElt in
theorem disc_elt_cls : ∀ (R : Type) [CommRing R] (F : Shv R), ∃ cl : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 → H R (disc.obj P) F n, (∀ P n x, ∃ t ht, cl P n t ht = x) ∧ (∀ P n t ht t' ht', cl P n t ht = cl P n t' ht' ↔ ∃ y : (free R).obj P ⟶ (res R F).X (n - 1), t = t' + y ≫ (res R F).d (n - 1) n) ∧ (∀ P n, cl P n 0 zero_comp = 0) ∧ ∀ (P P' : PSh) (f : P ⟶ P') n t ht, ∃ h, pull R (disc.map f) F n (cl P' n t ht) = cl P n ((free R).map f ≫ t) h := by
  intro R _ F
  obtain ⟨e, -, hnat⟩ := chains_disc_homotopyEquiv R
  have hb : ∀ (P : PSh) (n : ℤ), Function.Bijective (HK.pull R (e P).hom F n) := fun P n => by
    haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
    exact quasiIso_hypercohomology_bijective' R (e P).hom F n
  let E : ∀ (P : PSh) (n : ℤ), H R (disc.obj P) F n ≃ HK R (sgl ((free R).obj P)) F n :=
    fun P n => Equiv.ofBijective _ (hb P n)
  have hE : ∀ P n x, E P n x = HK.pull R (e P).hom F n x := fun _ _ _ => rfl
  let c : ∀ (P : PSh) (n : ℤ) (t : (free R).obj P ⟶ (res R F).X n), t ≫ (res R F).d n (n + 1) = 0 →
      HK R (sgl ((free R).obj P)) F n :=
    fun P n t ht => CohomologyClass.mk (Cocycle.fromSingleMk t (zero_add n) (n + 1) rfl ht)
  refine ⟨fun P n t ht => (E P n).symm (c P n t ht), ?_, ?_, ?_, ?_⟩
  · intro P n x
    obtain ⟨z, hz⟩ := (E P n x).mk_surjective
    obtain ⟨t, ht, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n + 1) rfl
    exact ⟨t, ht, by rw [Equiv.symm_apply_eq]; exact hz⟩
  · intro P n t ht t' ht'
    rw [(E P n).symm.injective.eq_iff]
    change CohomologyClass.mk _ = CohomologyClass.mk _ ↔ _
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, ← Cocycle.fromSingleMk_sub _ _ _ _ _ ht ht',
      CohomologyClass.mk_eq_zero_iff,
      Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (n - 1) (by omega)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; abel⟩
  · intro P n
    change (E P n).symm (CohomologyClass.mk _) = 0
    rw [Equiv.symm_apply_eq, hE, map_zero, Cocycle.fromSingleMk_zero, CohomologyClass.mk_zero]
  · intro P P' f n t ht
    refine ⟨by simp [ht], ?_⟩
    rw [Equiv.eq_symm_apply, hE]
    change HK.pull R (e P).hom F n (HK.pull R ((chains R).map (disc.map f)) F n _) = _
    rw [← hkpull_comp, hnat f, hkpull_comp]
    have h1 : HK.pull R (e P').hom F n ((E P' n).symm (c P' n t ht)) = c P' n t ht := by
      rw [← hE, Equiv.apply_symm_apply]
    rw [h1]
    exact hkpull_single R ((free R).map f) F n t ht

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyStalkLocalClasses
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem stalk_local_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (Θ Θ₂ : Over S ⥤ Spc) (α : Θ ⟶ Θ₂), (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F (Θ.mapCone c)) → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F (Θ₂.mapCone c)) → ∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (α.app (Over.mk s)) F → ∀ (U : Over S), Etale U.hom → ∀ (g : Over.mk s ⟶ U) (n : ℤ), (∀ x : H R (Θ.obj U) F n, ∃ (V : Over S) (g₁ : Over.mk s ⟶ V) (h : V ⟶ U) (y : H R (Θ₂.obj V) F n), Etale V.hom ∧ g₁ ≫ h = g ∧ pull R (α.app V) F n y = pull R (Θ.map h) F n x) ∧ ∀ y : H R (Θ₂.obj U) F n, pull R (α.app U) F n y = 0 → ∃ (V : Over S) (g₁ : Over.mk s ⟶ V) (h : V ⟶ U), Etale V.hom ∧ g₁ ≫ h = g ∧ pull R (Θ₂.map h) F n y = 0 := by
  intro R _ F S Θ Θ' α hΘ hΘ' O _ s hs hα U hU g n
  obtain ⟨I, _, _, G, π, ⟨hl⟩, hG⟩ := GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' S O s hs
  haveI : IsConnected I := IsCofiltered.isConnected I
  have hcF : IsLimit ((Over.forget S).mapCone (Cone.mk _ π)) := isLimitOfPreserves (Over.forget S) hl
  haveI : ∀ i, IsAffine ((G ⋙ Over.forget S).obj i) := fun i => (hG i).1
  haveI : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((G ⋙ Over.forget S).map f) := fun _ => inferInstance
  haveI : LocallyOfFinitePresentation U.hom := inferInstance
  let t0 : G ⋙ Over.forget S ⟶ (Functor.const I).obj S :=
    { app := fun i => (G.obj i).hom, naturality := fun i j f => by simp }
  obtain ⟨j, u0, hu0, hu1⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (G ⋙ Over.forget S) t0 U.hom _ hcF g.left (by
      ext i
      exact (Over.w (π.app i)).trans (Over.w g).symm)
  let u : G.obj j ⟶ U := Over.homMk u0 hu1
  have hu : π.app j ≫ u = g := Over.OverMorphism.ext hu0
  have hπ : ∀ {i k : I} (f : k ⟶ i), π.app k ≫ G.map f = π.app i := fun f => by
    simpa using (π.naturality f).symm
  have hnat : ∀ {A B : Over S} (f : A ⟶ B) (y : H R (Θ'.obj B) F n),
      pull R (Θ.map f) F n (pull R (α.app B) F n y) = pull R (α.app A) F n (pull R (Θ'.map f) F n y) := by
    intro A B f y
    rw [← pull_comp, ← pull_comp, α.naturality]
  have cΘ := hΘ I G (Cone.mk _ π) hl (fun i => (hG i).1) n
  have cΘ' := hΘ' I G (Cone.mk _ π) hl (fun i => (hG i).1) n
  simp only [Functor.mapCone_π_app, Functor.comp_obj, Functor.comp_map] at cΘ cΘ'
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (hα n).2 (pull R (Θ.map g) F n x)
    obtain ⟨i, y0, hy0⟩ := cΘ'.1 w
    let k := IsCofiltered.min i j
    let fi : k ⟶ i := IsCofiltered.minToLeft i j
    let fj : k ⟶ j := IsCofiltered.minToRight i j
    let y1 := pull R (Θ'.map (G.map fi)) F n y0
    have hgh : π.app k ≫ (G.map fj ≫ u) = g := by rw [← Category.assoc, hπ, hu]
    have hd : pull R (Θ.map (π.app k)) F n
        (pull R (α.app (G.obj k)) F n y1 - pull R (Θ.map (G.map fj ≫ u)) F n x) = 0 := by
      have e1 : pull R (Θ.map (π.app k)) F n (pull R (α.app (G.obj k)) F n y1) = pull R (Θ.map g) F n x := by
        rw [hnat]
        show pull R (α.app (Over.mk s)) F n (pull R (Θ'.map (π.app k)) F n (pull R (Θ'.map (G.map fi)) F n y0)) = _
        rw [← pull_comp R (Θ'.map (π.app k)), ← Functor.map_comp, hπ, hy0]
        exact hw
      have e2 : pull R (Θ.map (π.app k)) F n (pull R (Θ.map (G.map fj ≫ u)) F n x) = pull R (Θ.map g) F n x := by
        rw [← pull_comp, ← Functor.map_comp, hgh]
      rw [map_sub, e1, e2, sub_self]
    obtain ⟨k', f', hf'⟩ := cΘ.2 k _ hd
    refine ⟨G.obj k', π.app k', G.map f' ≫ G.map fj ≫ u, pull R (Θ'.map (G.map f')) F n y1, (hG k').2, ?_, ?_⟩
    · rw [← Category.assoc, hπ, hgh]
    · rw [map_sub, sub_eq_zero, hnat] at hf'
      rw [hf', ← pull_comp, ← Functor.map_comp]
  · have h0 : pull R (Θ'.map g) F n y = 0 := (hα n).1 (by rw [map_zero, ← hnat, hy, map_zero])
    rw [← hu, Functor.map_comp, pull_comp] at h0
    obtain ⟨k, f, hf⟩ := cΘ'.2 j _ h0
    exact ⟨G.obj k, π.app k, G.map f ≫ u, (hG k).2, by rw [← Category.assoc, hπ, hu],
      by rw [Functor.map_comp, pull_comp, hf]⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainMapOfFibreCocyclePairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cochain_map_of_fibre_cocycle_pairing : ∀ (q N : ℕ) (i₁ i₂ i : ℤ) (h : i₁ + i₂ = i) (d : ℕ) (z : Cocycle ((chains (ZMod q)).obj (fibQ q N)) (res (ZMod q) (tw q i₂)) (2 * (d : ℤ))), ∃ ψ : Cocycle (res (ZMod q) (tw q i₁)) (Jcx (ZMod q) q N (res (ZMod q) (tw q i))) (2 * (d : ℤ)), ∀ (m w : ℤ) (hw : m + 2 * (d : ℤ) = w) (U : Scheme.{0}) (a : Sec ((res (ZMod q) (tw q i₁)).X m) U), ∃ c : Cochain ((chains (ZMod q)).obj (sch.obj U ⨯ fibQ q N)) (res (ZMod q) (tw q i)) w, Sec.map (ψ.1.v m w hw) a = Jsec c ∧ ∀ (k : ℕ) (s : ℤ) (hs : -(k : ℤ) + w = s) (V : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) k V), ev c k s hs V y = twCast h ((twPair q i₁ i₂).mul V m (-(k : ℤ) + 2 * (d : ℤ)) s (by omega) (Sec.res (Sx.map (prod.fst : sch.obj U ⨯ fibQ q N ⟶ _) y : V ⟶ U) a) (ev z.1 k (-(k : ℤ) + 2 * (d : ℤ)) rfl V (Sx.map prod.snd y))) := by
  first | (exact @GlobalTheory.EtC.PsiModel.psi_exists) | (exact GlobalTheory.EtC.PsiModel.psi_exists) | (intros; apply GlobalTheory.EtC.PsiModel.psi_exists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleLiftingLineBundleTransitionUnitsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_lifting_lineBundle_transition_units : ∀ (q : ℕ) (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → (∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) → ∃ a : Cocycle ((chains ℤ).obj E) (sgl C) 1, ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c := by
  intro q C qb E L hE hb
  obtain ⟨α, hα⟩ := CupSpec.ev_exists (liftFam qb L hE hb) (liftFam_nat qb L hE hb)
  have hδα : δ 1 2 α = 0 := by
    apply CupSpec.ev_ext
    intro p t ht U x
    rw [CupSpec.ev_zero]
    by_cases h0 : t = 0
    · subst h0
      obtain rfl : p = 2 := by omega
      rw [CupSpec.ev_δ_succ (by norm_num) α U 1 (-1) 0 (by simp) ht x]
      simp only [hα]
      rw [show liftFam qb L hE hb 2 (-1) (by simp) U x = 0 from rfl,
        PicSpec.sec_map_zero, zero_add, Fin.sum_univ_three]
      simp only [liftFam_one]
      rw [liftSec_face, PicSpec.sec_map_add]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
      simp
    · exact PicSpec.sec_eq_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ h0) _
  refine ⟨Cocycle.mk α 2 (by norm_num) hδα, fun U x =>
    ⟨liftSec qb L hE hb U x, liftSec_spec qb L hE hb U x, ?_⟩⟩
  exact (hα 1 0 _ U x).trans (liftFam_one qb L hE hb _ U x)
end

