module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSqStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_cm_type_product_sq : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ d : E, ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.cm_type_normSq_prod_eq_abs_norm | exact GlobalTheory.cm_type_normSq_prod_eq_abs_norm | (intros; apply GlobalTheory.cm_type_normSq_prod_eq_abs_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndex
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def skewSub (G : Matrix (Fin r) (Fin r) E) : Submodule (maximalRealSubfield E) (Matrix (Fin r) (Fin r) E) where
  carrier := {X | X.trace = 0 ∧ ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0}
  zero_mem' := ⟨by simp, by simp [herm, cc]⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    have h2 := hY.2 u w
    simp only [herm, cc, add_mulVec, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX := by
    have hc : IsCMField.complexConj E (c : E) = c := IsCMField.complexConj_apply_eq_self E c
    have e : c • X = (c : E) • X := rfl
    refine ⟨by rw [e, trace_smul, hX.1, smul_zero], fun u w => ?_⟩
    have h1 := hX.2 u w
    rw [e]
    simp only [herm, cc, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, hc] at h1 ⊢
    have e1 : ∀ a b, ((c : E) * (X *ᵥ u) a) * G a b * (IsCMField.complexConj E) (w b) =
        (c : E) * ((X *ᵥ u) a * G a b * (IsCMField.complexConj E) (w b)) := fun a b => by ring
    have e2 : ∀ a b, u a * G a b * ((c : E) * (IsCMField.complexConj E) ((X *ᵥ w) b)) =
        (c : E) * (u a * G a b * (IsCMField.complexConj E) ((X *ᵥ w) b)) := fun a b => by ring
    simp only [e1, e2, ← Finset.mul_sum]
    rw [← mul_add, h1, mul_zero]

def trForm (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0) :
    LinearMap.BilinForm (maximalRealSubfield E) (skewSub G) :=
  LinearMap.mk₂ (maximalRealSubfield E)
    (fun X Y => ⟨(X.1 * Y.1).trace, _root_.GlobalTheory.trace_mul_skew_mem_maximalRealSubfield E r G X.1 Y.1 hG hd X.2.2 Y.2.2⟩)
    (fun X₁ X₂ Y => Subtype.ext (by simp [add_mul, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))
    (fun X Y₁ Y₂ => Subtype.ext (by simp [mul_add, trace_add]))
    (fun c X Y => Subtype.ext (by simp [trace_smul]; rfl))

theorem trForm_apply (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a) (hd : G.det ≠ 0)
    (X Y : skewSub G) : ((trForm G hG hd X Y : maximalRealSubfield E) : E) = (X.1 * Y.1).trace := rfl

theorem norm_algebraMap_real (d : maximalRealSubfield E) :
    Algebra.norm ℚ (algebraMap (maximalRealSubfield E) E d) = (Algebra.norm ℚ d) ^ 2 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := maximalRealSubfield E), Algebra.norm_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]

theorem isIntegral_coe_iff (x : maximalRealSubfield E) : IsIntegral ℤ (x : E) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E).toRingHom.injective

theorem abs_norm_gram_eq_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  intro E _ _ _ r G Λ e hr hΛ he hli
  obtain ⟨hG, hd, hfg, hsp, -⟩ := hΛ
  have heV : ∀ i, e i ∈ skewSub G := fun i => ⟨(he i).1, (he i).2.1⟩
  set v : Fin (r ^ 2 - 1) → skewSub G := fun i => ⟨e i, heV i⟩ with hv_def
  have hve : (skewSub G).subtype ∘ v = e := rfl
  have hvli : LinearIndependent (maximalRealSubfield E) v :=
    LinearIndependent.of_comp (skewSub G).subtype (by rw [hve]; exact hli)
  have hmapv : Submodule.map (skewSub G).subtype (Submodule.span (maximalRealSubfield E) (Set.range v)) =
      Submodule.span _ (Set.range e) := by
    rw [Submodule.map_span, ← Set.range_comp, hve]
  have hspan : ⊤ ≤ Submodule.span (maximalRealSubfield E) (Set.range v) := by
    rintro ⟨X, hX⟩ -
    have h := _root_.GlobalTheory.SkewSpan.mem_span_of_skew E r G e hG hd heV hli X hX.1 hX.2
    rw [← hmapv] at h
    obtain ⟨y, hy, hyX⟩ := h
    have : y = ⟨X, hX⟩ := Subtype.ext hyX
    rwa [← this]
  set b := Module.Basis.mk hvli hspan with hb
  have hbv : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hvli hspan i
  set B := trForm G hG hd with hB
  set f : skewSub G →+ Matrix (Fin r) (Fin r) E := (skewSub G).subtype.toAddMonoidHom with hf_def
  have hf : Function.Injective f := Subtype.val_injective
  set L' := (lieLat G Λ).comap f with hL'
  have hLrange : lieLat G Λ ≤ f.range := fun X hX => ⟨⟨X, hX.1, hX.2.1⟩, rfl⟩
  have hLmap : L'.map f = lieLat G Λ := AddSubgroup.map_comap_eq_self hLrange
  have hsymm : B.IsSymm := ⟨fun x y => Subtype.ext (by rw [hB, trForm_apply, trForm_apply]; exact Matrix.trace_mul_comm _ _)⟩
  have hsep : ∀ X : skewSub G, (∀ Y : skewSub G, B X Y = 0) → X = 0 := by
    intro X hX
    apply Subtype.ext
    refine _root_.GlobalTheory.TraceSkew.traceForm_nondegenerate E r G X.1 hG hd X.2.1 X.2.2 fun Y hY1 hY2 => ?_
    have := congrArg (fun z : maximalRealSubfield E => (z : E)) (hX ⟨Y, hY1, hY2⟩)
    simpa [hB, trForm_apply] using this
  have hnd : B.Nondegenerate := ⟨fun X hX => hsep X hX, fun Y hY => hsep Y fun X => by rw [hsymm.eq]; exact hY X⟩
  have hbL : ∀ i, b i ∈ L' := fun i => by rw [hbv]; exact he i
  have hsm : ∀ (a : 𝓞 (maximalRealSubfield E)) x, x ∈ L' → a • x ∈ L' := by
    intro a x hx
    refine ⟨(a • x).2.1, (a • x).2.2, fun y hy => ?_⟩
    have hc : IsIntegral ℤ (((a : maximalRealSubfield E) : E)) := (isIntegral_coe_iff _).2 a.isIntegral_coe
    have e1 : (f (a • x)) = (((a : maximalRealSubfield E) : E)) • x.1 := rfl
    rw [e1, smul_mulVec]
    have e2 : (((a : maximalRealSubfield E) : E)) • (x.1 *ᵥ y) = (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) • (x.1 *ᵥ y) := by
      rw [← algebraMap_smul E (⟨_, (mem_integralClosure_iff ℤ E).2 hc⟩ : 𝓞 E) (x.1 *ᵥ y)]; rfl
    rw [e2]
    exact Λ.smul_mem _ (hx.2.2 y hy)
  have hint : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (B x y) := by
    intro x hx y hy
    rw [← isIntegral_coe_iff, hB, trForm_apply]
    refine _root_.GlobalTheory.LatTrace.trace_isIntegral_of_preserves_lattice E r Λ _ hfg hsp fun z hz => ?_
    rw [← mulVec_mulVec]
    exact hx.2.2 _ (hy.2.2 z hz)
  have key := _root_.GlobalTheory.abs_norm_det_gram_eq_relIndex (maximalRealSubfield E) (skewSub G) (r ^ 2 - 1) b B L' hsymm hnd hbL hsm hint
  have hdet : (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      algebraMap (maximalRealSubfield E) E (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hbv]
    rfl
  have I1 : (lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧
      (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) =
      L'.relIndex (AddSubgroup.closure {y | ∀ x ∈ L', IsIntegral ℤ (B x y)}) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap, AddMonoidHom.map_closure]
    congr 2
    ext Y
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨Y, h1, h2⟩, fun x hx => ?_, rfl⟩
      rw [← isIntegral_coe_iff, hB, trForm_apply]
      exact h3 _ hx
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2.1, y.2.2, fun X hX => ?_⟩
      have := hy ⟨X, hX.1, hX.2.1⟩ hX
      rw [← isIntegral_coe_iff, hB, trForm_apply] at this
      exact this
  have I2 : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) =
      (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).toAddSubgroup.relIndex L' := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, hLmap]
    congr 1
    let g : skewSub G →ₗ[𝓞 (maximalRealSubfield E)] Matrix (Fin r) (Fin r) E :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hg : (Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range b)).map g =
        Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext i
      simp [g, hbv, v]
    rw [← hg, Submodule.map_toAddSubgroup]
    rfl
  rw [hdet, norm_algebraMap_real, I1, I2, ← key]
  push_cast
  rw [abs_pow, sq_abs]

end GlobalTheory.LieIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSection
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

noncomputable section

namespace GlobalTheory.TateResidue

open WithConv

theorem conv_eq_one_of_mul {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O)
    {B : Type} [CommRing B] [Algebra O B] (n : ℕ) (a b : WithConv (G.A n →ₐ[O] B))
    (h : a * b = b) : a = 1 :=
  (IsUnit.of_pow_eq_one (G.pts_pow_self n b)
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mul_right_cancel (h.trans (one_mul _).symm)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O), ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c) ∧ ∃ s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate, (∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t) ∧ ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)), t.pt n = t'.pt n → (s t).pt n = (s t').pt n := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h =>
    hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 h)⟩
  set k := IsLocalRing.ResidueField O
  set π := G.tatePush (Algebra.ofId O k)

  have hlift : ∀ (n : ℕ) (c : G.A n →ₐ[O] k), ∃ t : G.Tate, (π t).pt n = c := by
    intro n c
    obtain ⟨x, hx⟩ := _root_.GlobalTheory.ResiduePointLift.exists_algHom_lift p C v O hv (G.A n) c
    obtain ⟨t, ht⟩ := G.pt_surjective C n x
    refine ⟨t, AlgHom.ext fun a => ?_⟩
    rw [tatePush_pt]
    change IsLocalRing.residue O (t.pt n a) = c a
    rw [show t.pt n = x from ht]
    exact hx a
  refine ⟨fun n c => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hlift n c
    exact ⟨π t, ht⟩
  have := G.finite_tate C
  have hπ : Function.Surjective π := by
    refine TateFree.surjective_of_mod π TateOver.eq_zero_of_forall_pow_smul fun y => ?_
    obtain ⟨x, hx⟩ := hlift 1 (y.pt 1)
    obtain ⟨z, hz⟩ := (TateOver.conv_eq_one_iff (y - π x) 1).1 <| by
      have h1 : (y - π x + π x).conv 1 = y.conv 1 := by rw [sub_add_cancel]
      rw [TateOver.add_conv] at h1
      have h2 : (π x).conv 1 = y.conv 1 := congrArg toConv hx
      rw [h2] at h1
      exact conv_eq_one_of_mul G _ _ _ h1
    exact ⟨x, z, by rwa [pow_one] at hz⟩
  have : Module.Finite ℤ_[p] (G.TateOver k) := Module.Finite.of_surjective π hπ
  have : Module.Free ℤ_[p] (G.TateOver k) := inferInstance
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨s, fun t => LinearMap.congr_fun hs t, fun n t t' h => ?_⟩
  have hd : (t - t').conv n = 1 := by
    have h1 : (t - t' + t').conv n = t.conv n := by rw [sub_add_cancel]
    rw [TateOver.add_conv, show t'.conv n = t.conv n from congrArg toConv h.symm] at h1
    exact conv_eq_one_of_mul G _ _ _ h1
  obtain ⟨u, hu⟩ := (TateOver.conv_eq_one_iff (t - t') n).1 hd
  have h3 : (s t - s t').conv n = 1 := by
    rw [← map_sub, ← hu, map_smul]
    exact (TateOver.conv_eq_one_iff _ n).2 ⟨_, rfl⟩
  have h4 : (s t - s t' + s t').conv n = (s t).conv n := by rw [sub_add_cancel]
  rw [TateOver.add_conv, h3, one_mul] at h4
  exact congrArg ofConv h4.symm

end GlobalTheory.TateResidue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmType
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeLat

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem exists_one_le_norm {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K} (hα : α ≠ 0) :
    ∃ i, 1 ≤ ‖φ i (α : K)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ w : InfinitePlace K, w (α : K) < 1 := by
    intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    rw [← InfinitePlace.norm_embedding_eq]
    rcases hi with hi | hi
    · rw [hi]; exact h i
    · rw [hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact h i
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))

theorem one_le_norm_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K}
    (hα : GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0) : 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  have h0 : α ≠ 0 := by
    rintro rfl
    apply hα
    funext i
    simp [GlobalTheory.HeckeTheta.emb]
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  exact hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)

def embHom (φ : I → K →+* ℂ) : 𝓞 K →+ (I → ℂ) where
  toFun α := GlobalTheory.HeckeTheta.emb φ (α : K)
  map_zero' := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by funext i; simp [GlobalTheory.HeckeTheta.emb]

theorem embHom_injective {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : Function.Injective (embHom φ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  have : φ i (a : K) = 0 := congrFun ha i
  rw [this, norm_zero] at hi
  exact absurd hi (by norm_num)


omit [Fintype I] in
theorem summable_exp_neg_mul_norm_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by
  set k := Module.finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

def embLat (φ : I → K →+* ℂ) : Submodule ℤ (I → ℂ) := LinearMap.range (embHom φ).toIntLinearMap

theorem discrete_embLat {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by
  refine DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K) := by
    rw [← ha, ← hb]
    funext i
    simp [embHom, GlobalTheory.HeckeTheta.emb]
  rw [hsub]
  apply one_le_norm_emb hφ
  rw [← hsub, sub_ne_zero]
  exact fun h => hxy (Subtype.ext h)

theorem summable_exp_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun α : 𝓞 K => Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2) := by
  haveI := discrete_embLat hφ
  have hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2) :=
    summable_exp_neg_mul_norm_sq (embLat φ) hε
  have hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ := fun α => LinearMap.mem_range_self _ α
  let j : 𝓞 K → embLat φ := fun α => ⟨embHom φ α, hmem α⟩
  have hj : Function.Injective j := fun a b h => embHom_injective hφ (congrArg Subtype.val h)
  have h2 := hs.comp_injective hj
  refine h2.congr fun α => ?_
  simp only [Function.comp_apply, j]
  rfl

theorem bounded_of_periodic {M : Ideal (𝓞 K)} (F : 𝓞 K → ℂ) (hM : M ≠ ⊥)
    (hF : ∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) : ∃ C : ℝ, ∀ α, ‖F α‖ ≤ C := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM
  haveI := Fintype.ofFinite (𝓞 K ⧸ M)
  refine ⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩
  have hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have hα : F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
    have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem
    rwa [add_sub_cancel] at this
  rw [hα]
  exact Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

theorem periodic_bound_summable_norm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  intro K _ _ _ I _ φ hφ M F hM hF
  obtain ⟨C, hC⟩ := bounded_of_periodic F hM hF
  refine ⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩
  refine ((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  exact mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le

end GlobalTheory.HeckeLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLAdicRationalCohomologyGaloisCoverInvari
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory

theorem pullHQ_galoisCover_inv : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, Function.Injective (pullHQ l (sch.map f) n i) ∧
  LinearMap.range (pullHQ l (sch.map f) n i) = ⨅ g, LinearMap.ker (pullHQ l (sch.map (a g)) n i - LinearMap.id) := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  obtain ⟨tr, h1, h2⟩ := GlobalTheory.T.exists_trace_finiteEtaleGaloisCover_ladic l f G a ha hiso n i
  set F := pullHQ l (sch.map f) n i with hF
  set T := tr.baseChange ℚ_[l] with hT
  have pqc : ∀ {A B C : Scheme.{0}} (u : A ⟶ B) (v : B ⟶ C),
      pullHQ l (sch.map (u ≫ v)) n i = (pullHQ l (sch.map u) n i).comp (pullHQ l (sch.map v) n i) := by
    intro A B C u v
    rw [pullHQ, pullHQ, pullHQ, ← LinearMap.baseChange_comp, ← pullHl_comp, ← Functor.map_comp]
  have pqi : ∀ A : Scheme.{0}, pullHQ l (sch.map (𝟙 A)) n i = LinearMap.id := by
    intro A
    rw [pullHQ, CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  have key1 : ∀ x, T (F x) = (Fintype.card G : ℚ_[l]) • x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h1, Nat.cast_smul_eq_nsmul]
      exact TensorProduct.tmul_smul _ _ _
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  have key2 : ∀ y, F (T y) = ∑ g, pullHQ l (sch.map (a g)) n i y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hF, pullHQ, hT, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, h2, TensorProduct.tmul_sum]
      simp only [pullHQ, LinearMap.baseChange_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, ← Finset.sum_add_distrib]; simp only [map_add (f := _)]
  have comp : ∀ g, (pullHQ l (sch.map (a g)) n i).comp F = F := by
    intro g
    rw [hF, ← pqc, ha g]
  by_cases hG : Fintype.card G = 0
  ·
    haveI : IsEmpty G := Fintype.card_eq_zero_iff.mp hG
    have hS : IsEmpty ↥(∐ (fun _ : G => Y)) := by
      constructor
      intro p
      obtain ⟨j, _⟩ := (sigmaOpenCover (fun _ : G => Y)).exists_eq p
      exact isEmptyElim (show G from j)
    haveI hYe : IsEmpty Y :=
      ⟨fun y => hS.false ((pullback.lift (𝟙 Y) (𝟙 Y) rfl ≫ inv (Sigma.desc (fun g =>
        pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f)).base y)⟩
    haveI : IsEmpty X := ⟨fun x => by
      obtain ⟨y, _⟩ := (inferInstance : Surjective f).surj x
      exact hYe.false y⟩
    haveI : IsIso f := isIso_of_isEmpty f
    have e1 : (pullHQ l (sch.map (inv f)) n i).comp F = LinearMap.id := by
      rw [hF, ← pqc, IsIso.inv_hom_id, pqi]
    have e2 : F.comp (pullHQ l (sch.map (inv f)) n i) = LinearMap.id := by
      rw [hF, ← pqc, IsIso.hom_inv_id, pqi]
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have := congrArg (pullHQ l (sch.map (inv f)) n i) hxy
      rwa [← LinearMap.comp_apply, e1, ← LinearMap.comp_apply, e1] at this
    · rw [iInf_of_empty, LinearMap.range_eq_top]
      intro y
      exact ⟨pullHQ l (sch.map (inv f)) n i y, by rw [← LinearMap.comp_apply, e2, LinearMap.id_apply]⟩
  have hc : (Fintype.card G : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hG
  refine ⟨fun x y hxy => ?_, ?_⟩
  · have := congrArg T hxy
    rw [key1, key1] at this
    exact smul_right_injective _ hc this
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      intro g
      rw [← LinearMap.comp_apply, comp g, sub_self]
    · intro y hy
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hy
      refine ⟨(Fintype.card G : ℚ_[l])⁻¹ • T y, ?_⟩
      rw [map_smul, key2]
      simp only [hy, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hc, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackFormsIntersectionEqChartLocalizationStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  first | (exact @GlobalTheory.PD.omB_comap_loc) | (exact GlobalTheory.PD.omB_comap_loc) | (intros; apply GlobalTheory.PD.omB_comap_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
  (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  first | (exact @GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (exact GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (intros; apply GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic  <;> assumption)
end

