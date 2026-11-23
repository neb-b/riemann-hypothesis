module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpi
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.DualCover

variable {A B : Type} [CommRing A] [CommRing B]

def dualMap (g : A →+* B) : DualNumber A →+* DualNumber B :=
  letI : Algebra A B := g.toAlgebra
  (DualNumber.lift ⟨(Algebra.ofId A (DualNumber B), DualNumber.eps), by simp, fun _ ↦ Commute.all _ _⟩).toRingHom

theorem dualMap_apply (g : A →+* B) (x : DualNumber A) :
    dualMap g x = TrivSqZeroExt.inl (g x.fst) + TrivSqZeroExt.inr (g x.snd) := by
  letI : Algebra A B := g.toAlgebra
  show (DualNumber.lift _ : DualNumber A →ₐ[A] DualNumber B) x = _
  rw [DualNumber.lift_apply_apply]
  ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]

@[simp] theorem dualMap_fst (g : A →+* B) (x : DualNumber A) : (dualMap g x).fst = g x.fst := by
  simp [dualMap_apply]

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover
variable {A B : Type} [CommRing A] [CommRing B]

theorem isPushout_dualMap (g : A →+* B) :
    IsPushout (CommRingCat.ofHom (algebraMap A (DualNumber A))) (CommRingCat.ofHom g)
      (CommRingCat.ofHom (dualMap g)) (CommRingCat.ofHom (algebraMap B (DualNumber B))) := by
  letI : Algebra A B := g.toAlgebra
  have hc : ∀ a : A, dualMap g (algebraMap A (DualNumber A) a) = algebraMap A (DualNumber B) a := by
    intro a
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let ψ₀ : DualNumber A →ₐ[A] DualNumber B := AlgHom.mk (dualMap g) hc
  have hψ₀ : ∀ x, ψ₀ x = dualMap g x := fun _ ↦ rfl
  let j : B →ₐ[A] DualNumber B := TrivSqZeroExt.inlAlgHom A B B
  let G : TensorProduct A (DualNumber A) B →ₐ[A] DualNumber B :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber B → TensorProduct A (DualNumber A) B := fun x ↦
    (1 : DualNumber A) ⊗ₜ[A] x.fst + (DualNumber.eps : DualNumber A) ⊗ₜ[A] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, G (h x) = x := by
    intro x
    simp only [h, G, map_add (f := _), Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀, dualMap_apply]
  have hhg : ∀ x, h (G x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber A) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, dualMap_apply, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber A) ⊗ₜ[A] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[A] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add (f := _), hadd, hx, hy]
  have hbij : Function.Bijective G := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  let eR : TensorProduct A (DualNumber A) B ≃+* DualNumber B := (AlgEquiv.ofBijective G hbij).toRingEquiv
  refine (CommRingCat.isPushout_tensorProduct A (DualNumber A) B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    eR.toCommRingCatIso (by simp) (by ext; simp [RingHom.algebraMap_toAlgebra]) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (x ⊗ₜ[A] 1) = dualMap g x
    simp [G, hψ₀]
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    show G (1 ⊗ₜ[A] x) = algebraMap B (DualNumber B) x
    simp [G, j, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.DualCover

namespace GlobalTheory.DualCover

theorem epi_spMap_dualMap {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}
    (hG : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {A B : Type} [CommRing A] [CommRing B] (g : A →+* B)
    (x : Sp A ⟶ Y) (x' : Sp B ⟶ X) (hsq : IsPullback (spMap g) x' x π) : Epi (spMap (dualMap g)) := by
  have h2 := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_dualMap g)
  have h3 : IsPullback (spMap (dualMap g)) (spMap (algebraMap B (DualNumber B)) ≫ x')
      (spMap (algebraMap A (DualNumber A)) ≫ x) π :=
    (IsPullback.paste_horiz h2.flip hsq.flip).flip
  have he := GlobalTheory.GaloisCartDesc.epi_pullback_fst hG (spMap (algebraMap A (DualNumber A)) ≫ x)
  rw [← h3.isoPullback_hom_fst]
  exact epi_comp _ _

theorem exists_dualCover : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), GlobalTheory.ZM.IsGaloisCover Ga ρ π → ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ Y), ∃ (R'' : Type) (_ : CommRing R'') (g₁ : R' →+* R'') (x'' : Sp R'' ⟶ X) (d₁ : DualNumber R' →+* DualNumber R''), x'' ≫ π = spMap g₁ ≫ x ∧ d₁.comp (algebraMap R' (DualNumber R')) = (algebraMap R'' (DualNumber R'')).comp g₁ ∧ (TrivSqZeroExt.fstHom R'' R'' R'').toRingHom.comp d₁ = g₁.comp (TrivSqZeroExt.fstHom R' R' R').toRingHom ∧ (∀ r : R', d₁.comp (epsScaleR r) = (epsScaleR (g₁ r)).comp d₁) ∧ Epi (spMap d₁) := by
  intro X Y π Ga _ ρ hG R' _ x
  haveI : IsFinite π := hG.fin
  haveI : IsAffine (pullback x π) := isAffine_of_isAffineHom (pullback.fst x π)
  let X' := pullback x π
  let g₁ : R' →+* Γ(X', ⊤) := (Spec.preimage (X'.isoSpec.inv ≫ pullback.fst x π)).hom
  have hg₁ : spMap g₁ = X'.isoSpec.inv ≫ pullback.fst x π := Spec.map_preimage _
  let x'' : Sp Γ(X', ⊤) ⟶ X := X'.isoSpec.inv ≫ pullback.snd x π
  have hsq : IsPullback (spMap g₁) x'' x π := by
    rw [hg₁]
    exact IsPullback.of_iso_pullback ⟨by simp [x'', pullback.condition]⟩ X'.isoSpec.symm (by simp) (by simp [x''])
  refine ⟨Γ(X', ⊤), inferInstance, g₁, x'', dualMap g₁, hsq.w.symm, ?_, ?_, ?_, epi_spMap_dualMap hG g₁ x x'' hsq⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [dualMap_apply, TrivSqZeroExt.algebraMap_eq_inl']
  · refine RingHom.ext fun a ↦ ?_
    simp
  · intro r
    refine RingHom.ext fun a ↦ ?_
    ext <;> simp [epsScaleR, dualMap_apply] <;> ring

end GlobalTheory.DualCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK

theorem exists_at_evI_piInf_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) z ∧ ∀ w, piInf (τ w) z = c w := by
  classical
  have := h.1
  have := h.2.1

  have hloc : ∀ w : InfinitePlace F, ∃ (α : E) (a b : w.Completion),
      InfinitePlace.Completion.extensionEmbedding w a +
        InfinitePlace.Completion.extensionEmbedding w b * (τ w).1 α = c w := by
    intro w
    have hα : ∃ α : E, ((τ w).1 α).im ≠ 0 := by
      by_contra hn
      push Not at hn
      refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (τ w).1)))
        (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
      exact Complex.conj_eq_iff_im.2 (hn x)
    obtain ⟨α, hα⟩ := hα
    have hs := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w)
    obtain ⟨a, ha⟩ := hs ((c w).re - (c w).im / ((τ w).1 α).im * ((τ w).1 α).re)
    obtain ⟨b, hb⟩ := hs ((c w).im / ((τ w).1 α).im)
    refine ⟨α, a, b, ?_⟩
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w), ha, hb]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]; field_simp; ring
  choose α a b hab using hloc
  let δ : ∀ w : InfinitePlace F, w.Completion → AF F := fun w x =>
    ((Pi.single w x : ∀ v : InfinitePlace F, v.Completion), 0)
  have hδ : ∀ (u : AF F), evI F u = 0 → ∀ w x, u * δ w x = 0 := by
    intro u hu w x
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have hp : ∀ w v x (e : E), piInf (τ w) (δ v x ⊗ₜ[F] e) =
      InfinitePlace.Completion.extensionEmbedding w ((Pi.single v x : ∀ v : InfinitePlace F, v.Completion) w)
        * (τ w).1 e := fun _ _ _ _ => rfl
  refine ⟨∑ w, (δ w (a w) ⊗ₜ[F] (1 : E) + δ w (b w) ⊗ₜ[F] α w), fun u hu => ?_, fun w => ?_⟩
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hδ u hu, hδ u hu,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single w]
      · rw [map_add (f := _), hp, hp, Pi.single_eq_same, Pi.single_eq_same, map_one, mul_one, hab]
      · intro v _ hv
        rw [map_add (f := _), hp, hp, Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, map_zero, zero_mul, zero_mul, add_zero]
      · simp

end GlobalTheory.ThK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.PrincCong

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_cj (w : Pl E) (x : w.adicCompletion E) : cj w (cj w x) = x := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · obtain ⟨hc, he⟩ := GlobalTheory.ConjAtPlace.cj_spec w h
    have := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) E w).equalizer (hc.comp hc) continuous_id
      (funext fun k => by simp only [Function.comp_apply, id, he, IsCMField.complexConj_apply_apply])
    exact congrFun this x
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; rfl

theorem cj_lt_one (w : Pl E) {z : w.adicCompletion E} (hz : Valued.v z < 1) : Valued.v (cj w z) < 1 := by
  by_cases h : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)
  · exact GlobalTheory.ConjAtPlace.lt_one_of_continuous _ (GlobalTheory.ConjAtPlace.cj_spec w h).1 hz
  · rw [GlobalTheory.ConjAtPlace.cj_of_not w h]; exact hz

theorem v_cj (w : Pl E) (x : w.adicCompletion E) : Valued.v (cj w x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hsx : cj w x ≠ 0 := fun h => hx (by rw [← cj_cj w x, h, map_zero])
  have p1 : 0 < Valued.v x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have p2 : 0 < Valued.v (cj w x) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hsx)
  rcases lt_trichotomy (Valued.v (cj w x)) (Valued.v x) with hlt | heq | hgt
  · exfalso
    have h1 : Valued.v (cj w x / x) < 1 := by rw [map_div₀, div_lt_one₀ p1]; exact hlt
    have h2 := cj_lt_one w h1
    rw [map_div₀ (cj w), cj_cj, map_div₀, div_lt_one₀ p2] at h2
    exact absurd h2 (not_lt.2 hlt.le)
  · exact heq
  · exfalso
    have h1 : Valued.v (x / cj w x) < 1 := by rw [map_div₀, div_lt_one₀ p2]; exact hgt
    have h2 := cj_lt_one w h1
    rw [map_div₀ (cj w), cj_cj, map_div₀, div_lt_one₀ p1] at h2
    exact absurd h2 (not_lt.2 hgt.le)

def congIdeal (w : Pl E) (k : ℕ) : Ideal (Ov E w) where
  carrier := {x | Valued.v (x : w.adicCompletion E) ≤ WithZero.exp (-(k : ℤ))}
  add_mem' := fun {a b} ha hb => by
    show Valued.v ((a : w.adicCompletion E) + b) ≤ _
    exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  zero_mem' := by
    show Valued.v ((0 : w.adicCompletion E)) ≤ _
    simp
  smul_mem' := fun c x hx => by
    show Valued.v ((c : w.adicCompletion E) * x) ≤ _
    have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
    rw [map_mul]
    exact mul_le_of_le_one_of_le hc hx

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def congSub (w : Pl E) (n k : ℕ) : Subgroup (GLw n w) :=
  ((GeneralLinearGroup.map (Ideal.Quotient.mk (congIdeal w k)) : GL (Fin n) (Ov E w) →* _).ker).map
    (bc (Ov E w).subtype)

theorem mem_ker_iff (w : Pl E) (n k : ℕ) (h : GL (Fin n) (Ov E w)) :
    h ∈ (GeneralLinearGroup.map (Ideal.Quotient.mk (congIdeal w k)) : GL (Fin n) (Ov E w) →* _).ker ↔
      ∀ i j, Valued.v ((((h : Matrix (Fin n) (Fin n) (Ov E w)) i j : Ov E w) : w.adicCompletion E) -
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  apply forall_congr'; intro i; apply forall_congr'; intro j
  change Ideal.Quotient.mk _ ((h : Matrix (Fin n) (Fin n) (Ov E w)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j ↔ _
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq]
    rw [← map_one (Ideal.Quotient.mk (congIdeal w k)), Ideal.Quotient.eq]
    show Valued.v (((_ - 1 : Ov E w)) : w.adicCompletion E) ≤ _ ↔ _
    push_cast; rfl
  · simp only [Matrix.one_apply_ne hij, Ideal.Quotient.eq_zero_iff_mem, sub_zero]
    rfl

theorem mem_congSub_iff (w : Pl E) (n k : ℕ) (g : GLw n w) :
    g ∈ congSub w n k ↔ g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j -
      (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h, rfl⟩, (mem_ker_iff w n k h).1 hh⟩
  · rintro ⟨⟨h, rfl⟩, hg⟩
    exact ⟨h, (mem_ker_iff w n k h).2 hg, rfl⟩

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cj_mem_Ov (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ Ov E w) : cj w x ∈ Ov E w := by
  change Valued.v (cj w x) ≤ 1
  rw [v_cj]; exact hx

theorem thL_mem_congSub (w : Pl E) (hw : ¬ IsSplitAt w) (n k : ℕ) (g : GLw n w) (hg : g ∈ congSub w n k) :
    thL n w g ∈ congSub w n k := by
  obtain ⟨h, hh, rfl⟩ := hg
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (cj_mem_Ov w)
  have hI : congIdeal w k ≤ (congIdeal w k).comap c' := by
    intro x hx
    show Valued.v (cj w (x : w.adicCompletion E)) ≤ _
    rw [v_cj]; exact hx
  let c'' := Ideal.quotientMap (congIdeal w k) c' hI
  refine ⟨thetaGL n c' h, ?_, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hh ⊢
  rw [GlobalTheory.ThetaPull.map_thetaGL (Ideal.Quotient.mk (congIdeal w k)) c' c''
    (fun x => (Ideal.quotientMap_mk).symm) h, hh, map_one]

theorem isOpen_ball (w : Pl E) (m : ℤ) : IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} = {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_ball_subset (w : Pl E) {U : Set (w.adicCompletion E)} {x : w.adicCompletion E} (hU : U ∈ 𝓝 x) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - x) ≤ WithZero.exp (-(N : ℤ)) → y ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun N hN y hy => hγ ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  refine hy.trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

theorem isOpen_congSub (w : Pl E) (n k : ℕ) : IsOpen (congSub w n k : Set (GLw n w)) := by
  have hs : (congSub w n k : Set (GLw n w)) = (GlobalTheory.LFun.KGL w (n := n) : Set (GLw n w)) ∩
      ⋂ i, ⋂ j, {g : GLw n w | Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
        WithZero.exp (-(k : ℤ))} := by
    ext g
    simp only [SetLike.mem_coe, mem_congSub_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hs]
  refine (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact (isOpen_ball w _).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem exists_mat_subset (w : Pl E) (n : ℕ) {C : Set (Matrix (Fin n) (Fin n) (w.adicCompletion E))}
    (hC : C ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      (∀ i j, Valued.v (M i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(N : ℤ))) → M ∈ C := by
  have h1 : C ∈ Filter.pi fun i => Filter.pi fun j => 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) := by
    have e : 𝓝 (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        Filter.pi fun i => Filter.pi fun j => 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) := by
      change 𝓝 (fun i j => (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) = _
      rw [nhds_pi]; congr 1; funext i; rw [nhds_pi]
    rw [← e]; exact hC
  obtain ⟨I, -, t, ht, hsub⟩ := Filter.mem_pi.1 h1
  have h2 : ∀ i, ∃ t' : Fin n → Set (w.adicCompletion E),
      (∀ j, t' j ∈ 𝓝 ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) ∧ Set.univ.pi t' ⊆ t i := by
    intro i
    obtain ⟨J, -, t', ht', hs'⟩ := Filter.mem_pi.1 (ht i)
    exact ⟨t', ht', fun x hx => hs' fun j _ => hx j (Set.mem_univ j)⟩
  choose t' ht' hs' using h2
  have h3 : ∀ i j, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ y, Valued.v (y - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(N : ℤ)) → y ∈ t' i j := fun i j => exists_ball_subset w (ht' i j)
  choose N₀ hN₀ using h3
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => N₀ p.1 p.2, fun N hN M hM => hsub fun i _ => hs' i fun j _ => ?_⟩
  refine hN₀ i j N ?_ _ (hM i j)
  exact le_trans (Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (i, j))) hN

end GlobalTheory.PrincCong

namespace GlobalTheory.PrincCong

open Filter Topology

end GlobalTheory.PrincCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBounds
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem exists_nat_mul_integral_of_valuation_le : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  intro E _ _ γ hγ
  have hfin : {u : Pl E | ¬ γ u ≤ 1}.Finite := Filter.eventually_cofinite.1 hγ
  let S : Finset (Pl E) := hfin.toFinset
  let k : Pl E → ℕ := fun u => (WithZero.log (γ u)).toNat
  let N : Pl E → ℕ := fun u => Ideal.absNorm u.asIdeal
  refine ⟨∏ u ∈ S, N u ^ k u, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro u _
    apply pow_ne_zero
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  · intro x hx
    have hval : ∀ u : Pl E, u.valuation E x * u.valuation E ((∏ w ∈ S, N w ^ k w : ℕ) : E) ≤ 1 := by
      intro u
      have hcast : (((∏ w ∈ S, N w ^ k w : ℕ) : E)) =
          algebraMap (𝓞 E) E ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) := (map_natCast _ _).symm
      rw [hcast, HeightOneSpectrum.valuation_of_algebraMap]
      by_cases hu : γ u ≤ 1
      · calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ 1 * 1 := mul_le_mul' ((hx u).trans hu) (u.intValuation_le_one _)
          _ = 1 := one_mul 1
      · have huS : u ∈ S := by
          simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hu
        have hmem : ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) ∈ u.asIdeal ^ k u := by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w => N w ^ k w) huS
          rw [hc, Nat.cast_mul]
          apply Ideal.mul_mem_right
          rw [Nat.cast_pow]
          exact Ideal.pow_mem_pow (Ideal.absNorm_mem u.asIdeal) _
        have hle := (u.intValuation_le_pow_iff_mem _ (k u)).2 hmem
        have h0 : γ u ≠ 0 := by
          intro h; exact hu (h ▸ zero_le')
        calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ γ u * WithZero.exp (-(k u : ℤ)) := mul_le_mul' (hx u) hle
          _ = WithZero.exp (WithZero.log (γ u) + -(k u : ℤ)) := by
              rw [WithZero.exp_add, WithZero.exp_log h0]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero, WithZero.exp_le_exp]
              have := Int.self_le_toNat (WithZero.log (γ u))
              simp only [k]
              omega
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (((∏ w ∈ S, N w ^ k w : ℕ) : E) * x) (fun u => by rw [map_mul, mul_comm]; exact hval u)
    exact ⟨a, by rw [← ha]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboliStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  first | exact @GlobalTheory.JSW.MirPatch.Cover.exists_cover | exact GlobalTheory.JSW.MirPatch.Cover.exists_cover | (intros; apply GlobalTheory.JSW.MirPatch.Cover.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxIdealSmulMemOfLtOfRelIndexNeZeroStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximalIdeal_smul_mem_of_lt_of_relIndex_ne_zero : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (N₀ N : Submodule (𝓞 F) V), N₀ < N → N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 → ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  first | exact @GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero | exact GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero | (intros; apply GlobalTheory.exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero <;> assumption)
end

