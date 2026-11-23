module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalBranchesOfSeparableReduction
section
open Filter Topology

namespace GlobalTheory.ShiftHomomorphism

noncomputable def shiftHom (D : ℕ) (c : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPowerSeries (Fin D) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.X i + MvPowerSeries.C (c i))

theorem shiftHom_X (D : ℕ) (c : Fin D → ℂ) (i : Fin D) :
    shiftHom D c (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  simp [shiftHom]

theorem constantCoeff_comp_shiftHom (D : ℕ) (c : Fin D → ℂ) :
    (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)).comp (shiftHom D c).toRingHom
      = MvPolynomial.eval c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [shiftHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C, MvPolynomial.eval_C]
    first | rfl | simp [MvPowerSeries.algebraMap_apply] | simp [Algebra.algebraMap_eq_smul_one]
  · intro i; simp [shiftHom]

theorem shiftHom_injective (D : ℕ) (c : Fin D → ℂ) : Function.Injective (shiftHom D c) := by
  let τ : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i))
  let τ' : MvPolynomial (Fin D) ℂ →ₐ[ℂ] MvPolynomial (Fin D) ℂ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i))
  have hinv : τ'.comp τ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext; intro i; simp [τ, τ']
  have hτ : Function.Injective τ := by
    intro a b h
    have := congrArg τ' h
    simpa [← AlgHom.comp_apply, hinv] using this
  have hfac : shiftHom D c = (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp τ := by
    apply MvPolynomial.algHom_ext; intro i; simp [shiftHom, τ]
  rw [hfac]
  exact (MvPolynomial.coe_injective _ _).comp hτ

end GlobalTheory.ShiftHomomorphism

namespace GlobalTheory


open GlobalTheory.ShiftHomomorphism in
theorem branches_of_unramified_point : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by
  intro D P c hP hsep
  haveI : IsDomain (MvPowerSeries (Fin D) ℂ) := NoZeroDivisors.to_isDomain _
  set ψ := shiftHom D c with hψ
  set Q := P.map ψ.toRingHom with hQ
  have hQm : Q.Monic := hP.map _
  have hred : Q.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ)) = P.map (MvPolynomial.eval c) := by
    rw [hQ, Polynomial.map_map, constantCoeff_comp_shiftHom]
  obtain ⟨θ, hθi, hθr⟩ := GlobalTheory.T.exists_lifts_of_separable_reduction D Q hQm (by rw [hred]; exact hsep)
  have hroot : ∀ j, P.eval₂ ψ.toRingHom (θ j) = 0 := by
    intro j
    have := hθr j
    rw [Polynomial.IsRoot.def, hQ, Polynomial.eval_map] at this
    exact this
  refine ⟨Q.natDegree, fun j => AdjoinRoot.liftAlgHom P ψ (θ j) (hroot j), ?_, ?_⟩
  · intro u hu
    obtain ⟨R, rfl⟩ := AdjoinRoot.mk_surjective u
    have hR : AdjoinRoot.mk P R = AdjoinRoot.mk P (R %ₘ P) := by
      rw [← AdjoinRoot.modByMonicHom_mk hP R, AdjoinRoot.mk_leftInverse hP]
    rw [hR] at hu ⊢
    by_contra hne
    have hR0 : R %ₘ P ≠ 0 := by
      intro h; apply hne; rw [h, map_zero]
    have hdeg : (R %ₘ P).natDegree < P.natDegree :=
      Polynomial.natDegree_lt_natDegree hR0 (Polynomial.degree_modByMonic_lt R hP)
    have hz : (R %ₘ P).map ψ.toRingHom = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hθi ?_ ?_
      · intro j
        have := hu j
        simpa [AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, Polynomial.eval_map] using this
      · calc ((R %ₘ P).map ψ.toRingHom).natDegree ≤ (R %ₘ P).natDegree := Polynomial.natDegree_map_le
          _ < P.natDegree := hdeg
          _ = Q.natDegree := (hP.natDegree_map _).symm
          _ = Fintype.card (Fin Q.natDegree) := (Fintype.card_fin _).symm
    apply hR0
    exact Polynomial.map_injective _ (shiftHom_injective D c) (by rw [hz, Polynomial.map_zero])
  · intro j i
    simp [AdjoinRoot.liftAlgHom]
    rw [hψ]; exact shiftHom_X D c i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataIterated
section
open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in
theorem derivation_sumAlgEquiv_eq_pderiv {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by
  classical
  have eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a) := fun a => by
    simp [sumAlgEquiv_C_inl]
  have eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t := fun t => by
    simp [sumAlgEquiv_X_inl]
  have eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s) := fun s => by
    simp [sumAlgEquiv_X_inr]
  have hX : ∀ v : τ ⊕ σ,
      d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v)) := by
    intro v
    rcases u with t | s <;> rcases v with t' | s'
    · rw [eL, h1]
      by_cases h : t = t'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]
    · rw [eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]
    · rw [eL, h3, pderiv_X_of_ne (by simp), map_zero]
    · rw [eR, h2]
      by_cases h : s = s'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero,
          map_zero]
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [eC, pderiv_C, map_zero]
    rcases u with t | s
    · rw [h1, pderiv_C]
    · rw [h2, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add (f := _), smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]

theorem exists_generic_jacobian_data_iterated : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  intro Λ _ _ _ _ σ τ _ _ Q _ hQ d h1 h2 h3
  let e := MvPolynomial.sumAlgEquiv Λ τ σ
  have eC : ∀ a : Λ, e (MvPolynomial.C a) = MvPolynomial.C (MvPolynomial.C a) := fun a => by
    simp [e, MvPolynomial.sumAlgEquiv_C_inl]
  obtain ⟨h, f, s, g, hg, hf, hx, hdet⟩ := GlobalTheory.T.exists_local_generators_jacobian_det_not_mem Λ (τ ⊕ σ) (Q.comap e)
    (fun a ha => hQ a (by rw [← eC]; exact ha))
  refine ⟨h, fun j => e (f j), s, e g, hg, hf, fun x hxQ => ?_, ?_⟩
  · have h4 := hx (e.symm x) (by simpa [Ideal.mem_comap] using hxQ)
    have h5 := Ideal.mem_map_of_mem e h4
    rw [Ideal.map_span, ← Set.range_comp, map_mul, AlgEquiv.apply_symm_apply] at h5
    exact h5
  · intro hmem
    apply hdet
    rw [Ideal.mem_comap, AlgEquiv.map_det]
    convert hmem using 2
    ext i j : 1
    exact (derivation_sumAlgEquiv_eq_pderiv d h1 h2 h3 _ _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueSpecCompleteLocalRingThickenings
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LocalThickGlue

theorem subsingleton_primeSpectrum (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)),
      P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) =
        IsLocalRing.maximalIdeal R := by
    intro P
    have hP : (P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1)))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : IsLocalRing.maximalIdeal R ^ (e + 1) ≤
        P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))) := by
      intro r hr
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact P.asIdeal.zero_mem
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hP.ne_top (hP.le_of_pow_le hle)).symm
  constructor
  intro P Q
  ext1
  exact Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ((key P).trans (key Q).symm)

theorem pow_succ_ne_top (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing.maximalIdeal R ^ (e + 1) ≠ ⊤ := fun h =>
  (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))

theorem exists_glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X),
    (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) →
    ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  intro R _ _ hc X x hx
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hc
  haveI hnt : ∀ e, Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top R e)
  haveI hss := subsingleton_primeSpectrum R
  let z : ∀ e, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    (Classical.arbitrary (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))))
  have hpt : ∀ e (a : Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))), x e a = x 0 (z 0) := by
    intro e
    induction e with
    | zero => intro a; rw [Subsingleton.elim (α := PrimeSpectrum _) a (z 0)]
    | succ n ih =>
      intro a
      rw [Subsingleton.elim (α := PrimeSpectrum _) a (Out.thickTrans R (IsLocalRing.maximalIdeal R) n (z n))]
      have e1 := congrArg (fun h => h (z n)) (hx n)
      simp only [Scheme.Hom.comp_apply] at e1
      rw [e1, ih]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x 0 (z 0) ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hr : ∀ e, Set.range (x e) ⊆ Set.range hU'.fromSpec := by
    intro e
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt e a]
    exact hqU
  let ρ : ∀ e, Γ(X, U) ⟶ CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Spec.preimage (IsOpenImmersion.lift hU'.fromSpec (x e) (hr e))
  have hρ : ∀ e, Spec.map (ρ e) ≫ hU'.fromSpec = x e := fun e => by
    simp only [ρ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ e, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))).comp (ρ (e + 1)).hom =
      (ρ e).hom := fun e => by
    have h1 : ρ (e + 1) ≫ CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))) =
        ρ e := by
      apply Spec.map_injective
      rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Category.assoc, hρ, hρ]
      exact hx e
    exact congrArg CommRingCat.Hom.hom h1
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  let F : Γ(X, U) →+* R := IsAdicComplete.StrictMono.liftRingHom (IsLocalRing.maximalIdeal R) ha
    (fun n => (ρ n).hom) (fun {n} => hcomp n)
  refine ⟨Spec.map (CommRingCat.ofHom F) ≫ hU'.fromSpec, fun e => ?_⟩
  have hF : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))).comp F = (ρ e).hom :=
    IsAdicComplete.StrictMono.mk_comp_liftRingHom (IsLocalRing.maximalIdeal R) ha _ _
  rw [← hρ e, ← Category.assoc]
  congr 1
  rw [Out.thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hF]
  rfl

end GlobalTheory.LocalThickGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatible
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (K.sh (K.le_refl k) (a k)) := hG _ _ (ptHom (K.jet k) (K.le_refl k)) rfl
    let j : K.Hom (K.triv k) (K.jet k) :=
      fromTriv (K.jet k) (K.le_refl k) (tszeSec dw)
        (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
        (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
          fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
            simp only [RingHom.comp_apply, sh_refl]
            exact tsze_expand h fun a ↦ dw a h⟩)
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ j rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.AnPer.Charts.exists_cst_of_dw_eq_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (K.sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfFieldPointRelationProper
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FieldPointGraph

theorem epi_spMap {K K' : Type} [Field K] [Field K'] (ι : K →+* K') : Epi (spMap ι) := by
  have : Flat (spMap ι) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := ι.toAlgebra
    exact (inferInstance : Module.Flat K K')
  have : Surjective (spMap ι) := ⟨fun y => ⟨IsLocalRing.closedPoint K', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pt (K : Type) [Field K] : Sp K := IsLocalRing.closedPoint K

theorem eq_pt {K : Type} [Field K] (t : Sp K) : t = pt K := Subsingleton.elim _ _

theorem exists_eq_spMap_comp {X : Scheme.{0}} {K : Type} [Field K] (c : Sp K ⟶ X) {x : X}
    (hx : c (pt K) = x) :
    ∃ ι : X.residueField x →+* K, c = spMap ι ≫ X.fromSpecResidueField x := by
  subst hx
  exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X c).symm⟩

theorem exists_valuationRing_factor {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (φ : R →+* A)
      (ι : FractionRing A →+* K), IsLocalHom φ ∧
        ι.comp ((algebraMap A (FractionRing A)).comp φ) = f := by
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨A, inferInstance, inferInstance, inferInstance, f.codRestrict A.toSubring hA,
    IsFractionRing.lift (A := A) (g := A.subtype) Subtype.val_injective, hl, ?_⟩
  ext a
  exact IsFractionRing.lift_algebraMap (A := A) (g := A.subtype) Subtype.val_injective _

theorem exists_valuationRing_of_specializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A) (u : Sp A ⟶ X)
      (ι : FractionRing A →+* X.residueField x),
      spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ u = X.fromSpecResidueField x ∧
        (spMap (IsLocalRing.residue A) ≫ u) (pt _) = y := by
  obtain ⟨A, _, _, _, φ, ι, hl, hf⟩ := exists_valuationRing_factor
    (X.presheaf.stalkSpecializes h ≫ X.residue x).hom
  refine ⟨A, inferInstance, inferInstance, inferInstance, spMap φ ≫ X.fromSpecStalk y, ι, ?_, ?_⟩
  · have e : spMap ι ≫ spMap (algebraMap A (FractionRing A)) ≫ spMap φ =
        Spec.map (X.presheaf.stalkSpecializes h ≫ X.residue x) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hf]
      rfl
    refine Eq.trans ?_ ((congrArg (· ≫ X.fromSpecStalk y) e).trans ?_)
    · simp only [Category.assoc]
    · rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      rfl
  · have e1 : (spMap (IsLocalRing.residue A)) (pt _) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
    have e2 : (spMap φ) (IsLocalRing.closedPoint A) = IsLocalRing.closedPoint _ :=
      IsLocalRing.comap_closedPoint φ
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1]
    exact (congrArg (X.fromSpecStalk y) e2).trans Scheme.fromSpecStalk_closedPoint

theorem exists_section {W Q : Scheme.{0}} (r : W ⟶ Q) [IsProper r] [IsNoetherian Q]
    [GlobalTheory.IsNormalScheme Q] (G : ∀ (K : Type) [Field K], (Sp K ⟶ W) → Prop)
    (hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! c, G K c ∧ c ≫ r = z)
    (hB : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K c → G K' (spMap ι ≫ c))
    (hV : ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ W),
      G (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) →
      G (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u)) :
    ∃ s : Q ⟶ W, s ≫ r = 𝟙 Q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), G K (z ≫ s) := by

  have hD : ∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (c : Sp K ⟶ W),
      G K' (spMap ι ≫ c) → G K c := by
    intro K K' _ _ ι c hc
    obtain ⟨d, ⟨hd, hdr⟩, -⟩ := hU K (c ≫ r)
    have e : spMap ι ≫ c = spMap ι ≫ d :=
      (hU K' (spMap ι ≫ c ≫ r)).unique ⟨hc, Category.assoc _ _ _⟩
        ⟨hB _ _ ι d hd, by rw [Category.assoc, hdr]⟩
    have := epi_spMap ι
    rwa [(cancel_epi _).mp e]
  let T : Set W := {x | G (W.residueField x) (W.fromSpecResidueField x)}
  have hT : ∀ (K : Type) [Field K] (c : Sp K ⟶ W),
      G K c ↔ c (pt K) ∈ T := by
    intro K _ c
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp c rfl
    exact ⟨fun h => hD _ _ ι _ (hι ▸ h), fun h => by rw [hι]; exact hB _ _ ι _ h⟩
  have hspec : ∀ x y : W, x ⤳ y → x ∈ T → y ∈ T := by
    intro x y h hx
    obtain ⟨A, _, _, _, u, ι, hu, hy⟩ := exists_valuationRing_of_specializes h
    have h1 := hV A u (hD _ _ ι _ (hu ▸ hx))
    rwa [hT, hy] at h1
  choose g hg hg' using fun y : Q => hU (Q.residueField y) (Q.fromSpecResidueField y)
  let γ : Q → W := fun y => g y (pt _)
  have hγT : ∀ y, γ y ∈ T := fun y => (hT _ _).mp (hg y).1
  have hγr : ∀ y, r (γ y) = y := fun y => by
    refine (Scheme.Hom.comp_apply (g y) r _).symm.trans ?_
    rw [(hg y).2]
    exact Scheme.fromSpecResidueField_apply _ _
  have hTγ : ∀ x ∈ T, x = γ (r x) := by
    intro x hx
    have hpt : (W.fromSpecResidueField x ≫ r) (pt (W.residueField x)) =
        r x := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    obtain ⟨ι, hι⟩ := exists_eq_spMap_comp (K := W.residueField x) _ hpt
    have e : W.fromSpecResidueField x = spMap ι ≫ g (r x) :=
      (hU (W.residueField x) (W.fromSpecResidueField x ≫ r)).unique ⟨hx, rfl⟩
        ⟨hB _ _ ι _ (hg _).1, by rw [Category.assoc, (hg _).2, hι]⟩
    have e1 := Scheme.fromSpecResidueField_apply x (pt (W.residueField x))
    refine e1.symm.trans ?_
    rw [e, Scheme.Hom.comp_apply]
    exact congrArg (g (r x)) (eq_pt _)
  have hfin : (γ '' genericPoints Q).Finite :=
    (genericPoints.finite NoetherianSpace.finite_irreducibleComponents).image γ
  have hsub : closure (γ '' genericPoints Q) ⊆ T := by
    intro x hx
    rw [← Set.biUnion_of_singleton (γ '' genericPoints Q), hfin.closure_biUnion] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨_, ⟨y, -, rfl⟩, hx⟩ := hx
    exact hspec _ _ (specializes_iff_mem_closure.mpr hx) (hγT y)
  have hcl : IsClosed T := by
    have hsurj : r '' closure (γ '' genericPoints Q) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← genericPoints.closure (α := Q)]
      refine closure_minimal (fun y hy => ⟨γ y, subset_closure ⟨y, hy, rfl⟩, hγr y⟩)
        (r.isClosedMap _ isClosed_closure)
    have : T = closure (γ '' genericPoints Q) := by
      refine Set.Subset.antisymm (fun x hx => ?_) hsub
      obtain ⟨x', hx', e⟩ : r x ∈ r '' closure (γ '' genericPoints Q) := hsurj ▸ Set.mem_univ _
      rwa [hTγ x hx, ← e, ← hTγ x' (hsub hx')]
    rw [this]
    exact isClosed_closure
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hcl⟩ : Closeds W)
  have hI : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hGI : ∀ (K : Type) [Field K] (c : Sp K ⟶ I.subscheme), G K (c ≫ I.subschemeι) := by
    intro K _ c
    rw [hT, ← hI, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have : IsIso (I.subschemeι ≫ r) := by
    refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance
      (ReducedSubgroup.isReduced_subscheme_vanishingIdeal _) (GlobalTheory.IsNormalScheme.pred _)
      inferInstance fun K _ z => ?_
    obtain ⟨c, ⟨hc, hcr⟩, hu⟩ := hU K z
    have hker : I.subschemeι.ker ≤ c.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      apply ReducedSubgroup.vanishingIdeal_le_ker c ⟨T, hcl⟩
      rintro _ ⟨t, rfl⟩
      rw [eq_pt t]
      exact (hT K c).mp hc
    have hl := IsClosedImmersion.lift_fac I.subschemeι c hker
    refine ⟨IsClosedImmersion.lift I.subschemeι c hker, ?_, fun d hd => ?_⟩
    · show _ ≫ _ ≫ _ = _
      rw [← Category.assoc, hl, hcr]
    · rw [← cancel_mono I.subschemeι, hl]
      exact hu _ ⟨hGI K d, (Category.assoc _ _ _).trans hd⟩
  refine ⟨inv (I.subschemeι ≫ r) ≫ I.subschemeι, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [← Category.assoc]
    exact hGI K _

theorem exists_hom_of_rel : ∀ (Q P S : Scheme.{0}) (q : Q ⟶ S) (p : P ⟶ S) [IsProper p] [IsNoetherian Q] [GlobalTheory.IsNormalScheme Q] (R : ∀ (K : Type) [Field K], (Sp K ⟶ Q) → (Sp K ⟶ P) → Prop), (∀ (K : Type) [Field K] (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → z ≫ q = w ≫ p) → (∀ (K : Type) [Field K] (z : Sp K ⟶ Q), ∃! w, R K z w) → (∀ (K K' : Type) [Field K] [Field K'] (ι : K →+* K') (z : Sp K ⟶ Q) (w : Sp K ⟶ P), R K z w → R K' (spMap ι ≫ z) (spMap ι ≫ w)) → (∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ Q) (v : Sp A ⟶ P), u ≫ q = v ≫ p → R (FractionRing A) (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → R (IsLocalRing.ResidueField A) (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v)) → ∃ h : Q ⟶ P, h ≫ p = q ∧ ∀ (K : Type) [Field K] (z : Sp K ⟶ Q), R K z (z ≫ h) := by
  intro Q P S q p _ _ _ R hC hU hB hV
  obtain ⟨s, hs, hG⟩ := exists_section (pullback.fst q p)
    (fun K _ c => R K (c ≫ pullback.fst q p) (c ≫ pullback.snd q p))
    (fun K _ z => by
      obtain ⟨w, hw, hu⟩ := hU K z
      refine ⟨pullback.lift z w (hC K z w hw), ⟨?_, pullback.lift_fst _ _ _⟩, fun c hc => ?_⟩
      · rwa [pullback.lift_fst, pullback.lift_snd]
      · refine pullback.hom_ext (by rw [pullback.lift_fst, hc.2]) ?_
        rw [pullback.lift_snd]
        exact hu _ (hc.2 ▸ hc.1))
    (fun K K' _ _ ι c hc => by
      rw [Category.assoc, Category.assoc]
      exact hB K K' ι _ _ hc)
    (fun A _ _ _ u hu => by
      rw [Category.assoc, Category.assoc] at hu ⊢
      exact hV A _ _ (by simp [pullback.condition]) hu)
  refine ⟨s ≫ pullback.snd q p, ?_, fun K _ z => ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · have := hG K z
    rwa [Category.assoc, Category.assoc, hs, Category.comp_id] at this

end GlobalTheory.FieldPointGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparableStatement
section
open Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRing_exists_aeval_of_commute_separable : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y T : Matrix (Fin n) (Fin n) R), Y.charpoly.Separable → T * Y = Y * T → ∃ p : R[X], T = aeval Y p := by
  first | exact @GlobalTheory.LocalCommutant.exists_aeval_of_comm | exact GlobalTheory.LocalCommutant.exists_aeval_of_comm | (intros; apply GlobalTheory.LocalCommutant.exists_aeval_of_comm <;> assumption)
end

