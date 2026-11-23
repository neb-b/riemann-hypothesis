module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem finsum_match {α β : Type*} (F : α → ℂ) (G : β → ℚ) (Φ : α → β) (P : α → Prop)
    (hF0 : ∀ a, ¬ P a → F a = 0) (hF : ∀ a, P a → F a = G (Φ a))
    (hinj : ∀ a a', P a → P a' → Φ a = Φ a' → a = a') (hsurj : ∀ b, G b ≠ 0 → ∃ a, P a ∧ Φ a = b) :
    ∑ᶠ a, F a = ((∑ᶠ b, G b : ℚ) : ℂ) := by
  have hcast : ((∑ᶠ b, G b : ℚ) : ℂ) = ∑ᶠ b, (G b : ℂ) := by
    by_cases hfin : (Function.support G).Finite
    · simpa using (Rat.castHom ℂ).toAddMonoidHom.map_finsum hfin
    · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support]
      · simp
      · have : Function.support (fun b => (G b : ℂ)) = Function.support G := by
          ext b; simp
        rwa [this]
  have hP : ∀ a, F a ≠ 0 → P a := fun a ha => by by_contra h; exact ha (hF0 a h)
  rw [hcast, ← finsum_mem_support F, ← finsum_mem_support (fun b => (G b : ℂ))]
  apply finsum_mem_eq_of_bijOn Φ
  · refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [Function.mem_support] at ha ⊢
      rwa [hF a (hP a ha)] at ha
    · intro a ha a' ha' h
      exact hinj a a' (hP a ha) (hP a' ha') h
    · intro b hb
      simp only [Function.mem_support, ne_eq, Rat.cast_eq_zero] at hb
      obtain ⟨a, ha, rfl⟩ := hsurj b hb
      refine ⟨a, ?_, rfl⟩
      simp only [Function.mem_support, hF a ha]
      exact_mod_cast hb
  · intro a ha
    exact hF a (hP a ha)

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem ul_mem_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w)
    (g : GLw n w) : g ∈ UL n w ↔ (g.val.map (cj w))ᵀ * g.val = 1 := by
  unfold UL
  rw [if_neg hw]
  change cT (cj w) g.val * 1 * g.val = 1 ↔ _
  rw [Matrix.mul_one]
  rfl

theorem kapOrb_unit_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Monic → Q₂.Monic → Q₁.natDegree + Q₂.natDegree = n → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → ∀ B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → B₁.P = Q₁.map e.symm.toRingHom → B₂.P = Q₂.map e.symm.toRingHom → kapOrb n w Q₁ Q₂ ((KL n w : Set (UL n w)).indicator 1) = (B₁.kapSum B₂ : ℂ) := by
  intro E _ _ _ hU w hw K e he hint hval hq n Q₁ Q₂ hm₁ hm₂ hdeg hsep hc₁ hc₂ B₁ B₂ hu₁ hu₂ hP₁ hP₂
  have hBP : (B₁.prod B₂).P = (Q₁ * Q₂).map e.symm.toRingHom := by
    rw [GlobalTheory.UnitLemma.Orbit.prod_P, hP₁, hP₂, Polynomial.map_mul]
  have hBsep : (B₁.prod B₂).P.Separable := by rw [hBP]; exact hsep.map
  have hBsep' : (B₁.P * B₂.P).Separable := by rw [← GlobalTheory.UnitLemma.Orbit.prod_P]; exact hBsep
  have hBu : (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 := Prod.ext hu₁ hu₂
  have hdim : Module.finrank K.E (B₁.prod B₂).A = n := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E (B₁.prod B₂).g)]
    change (B₁.prod B₂).P.natDegree = n
    rw [hBP, natDegree_map_eq_of_injective e.symm.injective, hm₁.natDegree_mul hm₂, hdeg]
  set B := B₁.prod B₂ with hB
  have hcK : ∀ y, K.c (e.symm y) = e.symm (cj w y) := fun y => by
    apply e.injective
    rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let tr : GLw n w → Matrix (Fin n) (Fin n) K.E := fun γ => γ.val.map e.symm
  have trmul : ∀ a b : GLw n w, tr (a * b) = tr a * tr b := fun a b => by
    ext i j; simp [tr, Matrix.mul_apply, map_sum]
  have trinj : ∀ a b : GLw n w, tr a = tr b → a = b := fun a b h =>
    Units.ext (Matrix.map_injective e.symm.injective h)
  have trU : ∀ γ : UL n w, ((tr γ.1).map K.c)ᵀ * tr γ.1 = 1 := fun γ => by
    have h := (ul_mem_iff hw γ.1).1 γ.2
    have h2 : ((tr γ.1).map K.c)ᵀ = ((γ.1.val.map (cj w))ᵀ).map e.symm := by
      ext i j; simp [tr, hcK]
    rw [h2]
    calc _ = (((γ.1.val.map (cj w))ᵀ * γ.1.val).map e.symm) := by
            ext i j; simp [tr, Matrix.mul_apply, map_sum]
      _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have trcp : ∀ γ : GLw n w, (tr γ).charpoly = γ.val.charpoly.map e.symm.toRingHom := fun γ =>
    Matrix.charpoly_map γ.val e.symm.toRingHom
  have pull : ∀ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 → ∃ g : UL n w, tr g.1 = u := by
    intro u hu
    have h1 : ((u.map e).map (cj w))ᵀ * u.map e = 1 := by
      have h2 : ((u.map e).map (cj w))ᵀ = ((u.map K.c)ᵀ).map e := by
        ext i j; simp [he]
      have h3 := congrArg (fun M => M.map e) hu
      simp only [Matrix.map_one _ (map_zero e) (map_one e)] at h3
      rw [h2, ← h3]
      ext i j; simp [Matrix.mul_apply, map_sum]
    let g : GLw n w := ⟨u.map e, ((u.map e).map (cj w))ᵀ, mul_eq_one_comm.1 h1, h1⟩
    refine ⟨⟨g, (ul_mem_iff hw g).2 h1⟩, ?_⟩
    ext i j; simp [tr, g]
  have hmod : ∀ γ : UL n w, γ.1.val.charpoly = Q₁ * Q₂ →
      ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), IsModel B (tr γ.1) x ψ :=
    fun γ h => _root_.GlobalTheory.InertUnitOrb.exists_isModel_of_unitary K B n (tr γ.1) (trU γ) hBu hBsep (by rw [trcp, h, hBP])
  have clEq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have h1 : ((u⁻¹ : B.Aˣ) : B.A) * (u : B.A) = 1 := Units.inv_mul u
      have h2 : B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by rw [← map_mul, h1, map_one]
      rw [hu]
      linear_combination (-(x.1 : B.A)) * B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) * h1 + (-(x.1 : B.A)) * h2
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]; ring
  have twEq : Equivalence (fun x y : UL n w => ∃ g, y = g⁻¹ * x * (MonoidHom.id (UL n w)) g) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  let Fv : {x : B.Aˣ // B.σ (x : B.A) = x} → ℚ := fun x => K.eta (B₁.gramDet (x.1 : B.A).1) * B.N (x.1 : B.A)
  have Fv_resp : ∀ a b : {x : B.Aˣ // B.σ (x : B.A) = x},
      (∃ u : B.Aˣ, (b.1 : B.A) = a.1 * (u * B.σ (u : B.A))) → Fv a = Fv b := by
    rintro a b ⟨u, hu⟩
    have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B (a.1 : B.A) u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B₁ (a.1 : B.A).1 (Units.map (MonoidHom.fst B₁.A B₂.A) u)).2
    simp only [Fv, hu]
    exact (congrArg₂ (· * ·) e2 e1).symm
  have Fv_out : ∀ a, Fv (Quot.out (Quot.mk _ a : B.Cl)) = Fv a := fun a =>
    Fv_resp _ _ (clEq.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ a : B.Cl))))
  let P : TwCl (MonoidHom.id (UL n w)) → Prop := fun c => c.rep.1.val.charpoly = Q₁ * Q₂
  let Φ : TwCl (MonoidHom.id (UL n w)) → B.Cl := fun c =>
    if h : P c then Quot.mk _ ⟨(hmod c.rep h).choose, (hmod c.rep h).choose_spec.choose_spec.1⟩
    else Quot.mk _ ⟨1, by simp⟩
  unfold kapOrb clSum InvAlg.kapSum
  refine finsum_match _ _ Φ P ?_ ?_ ?_ ?_
  · intro c hc
    exact if_neg hc
  · intro c hc
    have hc' : c.rep ∈ {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} := hc
    rw [if_pos hc']
    obtain ⟨ψ, hψ⟩ := (hmod c.rep hc).choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hc).choose, hψ.1⟩ := dif_pos hc
    rw [hΦ]
    change _ = ((Fv (Quot.out (Quot.mk _ _ : B.Cl)) : ℚ) : ℂ)
    rw [Fv_out]
    beta_reduce
    rw [_root_.GlobalTheory.InertSign.main E hU w hw K e he hval n Q₁ B₁ B₂ hBsep' hP₁ c.rep.1 _ ψ hψ,
      _root_.GlobalTheory.InertUnitOrb.orb_eq_N E hU w hw K e he hint n B hBsep c.rep _ ψ hψ]
    simp only [Fv]
    push_cast
    rfl
  · intro c c' hc hc' h
    obtain ⟨ψ, hψ⟩ := (hmod c.rep hc).choose_spec
    obtain ⟨ψ', hψ'⟩ := (hmod c'.rep hc').choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hc).choose, hψ.1⟩ := dif_pos hc
    have hΦ' : Φ c' = Quot.mk _ ⟨(hmod c'.rep hc').choose, hψ'.1⟩ := dif_pos hc'
    rw [hΦ, hΦ'] at h
    obtain ⟨v, hv⟩ := clEq.eqvGen_iff.1 (Quot.eqvGen_exact h)
    obtain ⟨u, hu, hγu⟩ := GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class K B n _ _ _ _ v ψ ψ' hψ hψ' hv
    obtain ⟨g, rfl⟩ := pull u hu
    have hcomm : c.rep * g = g * c'.rep := by
      apply Subtype.ext
      apply trinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, trmul, trmul]
      exact hγu
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    refine Quot.sound ⟨g, ?_⟩
    change c'.rep = g⁻¹ * c.rep * g
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro k hk
    set a := Quot.out k with ha
    have hk' : Fv a ≠ 0 := hk
    have hN : B.N (a.1 : B.A) ≠ 0 := (mul_ne_zero_iff.1 hk').2
    obtain ⟨γm, ψ, hψ⟩ := _root_.GlobalTheory.InertUnitOrb.ModelOfN.exists_model K B n a.1 hdim a.2 hN
    obtain ⟨hcpm, hunm⟩ := _root_.GlobalTheory.ModelCharpoly.model_charpoly_unitary K B n γm a.1 ψ hψ
    obtain ⟨γ, hγ⟩ := pull γm (hunm hBu)
    have hcpγ : γ.1.val.charpoly = Q₁ * Q₂ := by
      apply Polynomial.map_injective e.symm.toRingHom e.symm.injective
      rw [← trcp, hγ, hcpm, hBP]
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ γ
    obtain ⟨g, hg⟩ := twEq.eqvGen_iff.1
      (Quot.eqvGen_exact (Quot.out_eq c : Quot.mk _ (Quot.out c) = Quot.mk _ γ))
    simp only [MonoidHom.id_apply] at hg
    have hcr : c.rep = g * γ * g⁻¹ := by
      change Quot.out c = g * γ * g⁻¹
      rw [hg]; group
    have hPc : P c := by
      change c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcr]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.coe_units_inv]
      rw [← hcpγ]
      exact Matrix.charpoly_units_conj (g.1) γ.1.val
    refine ⟨c, hPc, ?_⟩
    obtain ⟨ψc, hψc⟩ := (hmod c.rep hPc).choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hPc).choose, hψc.1⟩ := dif_pos hPc
    rw [hΦ]
    have hgu : γ * g⁻¹ = g⁻¹ * c.rep := by rw [hcr]; group
    obtain ⟨v, hv⟩ := _root_.GlobalTheory.InertUnitOrb.class_eq_of_conj K B n γm (tr c.rep.1) (tr (g⁻¹).1) a.1 _ ψ ψc hψ hψc (trU g⁻¹)
      (by rw [← hγ, ← trmul, ← trmul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hgu]) hBsep
    rw [← Quot.out_eq k]
    exact (Quot.sound ⟨v, hv⟩).symm

end GlobalTheory.InertUnitOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertTwUnit

theorem cast_finsum_rat {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h1 : (Function.support f).Infinite := h
    have h2 : (Function.support fun i => (f i : ℂ)).Infinite := by
      have e : (Function.support fun i => (f i : ℂ)) = Function.support f := by
        ext i; simp
      rw [e]; exact h1
    rw [finsum_of_infinite_support h1, finsum_of_infinite_support h2, Rat.cast_zero]

theorem twisted_unit_eq_stSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (a : ℕ) (Q : (w.adicCompletion E)[X]), Q.Monic → Q.natDegree = a → Q.Separable → IsCsr w Q → ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = Q.map e.symm.toRingHom ∧ stTw a w Q ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = (B.stSum : ℂ) := by
  intro E _ _ _ hU w hw K e hc hr hv hq a Q hm hd hs hQ
  unfold stTw IsCsr at *
  unfold clSum
  have hQ' : C ((cj w) (Q.coeff 0)) * Q = (Q.map (cj w)).reverse := hQ.resolve_left hw
  have hcomm : e.symm.toRingHom.comp (cj w) = (K.c : K.E →+* K.E).comp e.symm.toRingHom := by
    ext y
    have h := congrArg e.symm (hc (e.symm y))
    simp only [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h
    simp [h]
  have hrev : ∀ p : (w.adicCompletion E)[X],
      (p.reverse).map e.symm.toRingHom = (p.map e.symm.toRingHom).reverse := by
    intro p
    unfold Polynomial.reverse
    rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective, Polynomial.reflect_map]
  have hPr : C (K.c ((Q.map e.symm.toRingHom).coeff 0)) * Q.map e.symm.toRingHom =
      ((Q.map e.symm.toRingHom).map (K.c : K.E →+* K.E)).reverse := by
    have h1 := congrArg (Polynomial.map e.symm.toRingHom) hQ'
    have h0 : e.symm.toRingHom ((cj w) (Q.coeff 0)) = K.c ((Q.map e.symm.toRingHom).coeff 0) := by
      rw [Polynomial.coeff_map]
      exact RingHom.congr_fun hcomm (Q.coeff 0)
    rw [Polynomial.map_mul, Polynomial.map_C, h0] at h1
    rw [h1, hrev, Polynomial.map_map, hcomm, ← Polynomial.map_map]
  obtain ⟨B, hg, hP⟩ := _root_.GlobalTheory.UnitLemma.exists_invAlg_root K (Q.map e.symm.toRingHom) (hm.map _) hPr
  have hsep : B.P.Separable := by
    rw [hP]
    exact hs.map
  refine ⟨B, hg, hP, ?_⟩
  have hε : (-1 : B.A) ^ (a - 1) = 1 ∨ (-1 : B.A) ^ (a - 1) = -1 := neg_one_pow_eq_or B.A (a - 1)
  obtain ⟨β₀, hβ₀, hX⟩ := _root_.GlobalTheory.UnitLemma.TwistUnitAny.twisted_unit_eq_unit_any K B hg hsep _ hε
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.TwClassForms.twCl_equiv_cl E hU w hw K e hc hr a Q hm hd hs B hg hP β₀ hβ₀
  have hterm : ∀ k : B.Cl, twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (F k).1.rep
      ((GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)).indicator 1) = ((B.N k.rep : ℚ) : ℂ) := by
    intro k
    obtain ⟨b, hb⟩ := hF k
    have hu : B.σ (((Quot.out k).1 : B.Aˣ) : B.A) = ((Quot.out k).1 : B.Aˣ) := (Quot.out k).2
    have hβ : B.σ ((β₀ * (Quot.out k).1 : B.Aˣ) : B.A) =
        (β₀ * (Quot.out k).1 : B.Aˣ) * ((-1) ^ (a - 1) * B.g) := by
      rw [Units.val_mul, map_mul, hβ₀, hu]
      ring
    have h := GlobalTheory.T.twistedOrbitalIntegral_unitGL_eq_hermitianLatticeCount E hU w hw K e hc hr a B hsep (β₀ * (Quot.out k).1) _ hε hβ b (F k).1.rep
      (fun i j => by rw [Units.val_mul]; exact hb i j)
    rw [h, Units.val_mul, hX _ hu]
    rfl
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul]
  simp only [← finsum_eq_if]
  rw [← finsum_subtype_eq_finsum_cond, ← finsum_comp_equiv F]
  simp only [hterm]
  exact (cast_finsum_rat _).symm

end GlobalTheory.InertTwUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPos
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem toReal_mem_psdCone_of_pos_int : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) →
    (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  intro r b hs hp
  refine TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hs) fun y => ?_
  by_cases hy : y = 0
  · subst hy; simp
  · exact (hp y hy).le

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem RatModel.val_prod_zpow : ∀ {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) {K : Type} [Field K] (y : Sp K ⟶ M.Z) (z : M.Z), (∀ w, y w ⤳ z) → ∀ {ι : Type} (s : Finset ι) (f : ι → Ω) (m : ι → ℤ), (∀ i, f i ≠ 0 ∧ f i ∈ M.O z ∧ (f i)⁻¹ ∈ M.O z) → M.val y (∏ i ∈ s, f i ^ m i) = ∏ i ∈ s, M.val y (f i) ^ m i := by
  intro o' Ω _ _ _ M K _ y z h ι s f m hf
  have hmem : ∀ i, f i ^ m i ∈ M.O z := by
    intro i
    rcases Int.eq_nat_or_neg (m i) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast]; exact pow_mem (hf i).2.1 n
    · rw [hn, zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem (hf i).2.2 n
  have hval : ∀ i, M.val y (f i ^ m i) = M.val y (f i) ^ m i := by
    intro i
    have hinv : M.val y (f i)⁻¹ = (M.val y (f i))⁻¹ := by
      have e := RatModel.val_mul h (hf i).2.1 (hf i).2.2
      rw [mul_inv_cancel₀ (hf i).1, RatModel.val_one] at e
      exact (eq_inv_of_mul_eq_one_right e.symm)
    rcases Int.eq_nat_or_neg (m i) with ⟨n, hn | hn⟩
    · rw [hn, zpow_natCast, zpow_natCast]
      exact map_pow (RatModel.valHomOf y z h) ⟨f i, (hf i).2.1⟩ n
    · rw [hn, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow, ← hinv]
      exact map_pow (RatModel.valHomOf y z h) ⟨(f i)⁻¹, (hf i).2.2⟩ n
  have e := map_prod (RatModel.valHomOf y z h) (fun i => (⟨f i ^ m i, hmem i⟩ : M.O z)) s
  have hc : (↑(∏ i ∈ s, (⟨f i ^ m i, hmem i⟩ : M.O z)) : Ω) = ∏ i ∈ s, f i ^ m i := by
    exact map_prod (M.O z).subtype _ s
  rw [RatModel.valHomOf_apply, hc] at e
  rw [e]
  exact Finset.prod_congr rfl fun i _ => by rw [RatModel.valHomOf_apply]; exact hval i

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldEvalOriginEqTangentDerivativStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)), evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) = tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  first | exact @GlobalTheory.CoordsOrigin.evO_germ_of_isInv | exact GlobalTheory.CoordsOrigin.evO_germ_of_isInv | (intros; apply GlobalTheory.CoordsOrigin.evO_germ_of_isInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left], IsAbelianScheme A → ∀ (N : LB (A ⊗ T).left) (hN : N.IsLB), Triv (ev N (1 : T ⟶ A) (𝟙 T)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ T), IsAdditive (ev N (fst A (Over.mk s)) (snd A (Over.mk s) ≫ t))) → IsAdditive N := by
  first | exact @GlobalTheory.AddFib.isAdditive_of_geomFibres | exact GlobalTheory.AddFib.isAdditive_of_geomFibres | (intros; apply GlobalTheory.AddFib.isAdditive_of_geomFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionFibreOverPointToBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem isClosedImmersion_kerι : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T), IsClosedImmersion h.left → IsClosedImmersion (GlobalTheory.TwistFlat.kerι A φ h).left := by
  intro R _ A T V _ φ H h hh
  have hP : IsPullback (fst A T).left (snd A T).left A.hom T.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom T.hom
  have w : pullback.fst A.hom (φ ≫ T.hom) ≫ A.hom = (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) ≫ T.hom := by
    rw [Category.assoc]; exact pullback.condition
  let g : pullback A.hom (φ ≫ T.hom) ⟶ (A ⊗ T).left :=
    hP.lift (pullback.fst A.hom (φ ≫ T.hom)) (pullback.snd A.hom (φ ≫ T.hom) ≫ φ) w
  have hg1 : g ≫ (fst A T).left = pullback.fst A.hom (φ ≫ T.hom) := hP.lift_fst _ _ _
  have hg2 : g ≫ (snd A T).left = pullback.snd A.hom (φ ≫ T.hom) ≫ φ := hP.lift_snd _ _ _
  have ht : IsPullback g (pullback.snd A.hom (φ ≫ T.hom)) (snd A T).left φ := by
    refine IsPullback.of_right (h₁₂ := (fst A T).left) (h₂₂ := T.hom) ?_ hg2 hP
    rw [hg1]
    exact IsPullback.of_hasPullback A.hom (φ ≫ T.hom)
  have hs : IsPullback (pullback.fst (h ≫ snd A T).left φ)
      ((kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)) (h.left ≫ (snd A T).left) φ := by
    have e1 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom) = pullback.snd (h ≫ snd A T).left φ :=
      pullback.lift_snd _ _ _
    rw [e1, ← Over.comp_left]
    exact IsPullback.of_hasPullback _ _
  have hsq : pullback.fst (h ≫ snd A T).left φ ≫ h.left = (kerι A φ h).left ≫ g := by
    apply hP.hom_ext
    · rw [Category.assoc, Category.assoc, hg1]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Category.assoc, hg2, ← Over.comp_left, pullback.condition]
      exact congrArg (· ≫ φ) (pullback.lift_snd _ _ _).symm
  have hpb : IsPullback (pullback.fst (h ≫ snd A T).left φ) (kerι A φ h).left h.left g :=
    IsPullback.of_bot hs hsq ht
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb hh

end GlobalTheory.TwistFlat
end

