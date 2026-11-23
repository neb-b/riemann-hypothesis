module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0612
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassFirst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0588
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DvdOfPhiEqZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ExistsPolyOfCommute

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.FiniteRefSign
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace PositivityTheory.BCUSide.HermitianLocalForms.Lem

theorem ratio_poly : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := GlobalTheory.T.hermitian_form_polynomial_in

theorem sign_rel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ (m : (w.adicCompletion E)[X]) (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → sgnOn (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) = ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x) : ℤ) : ℂ) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) := _root_.GlobalTheory.CompanionTheory.LocalSignInert.main

theorem exists_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := _root_.GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus

theorem norms_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := _root_.GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi

theorem exists_crt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := _root_.GlobalTheory.CompanionTheory.EllCRT.main

theorem herm_of_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := _root_.GlobalTheory.CompanionTheory.HermFixed.main

theorem posDef_of_inf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := _root_.GlobalTheory.CompanionTheory.PosDefNorm.main

theorem norm_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] (r : ℕ) (Q : SelfRecip E r) (x : (k ⊗[(maximalRealSubfield E)] plus Q)ˣ), x ∈ norms Q k → Units.map (Algebra.norm k : k ⊗[(maximalRealSubfield E)] plus Q →* k) x ∈ GlobalTheory.QuadSymbol.normGroup (maximalRealSubfield E) E k := _root_.GlobalTheory.CompanionTheory.NormClassNorm.norm_mem_normGroup

theorem finite_ref_sign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E) (H₀ : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ P₁ : E[X], {w : Pl E | ¬ IsSplitAt w ∧ sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E))) ≠ 1}.Finite := _root_.GlobalTheory.CompanionTheory.FinSign.main

theorem local_assembly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (t : E[X]), (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ z : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)ˣ, locPhi hU w hw v hv Q m * ((z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q (v.adicCompletion (maximalRealSubfield E)) (z : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] Fld Q)) = locPhi hU w hw v hv Q (atPl w t)) → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val ∧ (H₀ * aeval γ₀.val t).map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) * c.val := by
  intro E _ _ _ hU w hw v hv n γ₀ hP H₀ _ _ h3 m t hz
  exact GlobalTheory.CompanionTheory.LocAssembly.assembly (locJ hU w hw v hv) (locJ_algebraMap hU w hw v hv) (cj w)
    (locJ_cj hU w hw v hv) γ₀ hP H₀ h3 m t hz

end PositivityTheory.BCUSide.HermitianLocalForms.Lem
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.LatticeStep
section
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem lattice_step {n : ℕ} (γ γi : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X])
    (hγ : ∀ i j, γ i j ∈ intL L) (hγi : ∀ i j, γi i j ∈ intL L) (hγγ : γ * γi = 1)
    (hch : γ.charpoly = Q₀.map (intL L).subtype) (hsep : Q₀.Separable) (k : GL (Fin n) L)
    (hk : ∀ i j, ((k⁻¹ : GL (Fin n) L).val * γ * k.val) i j ∈ intL L)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin n) L).val * γi * k.val) i j ∈ intL L) :
    ∃ a g : GL (Fin n) L, a.val * γ = γ * a.val ∧ k = a * g ∧ (∀ i j, g.val i j ∈ intL L) ∧
      (∀ i j, (g⁻¹ : GL (Fin n) L).val i j ∈ intL L) := by
  set f : intL L →+* L := (intL L).subtype with hf
  have finj : Function.Injective f := Subtype.val_injective
  set γ' : Matrix (Fin n) (Fin n) L := (k⁻¹ : GL (Fin n) L).val * γ * k.val with hγ'
  let γ₀ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨γ i j, hγ i j⟩
  let γ₁ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨γ' i j, hk i j⟩
  have e₀ : γ₀.map f = γ := by
    ext i j
    rfl
  have e₁ : γ₁.map f = γ' := by
    ext i j
    rfl
  have cγ' : γ'.charpoly = γ.charpoly := by
    rw [hγ', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have c₀ : γ₀.charpoly = Q₀ := by
    apply Polynomial.map_injective f finj
    rw [← Matrix.charpoly_map, e₀, hch]
  have c₁ : γ₁.charpoly = Q₀ := by
    apply Polynomial.map_injective f finj
    rw [← Matrix.charpoly_map, e₁, cγ', hch]
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic γ₀ (c₀ ▸ hsep)
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic γ₁ (c₁ ▸ hsep)
  set u₀ := hv₀.unit
  set u₁ := hv₁.unit
  set C := GlobalTheory.Orb.companionMat n Q₀
  have h₀ : γ₀ * (u₀ : Matrix (Fin n) (Fin n) (intL L)) = u₀ * C := by
    have := GlobalTheory.Orb.mul_krylov_eq γ₀ v₀
    rw [c₀] at this
    simpa [u₀] using this
  have h₁ : γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) = u₁ * C := by
    have := GlobalTheory.Orb.mul_krylov_eq γ₁ v₁
    rw [c₁] at this
    simpa [u₁] using this
  set u := u₀ * u₁⁻¹
  have hu : γ₀ * (u : Matrix (Fin n) (Fin n) (intL L)) = u * γ₁ := by
    have e : ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) := by
      calc ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁
          = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * (γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))) := by rw [Units.mul_inv_cancel_right]
        _ = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * ((u₁ : Matrix (Fin n) (Fin n) (intL L)) * C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))) := by rw [h₁]
        _ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [Units.val_mul, ← Matrix.mul_assoc, h₀, Matrix.mul_assoc, Matrix.mul_assoc, e]
  set F : Matrix (Fin n) (Fin n) (intL L) →* Matrix (Fin n) (Fin n) L := (f.mapMatrix : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L).toMonoidHom
  set g : GL (Fin n) L := Units.map F u
  have hgval : g.val = (u : Matrix (Fin n) (Fin n) (intL L)).map f := rfl
  have hginv : (g⁻¹ : GL (Fin n) L).val = ((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)).map f := rfl
  have hgg : γ * g.val = g.val * γ' := by
    rw [hgval, ← e₀, ← e₁, ← Matrix.map_mul, ← Matrix.map_mul, hu]
  have hgi : (g⁻¹ : GL (Fin n) L).val * γ = γ' * (g⁻¹ : GL (Fin n) L).val := by
    calc (g⁻¹ : GL (Fin n) L).val * γ
        = (g⁻¹ : GL (Fin n) L).val * (γ * g.val * (g⁻¹ : GL (Fin n) L).val) := by rw [Units.mul_inv_cancel_right]
      _ = (g⁻¹ : GL (Fin n) L).val * (g.val * γ' * (g⁻¹ : GL (Fin n) L).val) := by rw [hgg]
      _ = γ' * (g⁻¹ : GL (Fin n) L).val := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨k * g⁻¹, g, ?_, by group, fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_assoc, hgi, hγ']
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  · rw [hgval]
    exact ((u : Matrix (Fin n) (Fin n) (intL L)) i j).2
  · rw [hginv]
    exact (((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) i j).2

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.NormStep
section
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem norm_step [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) {n : ℕ}
    (γ J Ji Hn Hi : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X])
    (hγ : ∀ i j, γ i j ∈ intL L) (hJ : ∀ i j, J i j ∈ intL L) (hJi : ∀ i j, Ji i j ∈ intL L)
    (hH : ∀ i j, Hn i j ∈ intL L) (hHi : ∀ i j, Hi i j ∈ intL L)
    (hJJ : J * Ji = 1) (hHH : Hn * Hi = 1) (hJh : cT σ J = J) (hHh : cT σ Hn = Hn)
    (hγJ : cT σ γ * J * γ = J) (hγH : cT σ γ * Hn * γ = Hn)
    (hch : γ.charpoly = Q₀.map (intL L).subtype) (hsep : Q₀.Separable) :
    ∃ b : GL (Fin n) L, b.val * γ = γ * b.val ∧ cT σ b.val * J * b.val = Hn := by
  set sO := GlobalTheory.NormEq.sigO σ h.2.1 with hsO
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  let γO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨γ i j, hγ i j⟩
  let JO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨J i j, hJ i j⟩
  let JiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Ji i j, hJi i j⟩
  let HO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Hn i j, hH i j⟩
  let HiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Hi i j, hHi i j⟩
  have eγ : Φ γO = γ := rfl
  have eJ : Φ JO = J := rfl
  have eJi : Φ JiO = Ji := rfl
  have eH : Φ HO = Hn := rfl
  have eHi : Φ HiO = Hi := rfl
  have hJJO : JO * JiO = 1 := hΦinj (by rw [map_mul, map_one, eJ, eJi, hJJ])
  have hJJO' : JiO * JO = 1 := mul_eq_one_comm.1 hJJO
  have hHHO : HO * HiO = 1 := hΦinj (by rw [map_mul, map_one, eH, eHi, hHH])
  have hHHO' : HiO * HO = 1 := mul_eq_one_comm.1 hHHO
  have hγJO : cT sO γO * JO * γO = JO := hΦinj (by rw [map_mul, map_mul, hΦcT, eγ, eJ, hγJ])
  have hγHO : cT sO γO * HO * γO = HO := hΦinj (by rw [map_mul, map_mul, hΦcT, eγ, eH, hγH])
  have hJhO : cT sO JO = JO := hΦinj (by rw [hΦcT, eJ, hJh])
  have hHhO : cT sO HO = HO := hΦinj (by rw [hΦcT, eH, hHh])
  have hchO : γO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← eγ]
    exact (Matrix.charpoly_map γO (intL L).subtype).symm
  have hsepO : γO.charpoly.Separable := hchO ▸ hsep
  have hcsr : GlobalTheory.UTr.IsCsr sO Q₀ := hchO ▸ isCsr_charpoly sO γO JO JiO hJJO' hγJO
  let P : GlobalTheory.UTr.Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval γO P.1 = 0 := by
    show aeval γO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly γO
  let ev := GlobalTheory.UTr.evalMat P γO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (GlobalTheory.UTr.root P) r) = aeval γO r := fun r => by
    rw [← aeval_algHom_apply, GlobalTheory.UTr.evalMat_root]
  have hevinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun z hz => ?_
    obtain ⟨r, rfl⟩ := GlobalTheory.UTr.exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n γO r hsepO hz
    rw [hchO] at hd
    exact (GlobalTheory.UTr.aeval_root_eq_zero_iff P).2 hd

  let γiO := JiO * cT sO γO * JO
  have hγi : γiO * γO = 1 := by
    show JiO * cT sO γO * JO * γO = 1
    rw [Matrix.mul_assoc JiO, Matrix.mul_assoc JiO, hγJO, hJJO']
  let gU : UJ sO JO := ⟨⟨γO, γiO, mul_eq_one_comm.1 hγi, hγi⟩, hγJO⟩
  have hcT : ∀ z, cT sO (ev z) * JO = JO * ev (GlobalTheory.UTr.conj P z) := fun z => GlobalTheory.UTr.cT_evalMat P gU hg z

  have hxc : (JiO * HO) * γO = γO * (JiO * HO) := by
    have hA : cT sO γO * (JO * γO * JiO) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγJO, hJJO]
    have hA' : (JO * γO * JiO) * cT sO γO = 1 := mul_eq_one_comm.1 hA
    calc JiO * HO * γO = JiO * ((JO * γO * JiO) * cT sO γO) * HO * γO := by rw [hA', Matrix.mul_one]
      _ = γO * JiO * (cT sO γO * HO * γO) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc JiO JO, hJJO', Matrix.one_mul]
      _ = γO * (JiO * HO) := by rw [hγHO, Matrix.mul_assoc]
  obtain ⟨p, hp⟩ := exists_poly_of_commute γO (JiO * HO) hsepO hxc
  let tz : GlobalTheory.UTr.Alg P := aeval (GlobalTheory.UTr.root P) p
  have htO : ev tz = JiO * HO := by rw [hev, ← hp]

  let tiO := HiO * JO
  have htiO : (JiO * HO) * tiO = 1 := by
    show JiO * HO * (HiO * JO) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc HO, hHHO, Matrix.one_mul, hJJO']
  have hdet : IsUnit (ev tz).det := by
    rw [htO]
    exact isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz (ev tz).charpoly = 0 := hevinj (by
      rw [← aeval_algHom_apply, map_zero]; exact Matrix.aeval_self_charpoly (ev tz))
    have hc0 : IsUnit ((ev tz).charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff (ev tz)
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add (ev tz).charpoly)
    rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz (ev tz).charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (GlobalTheory.UTr.Alg P)ˣ := hunit.unit

  have hcTJi : cT sO JiO = JiO := by
    have h1 : cT sO JiO * JO = 1 := by
      rw [← hJhO, ← cT_mul, hJJO, cT_one]
    calc cT sO JiO = cT sO JiO * (JO * JiO) := by rw [hJJO, Matrix.mul_one]
      _ = JiO := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hconj : GlobalTheory.UTr.conj P tz = tz := by
    apply hevinj
    have h1 : JO * ev (GlobalTheory.UTr.conj P tz) = JO * ev tz := by
      rw [← hcT, htO, cT_mul, hHhO, hcTJi, Matrix.mul_assoc, hJJO', Matrix.mul_one, ← Matrix.mul_assoc, hJJO,
        Matrix.one_mul]
    have h2 := congrArg (JiO * ·) h1
    simpa only [← Matrix.mul_assoc, hJJO', Matrix.one_mul] using h2
  have hT : T ∈ GlobalTheory.UTr.plus P := (GlobalTheory.UTr.mem_plus (P := P)).2 (by rw [IsUnit.unit_spec]; exact hconj)
  have hsepP : (P : (intL L)[X]).Separable := hsep
  obtain ⟨u, hu⟩ := GlobalTheory.NormEq.normU_surj L σ ϖ q h P hsepP T hT
  have hu' : (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u = tz := by
    have := congrArg (fun z : (GlobalTheory.UTr.Alg P)ˣ => (z : GlobalTheory.UTr.Alg P)) hu
    simpa [GlobalTheory.UTr.normU, T] using this
  let Ψ : GlobalTheory.UTr.Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : GlobalTheory.UTr.Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * γ = γ * Φ (ev u)
    rw [← eγ, ← map_mul, ← map_mul]
    congr 1
    rw [← GlobalTheory.UTr.evalMat_root P γO hg, ← map_mul, ← map_mul, mul_comm]
  · show cT σ (Φ (ev u)) * J * Φ (ev u) = Hn
    rw [← hΦcT, ← eJ, ← map_mul, ← map_mul, hcT, Matrix.mul_assoc, ← map_mul, mul_comm (GlobalTheory.UTr.conj P _), hu',
      htO, ← Matrix.mul_assoc, hJJO, Matrix.one_mul, eH]

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
end
end

