module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelKer

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.BlockConj
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a)
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem algSat_shift {E : Type} [Field E] [NumberField E] (a n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    {χ : HChar E} (hχ : χ.IsAbsPow (((n : ℝ) - a) / 2)) (B : Multiset ℂˣ) :
    algSat n (Formalism.ConjugateSelfDual.normV w) (B.map (· * χ.val w)) = algSat a (Formalism.ConjugateSelfDual.normV w) B := by
  have h := hχ.2.1 w
  have hq : (0 : ℝ) < (Formalism.ConjugateSelfDual.normV w : ℕ) := by
    have he : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    rw [he]
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [algSat_eq, algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  rw [h]
  have e : Ideal.absNorm w.asIdeal = Formalism.ConjugateSelfDual.normV w := by
    first | rfl | exact Ideal.absNorm_apply _ | simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have e2 : ((a : ℝ) - 1) / 2 = ((n : ℝ) - 1) / 2 + -(((n : ℝ) - a) / 2) := by ring
  rw [e, e2, Real.rpow_add hq, Complex.ofReal_mul, Complex.ofReal_cpow hq.le (-_), Complex.ofReal_neg,
    Complex.ofReal_natCast]
  ring

theorem UpperTheory.V.Cj.blockConj :
    UpperTheory.V.Cj.BlockConj := by
  intro E _ _ _ a n hC π μ m h1 h2 h3 σ
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((n : ℝ) - a) / 2)
  have hν' := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((a : ℝ) - n) / 2)
  obtain ⟨π', hπ'⟩ := satConj E n hC _ (twReg E a n π μ m h1 h2 h3 _ hν) σ
  refine ⟨π'.twist (GlobalTheory.HeckeGal.Model.absPow E (((a : ℝ) - n) / 2)), fun w B hB => ?_⟩
  obtain ⟨B', b1, b2⟩ := hπ' w _ (sat_twist π hB (hν.1 w))
  refine ⟨_, sat_twist π' b1 (hν'.1 w), ?_⟩
  rw [algSat_shift n a w hν', b2, algSat_shift a n w hν]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelFacts
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem oc_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U U' : Subgroup G}
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (h3 : IsOpen (U' : Set G)) :
    IsOpen ((U ⊓ U' : Subgroup G) : Set G) ∧ IsCompact ((U ⊓ U' : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  exact ⟨h1.inter h3, h2.inter_right (U'.isClosed_of_isOpen h3)⟩

private theorem oc_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U : Subgroup G}
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (x : G) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ IsCompact (U' : Set G) ∧ ∀ u ∈ U', x⁻¹ * u * x ∈ U := by
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩
  · have : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun u => x⁻¹ * u * x) ⁻¹' U := by
      ext u; simp
    rw [this]
    exact h1.preimage (by fun_prop)
  · have : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun u => x * u * x⁻¹) '' U := by
      ext u
      constructor
      · intro hu
        exact ⟨x⁻¹ * u * x, by simpa using hu, by group⟩
      · rintro ⟨v, hv, rfl⟩
        simpa [mul_assoc] using hv
    rw [this]
    exact h2.image (by fun_prop)

theorem UpperTheory.V.Cj.relFacts :
    UpperTheory.V.Cj.RelFacts := by
  intro E _ _ _ a ha σ Ξ Ξ' h hσ q
  have mono : ∀ U U' : Subgroup (GL (Fin a) (Af E)), U' ≤ U → ∀ (α : Co Ξ q) (β : Co Ξ' q),
      RelAt U σ h α β → RelAt U' σ h α β := fun U U' hU α β hr => by
    have := relPull E a U U' 1 (fun u hu => by simpa using hU hu) σ Ξ Ξ' h q α β hr
    rwa [trans_one, trans_one] at this
  have L := (levSub E a Ξ q).2.1
  have L' := (levSub E a Ξ' q).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro s α α' β β' ⟨U, u1, u2, u3⟩ ⟨V, v1, -, v3⟩
    obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
    exact ⟨U ⊓ V, w1, w2, relLin E a _ σ Ξ Ξ' h q s α α' β β' (mono _ _ inf_le_left _ _ u3) (mono _ _ inf_le_right _ _ v3)⟩
  · rintro x α β ⟨U, u1, u2, u3⟩
    obtain ⟨V, v1, v2, v3⟩ := oc_conj u1 u2 x
    exact ⟨V, v1, v2, relPull E a U V x v3 σ Ξ Ξ' h q α β u3⟩
  · rintro α β ⟨U, u1, u2, u3⟩
    constructor
    · rintro ⟨V, v1, -, v3⟩
      obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
      exact ⟨U ⊓ V, w1, w2, ((relKer E a ha _ w2 σ Ξ Ξ' h hσ q α β).1 (mono _ _ inf_le_left _ _ u3)).1
        ((L _ _ inf_le_right α).2 v3)⟩
    · rintro ⟨V, v1, -, v3⟩
      obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
      exact ⟨U ⊓ V, w1, w2, ((relKer E a ha _ w2 σ Ξ Ξ' h hσ q α β).1 (mono _ _ inf_le_left _ _ u3)).2
        ((L' _ _ inf_le_right β).2 v3)⟩
  · rintro α β ⟨U, u1, u2, u3⟩ ⟨V, v1, -, v3⟩ d1 d2 ⟨X, x1, -, x3⟩ ⟨Y, y1, -, y3⟩
    obtain ⟨w1, w2⟩ := oc_inf u1 u2 v1
    obtain ⟨w3, w4⟩ := oc_inf w1 w2 x1
    obtain ⟨w5, w6⟩ := oc_inf w3 w4 y1
    exact ⟨_, w5, w6, (relKer E a ha _ w6 σ Ξ Ξ' h hσ q α β).2
      ((L _ _ (inf_le_left.trans (inf_le_left.trans inf_le_left)) α).1 u3)
      ((L' _ _ (inf_le_left.trans (inf_le_left.trans inf_le_right)) β).1 v3) d1 d2
      ((L _ _ (inf_le_left.trans inf_le_right) α).2 x3) ((L' _ _ inf_le_right β).2 y3)⟩
end

