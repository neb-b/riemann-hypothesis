module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.AlgSatSum
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem algSat_sum {ι : Type} [Fintype ι] (n q : ℕ) (B : ι → Multiset ℂˣ) :
    algSat n q (∑ i, B i) = ∑ i, algSat n q (B i) := by
  have e : ∀ C : Multiset ℂˣ, algSat n q C =
      C.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun C => by simp [algSat]
  simp only [e]
  exact map_sum (Multiset.mapAddMonoidHom _) B Finset.univ

theorem UpperTheory.V.Cj.noEis :
    UpperTheory.V.Cj.NoEis := by
  intro hJ E _ _ _ a ha ih π σ τ τ' hτ hc m hm ι _ n P μ k1 k2 k3 k4 k5 hw
  have hle : ∀ i t, μ i t ≤ m t := fun i t => by
    rw [← k5 t]
    exact Finset.single_le_sum (f := fun i => μ i t) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  choose Q hQ using fun i => blockConj E a (n i) (ih _ (k2 i) (k3 i)) (P i) (μ i) m (k4 i) (hle i) hm σ.symm
  have s1 : Sep σ.symm τ'.ρ π.finPart := hc.sep.2.trans hτ.sep.2
  have s2 : Sep σ.symm.symm π.finPart τ'.ρ := hτ.sep.1.trans hc.sep.1
  obtain ⟨s, -⟩ := hJ E Unit ι (fun _ => a) n (fun _ => CG.mk π) Q (fun _ => ha) k2 (hw.mono fun w ⟨B, h1, h2⟩ => by
    choose B' b1 b2 using fun i => hQ i w (B i) (h1 i)
    refine ⟨fun _ => ∑ i, B' i, B', fun _ => (CG.hasSat_mk ..).2 ?_, b1, by simp⟩
    refine (s1.comp _).hasSatGL (s2.comp _) h2 ?_
    rw [algSat_sum, algSat_sum, Finset.sum_congr rfl fun i _ => b2 i]
    exact (map_sum (Multiset.mapAddMonoidHom _) _ Finset.univ).symm)
  have := Fintype.card_congr s
  rw [Fintype.card_unit] at this
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelOnto
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relOnto :
    UpperTheory.V.Cj.RelOnto := by
  intro hA E _ _ _ a ha σ Ξ Ξ' h hσ q M hM1 hM2 ω ⟨U, uo, uc, hω⟩ dω rω
  obtain ⟨α, a1, a2, a3, a4⟩ := UpperTheory.V.Lit.Geo.g2 E a ha U uo uc Ξ q ω hω dω rω
  obtain ⟨U', -, uo', uc', β, b1, b2, b3⟩ := hA E a ha U uo uc σ Ξ Ξ' h hσ q α a1 a2 a3
  have bL : Lev Ξ' β := ⟨U', uo', uc', b3.2.1⟩
  obtain ⟨β', hβ', hex⟩ := hM2 β bL b1 b2
  obtain ⟨R1, -, -, R4⟩ := UpperTheory.V.Cj.relFacts E a ha σ Ξ Ξ' h hσ q
  obtain ⟨-, -, L, L1, -⟩ := UpperTheory.V.Cj.levSub E a Ξ q
  obtain ⟨-, -, L', L1', -⟩ := UpperTheory.V.Cj.levSub E a Ξ' q
  obtain ⟨B, B1, -⟩ := UpperTheory.V.Cj.exactSub E a Ξ' q
  have dsub : ∀ (Θ : AlgRep E a) (x y : Co Θ q), dCo (smLie Θ) x = 0 → dCo (smLie Θ) y = 0 →
      dCo (smLie Θ) (x - y) = 0 := fun Θ x y hx hy => by
    have e : x - y = (-1 : ℂ) • y + x := by rw [neg_one_smul ℂ y]; abel
    rw [e, dCo_comb, hx, hy, smul_zero, add_zero]
  have hx : Exact Ξ' (β' - β) := (B1 _).1 (by rw [← neg_sub]; exact B.neg_mem ((B1 _).2 hex))
  have r1 : Rel σ h (ω - α) (β' - β) :=
    R4 _ _ ((L1 _).1 (L.sub_mem ((L1 _).2 ⟨U, uo, uc, hω⟩) ((L1 _).2 ⟨U, uo, uc, a1⟩)))
      ((L1' _).1 (L'.sub_mem ((L1' _).2 (hM1 _ hβ').1) ((L1' _).2 bL)))
      (dsub _ _ _ dω a2) (dsub _ _ _ (hM1 _ hβ').2 b1) ⟨U, uo, uc, a4⟩ hx
  have r2 := R1 1 _ _ _ _ r1 ⟨U', uo', uc', b3⟩
  rw [map_one, one_smul, one_smul, sub_add_cancel, sub_add_cancel] at r2
  exact ⟨β', hβ', r2⟩
end

