module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeCU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.MemOfProdEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumTwoG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0073
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SymOfVieta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.CharpolyRelationUnderComplexEvaluation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExtensionCharacter
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Pa.Lev.LevelRelationOneTwo : Prop :=
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → (∀ j (g : (globOf r V).G₀), T.act1 ((fEl (qj w) (uV A.R) * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (MonoidAlgebra.single g 1 * q1El (ph j) (uV A.R j))) ^ n.factorial) = 0) ∧ ∀ j i (g : (globOf r V).G₀), T.act1 ((fEl (qj w) (uV A.R) * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (MonoidAlgebra.single g 1 * q2El (ph j) (ta j) (uV A.R j) i (yV A.R j i))) ^ n.factorial) = 0
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FFreeCU
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv
private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]
private theorem flag_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (κ : Fin n → ↥H →* kˣ) (g : GL (Fin n) k)
    (hg : ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
      ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)) :
    W.HasFlag ((tw r χ).comp H.subtype) fun i => κ i * χ.comp H.subtype := by
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := (hg s).1 i j hij
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [conj_tw, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 i
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
    exact mul_comm _ _
private theorem pow_fixes (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ (s : G F Ω) (ζ : Ω), ζ ^ M = 1 → (s ^ k) ζ = ζ := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine ((Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet).subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M by omega)] using hζ
  haveI : Finite {ζ : Ω // ζ ^ M = 1} := hfin
  let f : G F Ω →* Equiv.Perm {ζ : Ω // ζ ^ M = 1} :=
    { toFun := fun s => Equiv.Perm.subtypePerm (s : Ω ≃ₐ[F] Ω).toEquiv fun x => by
        change s x ^ M = 1 ↔ x ^ M = 1
        rw [← map_pow, map_eq_one_iff _ (s : Ω ≃ₐ[F] Ω).injective]
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1}), Nat.card_pos, fun s ζ hζ => ?_⟩
  have h1 : f (s ^ Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1})) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg (fun p : Equiv.Perm {ζ : Ω // ζ ^ M = 1} => (p ⟨ζ, hζ⟩ : Ω)) h1
theorem UpperTheory.V.Z.J.free_at_of_unlinked_of_automorphic_cyclotomic_twist :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
        ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (a : ℤ) (M : ℕ) (m : Fin n → ℤ), Continuous r →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw r (cycBar F Ω l ^ a)) → 1 ≤ M → StrictAnti m → Unl l M m r → FreeAt l r := by
  intro P F Ω _ _ _ _ _ _ l _ hl ι n hn r a M m hr haut hM hm hun A' hA'
  obtain ⟨w, hw', hw⟩ := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A' l).2 hA'
  obtain ⟨A, hA, κ, ⟨χ, hk, ⟨g, hg⟩, hκ⟩, hne⟩ := hun w hw
  have hAl : A.valuation (l : Ω) < 1 := (Formalism.VB.Cmp.exists_over_above_iff (K := F) A l).1 ⟨w, hA, hw⟩
  obtain ⟨k, hk0, hkf⟩ := pow_fixes F Ω hM
  have hz : Continuous fun s : G F Ω => ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ F Ω l)
  have hcyc : Continuous fun s : G F Ω => (cycBar F Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : G F Ω => cycBar F Ω l s ^ a := (cont_units _ hcyc).zpow a
  have hc : Continuous (tw r (cycBar F Ω l ^ a)) := by
    refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hr)
  obtain ⟨s, hs1, hs2⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar P F Ω l hl ι n hn _ hc haut A hAl
    (fun i => κ i * (cycBar F Ω l ^ a).comp (Dec (F := F) A).subtype) (fun i => m i + a) k
    (flag_tw r _ _ κ g hg)
    (fun i j hij => by have := hm hij; dsimp only; omega) hk0
    (fun i s hs => by
      show (κ i s * cycBar F Ω l s ^ a * cycBar F Ω l s ^ (-(m i + a))) ^ k = 1
      rw [hκ i s hs, mul_right_comm _ (χ i s), ← zpow_add, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul,
        ← map_pow]
      exact hk i _ (hkf s))
    (by
      intro i j e
      apply hne i j
      rw [mul_right_comm] at e
      exact mul_right_cancel e)
  have hb : cycBar F Ω l s = 1 := by
    simp only [cycBar, MonoidHom.comp_apply, hs1, map_one]
  have hfr : Pr.FreeRatios fun i => κ i s := by
    have e : (fun i => (κ i * (cycBar F Ω l ^ a).comp (Dec (F := F) A).subtype) s) = fun i => κ i s := by
      funext i
      show κ i s * cycBar F Ω l s ^ a = κ i s
      rw [hb, one_zpow, mul_one]
    rwa [e] at hs2
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hw'
  refine ⟨t * s * t⁻¹, ?_, ?_, fun i => κ i s, hfr, ?_⟩
  · rw [mem_Dec, mul_smul, inv_smul_smul, mul_smul, mem_Dec.1 s.2]
  · rw [map_mul, map_mul, hs1, mul_one, map_inv, mul_inv_cancel]
  · have e : r (t * s * t⁻¹) = (r t * g⁻¹) * (g * r s * g⁻¹) * (r t * g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    show (r (t * s * t⁻¹)).val.charpoly = _
    rw [e, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj,
      Matrix.charpoly_of_upperTriangular _ (fun i j hij => (hg s).1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => by rw [(hg s).2 i]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobLG
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
namespace UpperTheory.Gal.projectedFormsSystemPart
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : Plc F} {τ : SmIrr (GLw n w)} {B : Multiset ℂˣ}
theorem frobLG'_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (hc : Continuous r) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (hB : GlobalTheory.LFun.HasSatGL w τ.ρ B)
    (H : Win.LocGlobT ι r w τ) : Af.FrobEig ι r w (Af.algSat n (normV w) B) :=
  _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt P F Ω l ι n r hc w hw τ B hB fun A h rc hrc => (H A h rc hrc).1 hw
end
end UpperTheory.Gal.projectedFormsSystemPart
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.InducedFinalStatement
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.ConjugateSelfDual IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd.S2
section
variable {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R')
private theorem fin_adj (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext a b
  simp only [adj_apply, Matrix.map_apply, map_zsmul]
private theorem fin_conj (X Y : M4 R) : adj (X.map j) * Y.map j * X.map j = (adj X * Y * X).map j := by
  rw [fin_adj, Matrix.map_mul, Matrix.map_mul]
private theorem fin_gsp (hj : Function.Injective j) (ν : R) (X : M4 R) (h : IsGSp (j ν) (X.map j)) : IsGSp ν X := by
  unfold IsGSp at h ⊢
  rw [fin_adj, ← Matrix.map_mul] at h
  ext a b
  apply hj
  have h1 := congrFun (congrFun h a) b
  rw [Matrix.map_apply] at h1
  rw [h1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
  split_ifs <;> simp
private theorem fin_psi {ι Γ : Type} [Group Γ] (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (P.map j).ψ v i s = j (P.ψ v i s) :=
  congrFun (congrFun (fin_conj j (P.n v) (P.r s)) i) i
end
private theorem fin_q (i j : Fin 4) (h : i ≠ j) (h' : wt i j ∉ qQ) : i < j ∨ (i = 2 ∧ j = 1) := by
  revert i j; decide
private theorem fin_v (w : ℤ × ℤ) (h : w ∉ nP) : w ∉ vV := by
  simp only [nP, vV, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  tauto
theorem UpperTheory.induced_final_statement_alt :
    _root_.UpperTheory.V.Sd.S2.Final_s := by
  intro Ω _ _ _ l _ c D T ι P hG hL hS
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  obtain ⟨c₁, h, Q, hQ, hc⟩ := (UpperTheory.automorphic_forms_descent_to_smaller_level l c).2 T.ι (G T.F Ω) P hG.cont hG.int fun v => (hL.low v).2.1
  subst hQ
  have hinj : Function.Injective (algebraMap c₁.O (Qbar l)) := Subtype.val_injective
  have hz : ∀ x : c₁.O, residue c₁.O x = 0 ↔ ‖algebraMap c₁.O (Qbar l) x‖ < 1 := fun x =>
    (residue_eq_zero_iff x).trans ((UpperTheory.automorphic_forms_descent_to_smaller_level l c₁).1 x).2
  have hne : ∀ x : c₁.O, ‖algebraMap c₁.O (Qbar l) x‖ = 1 → residue c₁.O x ≠ 0 := fun x hx h0 =>
    absurd ((hz x).1 h0) (by rw [hx]; exact lt_irrefl _)
  have heq : ∀ x y : c₁.O, ‖algebraMap c₁.O (Qbar l) x - algebraMap c₁.O (Qbar l) y‖ < 1 →
      residue c₁.O x = residue c₁.O y := fun x y hxy => by
    rw [← sub_eq_zero, ← map_sub, hz, map_sub]
    exact hxy
  have h0 : ∀ x : c₁.O, algebraMap c₁.O (Qbar l) x = 0 → x = 0 := fun x hx => hinj (by rw [hx, map_zero])
  have hV : Supp vV (Q.map (residue c₁.O)).r := fun g i j hij hw => (hz _).2 (hG.supp g i j hij hw)
  have hq : ∀ v, SuppM qQ ((Q.map (residue c₁.O)).n v) := fun v i j hij hw => by
    rcases fin_q i j hij hw with hlt | ⟨rfl, rfl⟩
    · refine (hz _).2 ?_
      have h1 : algebraMap c₁.O (Qbar l) (Q.n v i j) = 0 := (hL.low v).1.2.2 i j hlt
      rw [h1, norm_zero]
      exact one_pos
    · exact (hz _).2 (hL.low v).2.2.1
  refine ⟨c₁, h, Q, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hc, ⟨?_, ?_, Or.inl ⟨?_, hq⟩⟩, hS⟩,
    ⟨hV, fun v => ⟨hq v, hne _ (hL.low v).2.2.2⟩⟩, ?_⟩
  · exact fun g => fin_gsp _ hinj _ _ (hG.mult g)
  · intro g hg
    ext i j
    have h1 := congrFun (congrFun (hG.kill g hg) i) j
    have h2 : algebraMap c₁.O (Qbar l) ((1 : M4 c₁.O) i j) = (1 : M4 (Qbar l)) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    exact h1.trans h2.symm
  · exact fun i j hij => h0 _ (hG.nrm hij)
  · intro v
    obtain ⟨a1, a2, a3⟩ := (hL.low v).1
    refine ⟨fin_gsp _ hinj _ _ (by rw [map_one]; exact a1), fun i => hinj (by rw [map_one]; exact a2 i),
      fun i j hij => h0 _ (a3 i j hij)⟩
  · intro v s hs i j hij
    refine h0 _ ?_
    have h1 := hL.flag v s hs i j hij
    exact (congrFun (congrFun (fin_conj (algebraMap c₁.O (Qbar l)) (Q.n v) (Q.r s)) i) j).symm.trans h1
  · intro v s hs i
    refine hinj ?_
    exact ((fin_psi (algebraMap c₁.O (Qbar l)) Q v i s).symm.trans (hL.mu v s hs i)).trans (map_one _).symm
  · exact fun g i => heq _ _ (hG.diag g i)
  · intro v s hs i
    refine (fin_psi (residue c₁.O) Q v i s).trans (heq _ _ ?_)
    have h1 := hL.char v s hs i
    rw [fin_psi (algebraMap c₁.O (Qbar l)) Q v i s] at h1
    exact h1
  · exact fun g i j hij hw => hV g i j hij (fin_v _ hw)
  · rcases hG.ent with ⟨g, hg⟩ | ⟨⟨g, hg⟩, g', hg'⟩
    · exact Or.inl ⟨g, 1, 0, by decide, hne _ hg⟩
    · exact Or.inr ⟨⟨g, 1, 2, by decide, hne _ hg⟩, g', 3, 0, by decide, hne _ hg'⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevSymOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Pa.Lev.symOf_s_ty : Prop :=
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → ∀ j k, k ≤ n → ∀ m : fixd A.ρ (UC n w fun _ => ⊤), (m : A.P) ∈ fixd A.ρ (UK n w) → T.actw (emb ℤ A.R j (MvPolynomial.esymm (Fin n) ℤ k)) m = A.p.D.lam k (MonoidAlgebra.single (ph j) 1) • m
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2BaseEq
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x
private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j := by simp
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e
private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = Hi.unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (Hi.unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e
private theorem push_cont {Γ O T T₀ : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T]
    [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀] (φ : T →ₐ[O] T₀) {f : Γ → T}
    (hf : Alg.AdicCont (maximalIdeal T) f) : Alg.AdicCont (maximalIdeal T₀) fun g => φ (f g) := fun N => by
  have hle : maximalIdeal T ^ N ≤ (maximalIdeal T₀ ^ N).comap (φ : T →+* T₀) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show φ y ∈ maximalIdeal T₀
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (hf N).comp (Ideal.quotientMap _ (φ : T →+* T₀) hle)
private theorem abs_det {n : ℕ} {G G₀ O T T₀ : Type} [Group G] [TopologicalSpace G] [Group G₀] [TopologicalSpace G₀]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (p : G →* G₀) (hp : Continuous p) (D : W.GDet n T G) (D₀ : W.GDet n T₀ G₀)
    (hD : D.IsCont (maximalIdeal T)) (hD₀ : D₀.IsCont (maximalIdeal T₀)) {S : Set G} (hS : Dense S)
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom = D₀.chi (MonoidAlgebra.single (p g) 1)) :
    D.map φ.toRingHom = D₀.comap p := by
  have e : ∀ g, (D.map φ.toRingHom).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom :=
    fun g => by
      rw [← (AlgebraTools.Det.mapApi D _).1]
      simp
  refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
  have h1 := congrFun (cu_ext _ hS (push_cont φ (hD i)) (fun N => (hD₀ i N).comp_continuous hp) fun g hg => by
    simp only [W.GDet.lam, ← h g hg, coeff_map, map_mul, map_pow, map_neg, map_one]
    rfl) g
  simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one] at h1
  simp only [W.GDet.lam, e, LvR.chi_comap, coeff_map]
  exact h1
private theorem abs_chr {n : ℕ} {Wl Dc O T T₀ k : Type} [Group Wl] [Group Dc] [TopologicalSpace Dc] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (inc : Wl →* Dc) (hd : DenseRange inc) (art : Wl →* kˣ) (ha : Function.Surjective art)
    (ψ : Fin n → Dc →* Tˣ) (ψ₀ : Fin n → Dc →* T₀ˣ) (c1 : ∀ i, Alg.AdicCont (maximalIdeal T) fun g => (ψ i g : T))
    (c0 : ∀ i, Alg.AdicCont (maximalIdeal T₀) fun g => (ψ₀ i g : T₀)) (ε : Dc → Tˣ) (ε₀ : Dc → T₀ˣ)
    (hε : ∀ g, φ (ε g) = ε₀ g) (u : Fin n → Uo k → T) (u₀ : Fin n → Uo k → T₀) (hu : ∀ i y, φ (u i y) = u₀ i y)
    (γ : Fin n → T) (γ₀ : Fin n → T₀) (hγ : ∀ i, φ (γ i) = γ₀ i)
    (a1 : ∀ i s (y : Uo k), art s = y → (ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) * u i y = 1)
    (a0 : ∀ i s (y : Uo k), art s = y → (ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) * u₀ i y = 1)
    (b1 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) : T) = γ j)
    (b0 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) : T₀) = γ₀ j) (i : Fin n) :
    W.pushCh φ.toRingHom (ψ i) = ψ₀ i := by
  have hm : ∀ i g, φ ((ψ i g * ε g ^ (i : ℕ) : Tˣ) : T) = ((W.pushCh φ.toRingHom (ψ i) g * ε₀ g ^ (i : ℕ) : T₀ˣ) : T₀) :=
    fun i g => by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hε]
      rfl
  refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (push_cont φ (c1 i)) (c0 i) ?_) g)
  rintro _ ⟨s, rfl⟩
  refine congrArg Units.val (cu_gen art ha ((W.pushCh φ.toRingHom (ψ i)).comp inc) ((ψ₀ i).comp inc)
    (fun s y hy => ?_) (fun s hs => ?_) s)
  · have e := congrArg φ (a1 i s y hy)
    rw [map_mul, hm, hu, map_one] at e
    have e' := a0 i s y hy
    exact mul_right_cancel (inv_injective (Units.ext
      ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
  · refine mul_right_cancel (cu_prod (fun i => W.pushCh φ.toRingHom (ψ i) (inc s) * ε₀ (inc s) ^ (i : ℕ))
      (fun i => ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have e := congrArg φ (b1 j s hs)
    rw [Units.coe_prod, map_prod, hγ] at e
    rw [b0 j s hs, ← e, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (hm i _).symm
private theorem heckePol_map' {T T₀ : Type} [CommRing T] [CommRing T₀] (f : T →+* T₀) (n q : ℕ) (g : ℕ → T) :
    (heckePol n q g).map f = heckePol n q fun j => f (g j) := JEx.heckePol_map _ _ _ _
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2BaseEq_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ → ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → ∀ [Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))] [Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)] [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)] (D₀ : W.GDet n ((hset Q₀ τ₀).TK θ a K₀) V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q₀ τ₀).TK θ a K₀)ˣ), (hset Q₀ τ₀).IsUniv θ a K₀ (maximalIdeal _) D₀ ψ₀ → ∀ (D : W.GDet n ((hset Q τ₀).TK θ' a' K) V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q τ₀).TK θ' a' K)ˣ), (hset Q τ₀).IsUniv θ' a' K (maximalIdeal _) D ψ → ∀ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀, (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) → D.map φ.toRingHom = D₀.comap p ∧ ∀ v i, W.pushCh φ.toRingHom (ψ v i) = ψ₀ v i := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ _ a K₀ K p hp _ hpr j hj hjw θ' a' _ hθ _ _ _ _ _ D₀ ψ₀ hU₀ D ψ hU φ hφ
  have hAx := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  refine ⟨abs_det (φ.restrictScalars c.O) p hp D D₀ hU.cont hU₀.cont hAx.dense ?_, fun v i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    obtain ⟨hw₀, -⟩ := hjw ⟨w, hw⟩ ⟨0, hn⟩
    have e1 := hU.frob ⟨w, hw⟩ B σ hB hσ
    have e0 := hU₀.frob ⟨w, hw₀⟩ B σ hB hσ
    refine ((congrArg (Polynomial.map _) e1).trans ((heckePol_map' _ _ _ _).trans ?_)).trans
      (e0.symm.trans (congrArg (fun g => D₀.chi (MonoidAlgebra.single g 1)) (hpr σ⁻¹).symm))
    refine congrArg (heckePol n (normV w)) (funext fun k => ?_)
    unfold HSet.genW
    split_ifs with h
    · obtain ⟨_, e⟩ := hjw ⟨w, hw⟩ ⟨k - 1, h.2⟩
      exact (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) e)
    · exact map_one _
  · exact abs_chr (k := ((hset Q τ₀).Sl v).adicCompletion L) (φ.restrictScalars c.O) (Subgroup.inclusion (Weil_le_Dec (s.hw v.1))) (UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (s.hw v.1))
      ((hset Q τ₀).art v) (hAx.art_spec v).surj (ψ v) (ψ₀ v) (hU.ψ_cont v) (hU₀.ψ_cont v)
      ((hset Q τ₀).epsV _ v) ((hset Q₀ τ₀).epsV _ v) (fun g => (φ.restrictScalars c.O).commutes _)
      (fun i y => algebraMap A _ (θ' (eV n (hset Q τ₀).Sl v i y))) (fun i y => algebraMap A _ (θ (eV n (hset Q₀ τ₀).Sl v i y)))
      (fun i y => (φ.commutes _).trans (congrArg (fun u : Aˣ => algebraMap A _ (u : A))
        (congrArg (fun t : (hset Q τ₀).X.I.T →* Aˣ => t (eV n (hset Q τ₀).Sl v i y)) hθ)))
      _ _ (fun k => (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) (hj (v, k))))
      (fun i x y h => hU.ψ_unit v i x _ y rfl h) (fun i x y h => hU₀.ψ_unit v i x _ y rfl h)
      (fun k x h => hU.ψ_unif v k x _ rfl h) (fun k x h => hU₀.ψ_unif v k x _ rfl h) i
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularityLinkedEnds
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Th.LevelRelationTwoX : Prop :=
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → ∀ j i, T.act1 (fEl (qj w) (uV A.R) ^ (2 * n.factorial) * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus (2 * n.factorial) (ph j) (ta j) (uV A.R j) i (yV A.R j i))) = 0
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFreeW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
namespace UpperTheory.V.Z.Win.RR
theorem freePUA_alt : _root_.UpperTheory.V.Af.HypothesesH' → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Continuous r → AutP ι r → WitA ι r → Th.Unl l M m r → FreeAt l r :=
  fun P K Ω _ _ _ _ _ _ hK l _ hl ι n hn r M m h1 h2 h3 h4 hW h5 => _root_.UpperTheory.V.Z.Win.RR.freeAt_of_autPA_of_unl_of_finrank_eq_two P K Ω hK l hl ι n hn r M m h1 h2 h3 ⟨h4, fun _ => hW⟩ h5
end UpperTheory.V.Z.Win.RR
end
end

