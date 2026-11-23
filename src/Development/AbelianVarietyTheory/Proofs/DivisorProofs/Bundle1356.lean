module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpaceStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (β ⊕ β) (β ⊕ β) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((g : GL β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w := by
  first | exact @GlobalTheory.RealLift.Compare.constant_eq_dbl | exact GlobalTheory.RealLift.Compare.constant_eq_dbl | (intros; apply GlobalTheory.RealLift.Compare.constant_eq_dbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexPrincipalCongruenceNeZero
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKDef.Regroup.regroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 :=
  GlobalTheory.LKDef.Regroup.regroup_main GlobalTheory.LKDef.DFormPos.sim_pos _root_.GlobalTheory.LKDef.FinPairs.finite_classes_irr_term_ne_zero _root_.GlobalTheory.LKDef.TermPair.term_eq_centSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantDerivativeNeZero
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.PencilDisc

theorem resultant_derivative_ne_zero : ∀ (σ F : Type) [Fintype σ] [Field F] [CharZero F] (p : Polynomial (MvPolynomial σ F)) (δ : ℕ), 1 ≤ δ → p.natDegree = δ → Irreducible p → Polynomial.resultant p (Polynomial.derivative p) δ (δ - 1) ≠ 0 := by
  intro σ F _ _ _ p δ hδ hp hirr
  let K := FractionRing (MvPolynomial σ F)
  have hinj : Function.Injective (algebraMap (MvPolynomial σ F) K) := IsFractionRing.injective _ _
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hprim : p.IsPrimitive := hirr.isPrimitive (by omega)
  have h1 : Irreducible (p.map (algebraMap _ K)) := hprim.irreducible_iff_irreducible_map_fraction_map.1 hirr
  have h2 := Polynomial.resultant_ne_zero _ _ h1.separable
  rw [Polynomial.natDegree_derivative, Polynomial.natDegree_map_eq_of_injective hinj, hp, Polynomial.derivative_map,
    Polynomial.resultant_map_map] at h2
  intro h
  exact h2 (by rw [h, map_zero])

theorem exists_specialise_ne_zero : ∀ (F S T : Type) [Field F] [Infinite F] (R : MvPolynomial (S ⊕ T) F), R ≠ 0 → ∃ v : T → F, MvPolynomial.aeval (Sum.elim (fun i => (MvPolynomial.X i : MvPolynomial S F)) fun k => MvPolynomial.C (v k)) R ≠ 0 := by
  intro F S T _ _ R hR
  have h1 : sumAlgEquiv F S T R ≠ 0 := (map_ne_zero_iff _ (sumAlgEquiv F S T).injective).2 hR
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 h1
  obtain ⟨v, hv⟩ : ∃ v : T → F, eval v (AddMonoidAlgebra.coeff (sumAlgEquiv F S T R) m) ≠ 0 := by
    by_contra! H
    exact hm (MvPolynomial.funext fun x => by simpa using H x)
  refine ⟨v, fun h => hv ?_⟩
  have key : ∀ P : MvPolynomial (S ⊕ T) F,
      aeval (Sum.elim (fun i => (X i : MvPolynomial S F)) fun k => C (v k)) P = MvPolynomial.map (eval v) (sumAlgEquiv F S T P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases i <;> simp
  rw [← coeff_map, ← key, h]
  simp

theorem irreducible_of_map {F L : Type} [Field F] [Field L] [Algebra F L] {σ : Type} (f : MvPolynomial σ F)
    (h : Irreducible (MvPolynomial.map (algebraMap F L) f)) : Irreducible f := by
  have hinj := (algebraMap F L).injective
  haveI : IsLocalHom (MvPolynomial.map (σ := σ) (algebraMap F L)) := ⟨fun g hg => by
    obtain ⟨c, hc, e⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hg
    have hc0 : algebraMap F L (AddMonoidAlgebra.coeff g 0) = c := by
      rw [← coeff_map, e, coeff_zero_C]
    refine MvPolynomial.isUnit_iff_eq_C_of_isReduced.2 ⟨AddMonoidAlgebra.coeff g 0, ?_, ?_⟩
    · refine isUnit_iff_ne_zero.2 fun h0 => hc.ne_zero ?_
      rw [← hc0, h0, map_zero]
    · apply MvPolynomial.map_injective _ hinj
      rw [e, map_C, hc0]⟩
  exact Irreducible.of_map h

theorem exists_poly_noSquare : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), 1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ 2 * D * δ ^ 2 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K), aeval (fun p : Fin D × Fin N => s p.1 p.2) Q ≠ 0 → NoSquare (spec s f) := by
  intro F _ _ D N δ f hδ hf hirr
  have hF : Irreducible f := irreducible_of_map f hirr
  let u : Fin D → Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun i j => X (Sum.inl (i, j))
  let a : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inl j))
  let b : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inr j))
  have hc := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F _ D N δ f hf u a b
  let g : Fin (D + 1) × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun p =>
    Fin.lastCases (motive := fun _ => (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Sum.inr (Sum.inr p.2)) (fun i => Sum.inl (i, p.2)) p.1
  have hg : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    induction i using Fin.lastCases <;> induction i' using Fin.lastCases <;> simp_all [g]
  have hjoin : join u b = fun p => X (g p) := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, g, u, b]
  have hlead : (line u a b f).coeff δ ≠ 0 := by
    rw [hc.2, hjoin, show (aeval fun p => (X (g p) : MvPolynomial _ F)) f = rename g f from congrArg (fun φ : MvPolynomial _ F →ₐ[F] MvPolynomial _ F => φ f) (MvPolynomial.algHom_ext fun p => by simp)]
    exact (rename_injective g hg).ne_iff' (map_zero _) |>.mpr hF.ne_zero
  have hnat : (line u a b f).natDegree = δ := le_antisymm hc.1 (Polynomial.le_natDegree_of_ne_zero hlead)
  have hR : disc δ u a b f ≠ 0 := resultant_derivative_ne_zero _ F (line u a b f) δ hδ hnat (GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line F D N f hF)
  obtain ⟨v, hv⟩ := exists_specialise_ne_zero F (Fin D × Fin N) (Fin N ⊕ Fin N) _ hR
  refine ⟨disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f,
    ?_, GlobalTheory.T.totalDegree_pencilLineDiscriminant_le F D N δ f hf _ _, ?_⟩
  · have e := map_disc (aeval (Sum.elim (fun i => (X i : MvPolynomial (Fin D × Fin N) F)) fun k => C (v k))) δ u a b f
    rw [e] at hv
    simpa [u, a, b] using hv
  · intro K _ _ s hs
    have e := map_disc (aeval (fun p : Fin D × Fin N => s p.1 p.2)) δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f
    rw [e] at hs
    simp only [aeval_X, aeval_C] at hs
    have hc' := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F K D N δ f hf s (fun j => algebraMap F K (v (Sum.inl j))) (fun j => algebraMap F K (v (Sum.inr j)))
    exact _root_.GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero F K D N δ f s _ _ hδ hc'.1 hc'.2 hs

end GlobalTheory.PencilDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem isCompact_scaledInt_of_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Finite κ] {a : F} (ha : a ≠ 0) :
    IsCompact (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      fun v => isCompact_iff_compactSpace.1 (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
    have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (𝓕 := Filter.cofinite)).continuous
    rw [RestrictedProduct.range_structureMap] at h
    exact h
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun z i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul (continuous_apply i)
  have hP : IsCompact (Set.pi Set.univ fun _ : κ =>
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}) := isCompact_univ_pi fun _ => hO
  refine (hP.image hg).of_isClosed_subset ((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)) ?_
  intro z hz
  refine ⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩
  · have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _
    rw [h]
    exact hz i v
  · funext i
    simp only [g]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem indicator_coset_scaledInt_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ a ha r
  have hf : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r := continuous_id.sub continuous_const
  have hcl : IsClopen {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    ⟨((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)).preimage hf, (isOpen_scaledInt a).preimage hf⟩
  have hco : IsCompact {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (Homeomorph.subRight r).isCompact_preimage.2 (isCompact_scaledInt_of_ne_zero (κ := κ) ha)
  generalize {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = S at hcl hco ⊢
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

end GlobalTheory.EvAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.EvAdm.CosetSum

variable {F : Type} [Field F] [NumberField F]

theorem finAdele_algebraMap_apply (x : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v = algebraMap F (v.adicCompletion F) x := rfl

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F ↔ v.valuation F x ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact iff_of_eq (congrArg (· ≤ 1) (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x))

theorem int_mem (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
  rw [algebraMap_mem_iff]
  exact v.valuation_le_one x

variable {κ : Type}

theorem mul_int_mem {b : F} (hb : b ≠ 0) (x : κ → 𝓞 F) :
    (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (b * (x i : F))) ∈ scaledInt F κ b := by
  rw [mem_scaledInt]
  intro i v
  rw [finAdele_algebraMap_apply, map_mul, ← mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero (algebraMap F (v.adicCompletion F))).2 hb), one_mul]
  exact int_mem v (x i)

theorem scaledInt_mul_le {a : F} (ha : a ≠ 0) {m : 𝓞 F} (hm : m ≠ 0) :
    scaledInt F κ (a * m) ≤ scaledInt F κ a := by
  intro z hz
  rw [mem_scaledInt] at hz ⊢
  intro i v
  have hm' : algebraMap F (v.adicCompletion F) (m : F) ≠ 0 :=
    (map_ne_zero _).2 (by exact_mod_cast hm)
  have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v =
      algebraMap F (v.adicCompletion F) (m : F) *
        ((algebraMap F (v.adicCompletion F) (a * m))⁻¹ * (z i) v) := by
    set A := algebraMap F (v.adicCompletion F) a
    set M := algebraMap F (v.adicCompletion F) (m : F)
    rw [map_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_comm M A⁻¹, mul_assoc A⁻¹ M M⁻¹,
      mul_inv_cancel₀ hm', mul_one]
  rw [e]
  exact mul_mem (int_mem v m) (hz i v)

theorem rat_mem {b : F} (hb : b ≠ 0) (ξ : κ → F)
    (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ scaledInt F κ b) (i : κ) :
    ∃ x : 𝓞 F, (x : F) = ξ i / b := by
  rw [mem_scaledInt] at h
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ i / b) ≤ 1 := fun v => by
    rw [← algebraMap_mem_iff, div_eq_inv_mul, map_mul, map_inv₀]
    exact h i v
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ i / b) hv
  exact ⟨x, hx⟩

theorem indicator_scaledInt_eq_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ a ha m hm
  set I : Ideal (𝓞 F) := Ideal.span {m} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hm
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Fintype (κ → 𝓞 F ⧸ I) := Fintype.ofFinite _
  let out : 𝓞 F ⧸ I → 𝓞 F := fun q => (Ideal.Quotient.mk_surjective q).choose
  have hout : ∀ q, Ideal.Quotient.mk I (out q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
  let rep : (κ → 𝓞 F ⧸ I) → (κ → F) := fun c i => a * ((out (c i) : 𝓞 F) : F)
  let ι : (κ → F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun ξ i => algebraMap F _ (ξ i)
  have hrep_inj : Function.Injective rep := by
    intro c c' h
    funext i
    have h1 := congrFun h i
    simp only [rep, mul_right_inj' ha] at h1
    have h2 : out (c i) = out (c' i) := by exact_mod_cast h1
    rw [← hout (c i), ← hout (c' i), h2]
  have hrepS : ∀ c, ι (rep c) ∈ scaledInt F κ a := fun c => mul_int_mem ha (fun i => out (c i))
  have hsub := scaledInt_mul_le (κ := κ) ha hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast hm
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha hm0
  have huniq : ∀ c c' (y : κ → FiniteAdeleRing (𝓞 F) F), y - ι (rep c) ∈ scaledInt F κ (a * m) →
      y - ι (rep c') ∈ scaledInt F κ (a * m) → c = c' := by
    intro c c' y h h'
    have hd : ι (fun i => rep c' i - rep c i) ∈ scaledInt F κ (a * m) := by
      have := sub_mem h h'
      convert this using 1
      funext i
      simp only [ι, Pi.sub_apply, map_sub]
      abel
    funext i
    obtain ⟨z, hz⟩ := rat_mem ham _ hd i
    have h3 : ((out (c' i) - out (c i) : 𝓞 F) : F) = ((z * m : 𝓞 F) : F) := by
      have hz' : (z : F) * (a * m) = rep c' i - rep c i := by rw [hz, div_mul_cancel₀ _ ham]
      simp only [rep] at hz'
      push_cast
      apply mul_left_cancel₀ ha
      linear_combination (-1 : F) * hz'
    have h4 : out (c' i) - out (c i) ∈ I := by
      rw [hIdef, Ideal.mem_span_singleton']
      exact ⟨z, by exact_mod_cast h3.symm⟩
    have h5 := (Ideal.Quotient.eq).2 h4
    rw [hout, hout] at h5
    exact h5.symm
  have hexist : ∀ y ∈ scaledInt F κ a, ∃ c, y - ι (rep c) ∈ scaledInt F κ (a * m) := by
    intro y hy
    have hd : DenseRange ι :=
      DenseRange.piMap (fun _ => GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F)
    have hopen : IsOpen {z | y - z ∈ (scaledInt F κ (a * m) : Set (κ → FiniteAdeleRing (𝓞 F) F))} :=
      (isOpen_scaledInt (a * m)).preimage (continuous_const.sub continuous_id)
    obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hopen ⟨y, by simp [zero_mem]⟩
    have hξ' : y - ι ξ ∈ scaledInt F κ (a * m) := hξ
    have hξa : ι ξ ∈ scaledInt F κ a := by
      have := sub_mem hy (hsub hξ')
      simpa using this
    choose x hx using fun i => rat_mem ha ξ hξa i
    have ht : ∀ i, ∃ t : 𝓞 F, t * m = out (Ideal.Quotient.mk I (x i)) - x i := fun i => by
      have := (Ideal.Quotient.eq).1 (hout (Ideal.Quotient.mk I (x i)))
      exact Ideal.mem_span_singleton'.1 this
    choose t htm using ht
    refine ⟨fun i => Ideal.Quotient.mk I (x i), ?_⟩
    have hF : ∀ i, rep (fun i => Ideal.Quotient.mk I (x i)) i = ξ i + a * m * (t i : F) := fun i => by
      have e1 : ((t i * m : 𝓞 F) : F) = ((out (Ideal.Quotient.mk I (x i)) - x i : 𝓞 F) : F) := by rw [htm i]
      push_cast at e1
      have e2 : ξ i = a * (x i : F) := by rw [hx i]; field_simp
      simp only [rep]
      rw [e2]
      linear_combination (-a) * e1
    have hw : ι (fun i => a * m * (t i : F)) ∈ scaledInt F κ (a * m) := mul_int_mem ham t
    have e : y - ι (rep (fun i => Ideal.Quotient.mk I (x i))) = (y - ι ξ) - ι (fun i => a * m * (t i : F)) := by
      funext i
      simp only [ι, Pi.sub_apply]
      rw [hF i, map_add (f := _)]
      abel
    rw [e]
    exact sub_mem hξ' hw
  refine ⟨Finset.univ.image rep, ?_⟩
  rw [Finset.sum_image (fun c _ c' _ h => hrep_inj h)]
  funext y
  rw [Finset.sum_apply]
  by_cases hy : y ∈ scaledInt F κ a
  · obtain ⟨c0, hc0⟩ := hexist y hy
    rw [Set.indicator_of_mem (by exact hy), Finset.sum_eq_single c0]
    · rw [Set.indicator_of_mem (by exact hc0)]
    · intro c _ hc
      rw [Set.indicator_of_notMem]
      intro h
      exact hc (huniq c c0 y h hc0)
    · intro h
      exact absurd (Finset.mem_univ c0) h
  · rw [Set.indicator_of_notMem (by exact hy)]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [Set.indicator_of_notMem]
    intro h
    apply hy
    rw [show y = (y - ι (rep c)) + ι (rep c) from (sub_add_cancel _ _).symm]
    exact add_mem (hsub h) (hrepS c)

end GlobalTheory.EvAdm.CosetSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SegDualExistsTerms
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.SegDualProof

theorem segDual_exists_terms : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) → (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) → (∀ x, (D x).1 = x.1) → ∀ Δ : Segment k, (∃ Δ', SegDual Δ Δ') ∧ ∀ Δ', SegDual Δ Δ' → Δ'.len = Δ.len ∧ ∀ a : ℕ, a < Δ.len → Δ'.first.nu (a : ℂ) = D (Δ.first.nu ((Δ.len : ℂ) - 1 - a)) := by
  intro k _ _ _ _ D hD _ hnu hcusp _ Δ
  have hρ : (D (Δ.first.nu ((Δ.len : ℂ) - 1))).IsCusp := hcusp _ (Δ.isCusp_first.nu _)
  refine ⟨⟨Segment.ofFirst _ hρ Δ.len Δ.len_pos, rfl, (hD _ _).2 rfl⟩, ?_⟩
  rintro Δ' ⟨hl, hd⟩
  refine ⟨hl, fun a _ => ?_⟩
  rw [(hD _ _).1 hd]
  have h1 := hnu (Δ.first.nu ((Δ.len : ℂ) - 1)) (-(a : ℂ))
  rw [neg_neg, IrrGL.nu_nu, ← sub_eq_add_neg] at h1
  exact h1.symm

end GlobalTheory.SegDualProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpace
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SkewGram

theorem det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsSkew σ B r s → X.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B n X r s h hJ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  have hM : (Complex.I • X.J.map (B.emb w).1).det = 0 := by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * (Complex.I • X.J.map (B.emb w).1) * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e.symm e.symm := by
    rw [← hA]; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, hM] at hd
  rw [Matrix.det_neg, Matrix.det_one, Matrix.det_one, mul_one, one_mul, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

end GlobalTheory.SkewGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponentStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  first | exact @GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | exact GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | (intros; apply GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero <;> assumption)
end

