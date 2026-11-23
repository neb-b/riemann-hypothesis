module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AmpleTwistSectionsGenerateSubsheaf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem le_of_epi_sectionsHom {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules} (S B : Subobject P) (n : ℤ) {k : ℕ}
    (s : Fin k → Γ(GlobalTheory.twistZ (S : X.Modules) H n, ⊤)) (hs : Epi (GlobalTheory.QCoh.sectionsHom s))
    (hB : ∀ i, genSub hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)) ≤ B) : S ≤ B := by
  have hL' := GlobalTheory.Twist.isLB_lbZPow hH (-n)
  have h₁ := (GlobalTheory.Twist.epi_map_iff hL' (GlobalTheory.QCoh.sectionsHom s)).2 hs
  have := GlobalTheory.Twist.preservesColimits_twistFunctor hL'
  let T := GlobalTheory.twistFunctor (GlobalTheory.lbZPow H (-n))
  let E : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (S : X.Modules) :=
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫
      (GlobalTheory.Twist.twistZAddIso (S : X.Modules) hH (add_neg_cancel n)).hom ≫
      (GlobalTheory.Twist.twistZZeroIso (S : X.Modules) hH).inv
  haveI hE : Epi E := epi_comp' h₁ inferInstance
  have key : ∀ i, T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) ≫ E =
      genHom hH n (s i) := fun i => by
    have e : Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i ≫ GlobalTheory.QCoh.sectionsHom s =
        GlobalTheory.QCoh.sectionHom (s i) := Sigma.ι_desc _ _
    rw [genHom, ← e]
    change T.map _ ≫ T.map _ ≫ _ = T.map (_ ≫ _) ≫ _
    exact (Category.assoc (T.map _) (T.map _) _).symm
  let g : ∀ i : Fin k, T.obj (GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) := fun i =>
    factorThruImageSubobject (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i))) ≫
      Subobject.ofLE _ _ (hB i)
  have hg : ∀ i, g i ≫ B.arrow = genHom hH n (s i) ≫ S.arrow := fun i => by
    rw [← genHom_map_app hH S.arrow n (s i)]
    exact (Category.assoc _ _ _).trans ((congrArg _ (Subobject.ofLE_arrow _)).trans
      (imageSubobject_arrow_comp
        (genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤ (s i)))))
  let c := PreservesCoproduct.iso T (fun _ : Fin k => GlobalTheory.QCoh.structureModule X)
  let t : T.obj (∐ fun _ : Fin k => GlobalTheory.QCoh.structureModule X) ⟶ (B : X.Modules) :=
    c.hom ≫ Sigma.desc g
  have ht : t ≫ B.arrow = E ≫ S.arrow := by
    have hι : ∀ i, Sigma.ι (fun _ : Fin k => T.obj (GlobalTheory.QCoh.structureModule X)) i ≫ c.inv =
        T.map (Sigma.ι (fun _ : Fin k => GlobalTheory.QCoh.structureModule X) i) :=
      fun i => ι_comp_sigmaComparison T _ i
    have h₂ : c.inv ≫ t = Sigma.desc g := Iso.inv_hom_id_assoc c _
    have h₃ : c.inv ≫ t ≫ B.arrow = c.inv ≫ E ≫ S.arrow := by
      rw [← Category.assoc, h₂]
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, Sigma.ι_desc, hg i, ← key i, ← Category.assoc, ← Category.assoc,
        hι i]
      rfl
    exact (cancel_epi c.inv).1 h₃
  haveI : StrongEpi E := strongEpi_of_epi E
  have sq : CommSq t E B.arrow S.arrow := ⟨ht⟩
  exact Subobject.le_of_comm sq.lift sq.fac_right

theorem le_of_genSub_le : ∀ {X : Scheme.{0}} [IsNoetherian X] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}
    (hA : GlobalTheory.IsAmpleLB H) {P : X.Modules} (S : Subobject P), IsCoherent (S : X.Modules) →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ B : Subobject P,
      (∀ b ∈ twSecs H n S, genSub hA.isLB n b ≤ B) → S ≤ B := by
  intro X _ H hA P S hS
  haveI : GlobalTheory.QCoh.IsFiniteQC (S : X.Modules) := ⟨hS.1, hS.2⟩
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.1
    (hA.eventually_isGloballyGenerated_twistZ (S : X.Modules))
  refine ⟨n₀, fun n hn B hB => ?_⟩
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 (h₀ n hn)
  exact le_of_epi_sectionsHom hA.isLB S B n s ((GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs)
    fun i => hB _ ⟨s i, rfl⟩

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatCellParabolicUnipotentFactorization
section
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.DCell

open Matrix PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem rows_rel (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have hinv : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have h' : gᴴ * JJ n * g = JJ n := h
    calc (-(JJ n) * gᴴ * JJ n) * g = -(JJ n * (gᴴ * JJ n * g)) := by
          simp only [Matrix.mul_assoc, Matrix.neg_mul]
      _ = 1 := by rw [h', JJ_mul_self, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.mp hinv
  calc g * JJ n * gᴴ = g * JJ n * gᴴ * (-(JJ n * JJ n)) := by
        rw [JJ_mul_self, neg_neg, Matrix.mul_one]
    _ = -((g * (-(JJ n) * gᴴ * JJ n)) * JJ n) * (-1) * (-1) * (-1) := by
        simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = JJ n := by
        rw [h2]; simp

theorem block_rel (g : M2 n) (h : InG g) :
    g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h1 := rows_rel g h
  have h3 : (g * JJ n * gᴴ).toBlocks₂₂ = (JJ n).toBlocks₂₂ := by rw [h1]
  rw [← fromBlocks_toBlocks g] at h3
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h3
  simp at h3
  have h4 := sub_eq_zero.mp (by
    rw [← h3]; abel : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ - g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = 0)
  exact h4

theorem inG_lower (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) :
    InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG
  rw [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hc]

def lowerU (c : Matrix (Fin n) (Fin n) ℂ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 c 1
  inv := fromBlocks 1 0 (-c) 1
  val_inv := by rw [fromBlocks_multiply, ← fromBlocks_one]; simp
  inv_val := by rw [fromBlocks_multiply, ← fromBlocks_one]; simp

theorem main : ∀ (n : ℕ) (y : PositivityTheory.Rg.Sw.GR n), ((PositivityTheory.Rg.Sw.mR y).toBlocks₂₂).det ≠ 0 → ∃ (p nbb : PositivityTheory.Rg.Sw.GR n) (c : Matrix (Fin n) (Fin n) ℂ), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 ∧ cᴴ = c ∧ PositivityTheory.Rg.Sw.mR nbb = Matrix.fromBlocks 1 0 c 1 ∧ y = p * nbb := by
  intro n y hD
  set g : M2 n := mR y with hg
  have hy : InG g := y.2
  set C := g.toBlocks₂₁ with hC
  set D := g.toBlocks₂₂ with hDd
  have hrel : C * Dᴴ = D * Cᴴ := block_rel g hy
  have hu : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hDi : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hu
  have hiD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hu
  have hiDH : (D⁻¹)ᴴ * Dᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hDi, Matrix.conjTranspose_one]
  have hc : (D⁻¹ * C)ᴴ = D⁻¹ * C := by
    rw [Matrix.conjTranspose_mul]
    have hDH : Dᴴ * (D⁻¹)ᴴ = 1 := mul_eq_one_comm.mp hiDH
    calc Cᴴ * (D⁻¹)ᴴ = (D⁻¹ * D) * Cᴴ * (D⁻¹)ᴴ := by rw [hiD, Matrix.one_mul]
      _ = D⁻¹ * (D * Cᴴ) * (D⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (C * Dᴴ) * (D⁻¹)ᴴ := by rw [hrel]
      _ = D⁻¹ * C * (Dᴴ * (D⁻¹)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = D⁻¹ * C := by rw [hDH, Matrix.mul_one]
  set c := D⁻¹ * C with hcdef
  have hmem : lowerU c ∈ GR n := inG_lower c hc
  refine ⟨y * (⟨lowerU c, hmem⟩ : GR n)⁻¹, ⟨lowerU c, hmem⟩, c, ?_, hc, rfl, by simp⟩
  have hval : mR (y * (⟨lowerU c, hmem⟩ : GR n)⁻¹) = g * fromBlocks 1 0 (-c) 1 := rfl
  rw [hval]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  have : D * c = C := by rw [hcdef, ← Matrix.mul_assoc, hDi, Matrix.one_mul]
  simp [← hC, ← hDd, this]

end GlobalTheory.CompanionTheory.DCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiagStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_functor_nonscalar_offdiag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → ∀ (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true ≠ 0 → ∀ φ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom), φ.toLinearMap = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero | exact GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_restriction_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ T : (O : Scheme.{0}).IdealSheafData, IsProper (T.subschemeι ≫ ((O : Scheme.{0}) ↘ Spec (.of A))) → Scheme.Modules.SupportedIn (cokernel (S 0).arrow) (T.support : Set (O : Scheme.{0})) → IsClosed (O.ι '' (T.support : Set (O : Scheme.{0}))) ∧ ∃ Sb : ℕ → Subobject P, ClosedSys I P Sb ∧ (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) ∧ ∀ e (V : X.Opens), Disjoint (V : Set X) (O.ι '' (T.support : Set (O : Scheme.{0}))) → secs (Sb e) V = Set.univ := by
  first | exact @GlobalTheory.CompanionTheory.GE.Extend.extend | exact GlobalTheory.CompanionTheory.GE.Extend.extend | (intros; apply GlobalTheory.CompanionTheory.GE.Extend.extend <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentNoetherianMaximalSubsheafStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coherent_noetherian_maximal_subsheaf : ∀ {X : Scheme.{0}} [IsNoetherian X] {P : X.Modules}, IsCoherent P → ∀ F : Set (Subobject P), F.Nonempty → (∀ B ∈ F, (B : X.Modules).IsQuasicoherent) → ∃ M ∈ F, ∀ B ∈ F, M ≤ B → B = M := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | exact GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject | (intros; apply GlobalTheory.CompanionTheory.GE.exists_maximal_qcoh_subobject <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteOfCommuteCyclicMatrix
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem map_aeval_commute_of_commute {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X) (h : K[X]) :
    X * (aeval γ h).map (algebraMap K R) = (aeval γ h).map (algebraMap K R) * X := by
  have hc : Commute X (γ.map (algebraMap K R)) := hX
  have key : ∀ h : K[X], Commute X (((algebraMap K R).mapMatrix (m := Fin n)) (aeval γ h)) := by
    intro h
    induction h using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _)]
      exact hp.add_right hq
    | monomial k a =>
      rw [aeval_monomial, map_mul, map_pow]
      have h1 : ((algebraMap K R).mapMatrix (m := Fin n)) γ = γ.map (algebraMap K R) := rfl
      rw [h1]
      refine Commute.mul_right ?_ (hc.pow_right k)
      have h2 : ((algebraMap K R).mapMatrix (m := Fin n)) (algebraMap K (Matrix (Fin n) (Fin n) K) a)
          = (algebraMap K R a) • (1 : Matrix (Fin n) (Fin n) R) := by
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one]
      rw [h2]
      exact (Commute.one_right X).smul_right _
  exact key h

theorem commute_of_commute_cyclic (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hv : ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v)
    (X Y : Matrix (Fin n) (Fin n) R)
    (hX : X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X)
    (hY : Y * γ.map (algebraMap K R) = γ.map (algebraMap K R) * Y) : X * Y = Y * X := by
  classical
  choose h hh using fun j : Fin n => hv (Pi.single j 1)
  set φ := algebraMap K R with hφ
  set A : Fin n → Matrix (Fin n) (Fin n) R := fun j => (aeval γ (h j)).map φ with hA
  set vR : Fin n → R := φ ∘ v with hvR
  have hAv : ∀ j, A j *ᵥ vR = Pi.single j 1 := by
    intro j
    ext i
    have := RingHom.map_mulVec φ (aeval γ (h j)) v i
    rw [hA, hvR]
    simp only
    rw [← this, ← hh j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  set w := X *ᵥ vR with hw
  set X' : Matrix (Fin n) (Fin n) R := ∑ j, w j • A j with hX'
  have hX'v : X' *ᵥ vR = w := by
    rw [hX', Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, hAv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hXA : ∀ j, X * A j = A j * X := fun j => map_aeval_commute_of_commute γ X hX (h j)
  have hYA : ∀ j, Y * A j = A j * Y := fun j => map_aeval_commute_of_commute γ Y hY (h j)
  have hAA : ∀ i j, A i * A j = A j * A i := by
    intro i j
    simp only [hA]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]
  have hX'A : ∀ j, X' * A j = A j * X' := by
    intro j
    rw [hX', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA i j]
  have hD : ∀ j, (X - X') *ᵥ (Pi.single j 1 : Fin n → R) = 0 := by
    intro j
    rw [← hAv j, Matrix.mulVec_mulVec, sub_mul, hXA j, hX'A j, ← mul_sub, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, hX'v, ← hw, sub_self, Matrix.mulVec_zero]
  have hXX' : X = X' := by
    refine sub_eq_zero.mp ?_
    ext i j
    have := congrFun (hD j) i
    simpa using this
  rw [hXX', hX', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hYA j]

end GlobalTheory.CompanionTheory.TorusCh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLowG
section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def lowU (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem lowU_mul (s t : ℝ) : (lowU s : M2 n) * lowU t = lowU (s + t) := by
  simp [lowU, fromBlocks_multiply, add_smul, add_comm]

theorem lowU_zero : (lowU 0 : M2 n) = 1 := by
  simp [lowU, fromBlocks_one]

theorem lowU_inG (t : ℝ) : InG (lowU t : M2 n) := by
  simp [InG, lowU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]

def lowG (t : ℝ) : GR n :=
  ⟨⟨lowU t, lowU (-t), by simp [lowU_mul, lowU_zero], by simp [lowU_mul, lowU_zero]⟩, lowU_inG t⟩

theorem lowG_zero : (lowG 0 : GR n) = 1 :=
  Subtype.ext (Units.ext lowU_zero)

theorem continuous_lowU : Continuous (lowU : ℝ → M2 n) := by
  unfold lowU
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem continuous_lowG : Continuous (lowG : ℝ → GR n) := by
  have h : Continuous (fun t : ℝ => ((lowG t : GR n) : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.continuous_iff.2 ⟨(continuous_lowU : Continuous (lowU : ℝ → M2 n)),
      ((continuous_lowU : Continuous (lowU : ℝ → M2 n)).comp continuous_neg)⟩
  exact h.subtype_mk _

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem mul_JJ_mul_conj {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have h1 : (JJ n * Mᴴ * JJ n) * M = -1 := by
    calc (JJ n * Mᴴ * JJ n) * M = JJ n * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [h, JJ_mul_JJ]
  have h2 : (-(JJ n * Mᴴ * JJ n)) * M = 1 := by rw [Matrix.neg_mul, h1, neg_neg]
  have h3 : M * (-(JJ n * Mᴴ * JJ n)) = 1 := mul_eq_one_comm.1 h2
  calc M * JJ n * Mᴴ = (M * (-(JJ n * Mᴴ * JJ n))) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, JJ_mul_JJ]
        simp
    _ = JJ n := by rw [h3, Matrix.one_mul]

theorem lower_symm {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    C * Dᴴ = D * Cᴴ := by
  have := congrArg toBlocks₂₂ (mul_JJ_mul_conj h)
  simp [JJ, fromBlocks_multiply, fromBlocks_conjTranspose] at this
  exact (neg_add_eq_zero.1 this).symm

theorem det_lower_I_ne (y : GR n) :
    ((mR y).toBlocks₂₁ + Complex.I • (mR y).toBlocks₂₂).det ≠ 0 := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hM : InG (fromBlocks (mR y).toBlocks₁₁ (mR y).toBlocks₁₂ C D) := by
    rw [hC, hD, fromBlocks_toBlocks]; exact y.2
  have hs : C * Dᴴ = D * Cᴴ := lower_symm hM
  intro h0
  obtain ⟨v, hv, hvE⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have hEE : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = fromCols C D * (fromCols C D)ᴴ := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows]
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, hs, smul_smul, Complex.star_def, Complex.conj_I]
    simp
    abel_nf
    simp [smul_smul]
  have hL : v ᵥ* fromCols C D = 0 := by
    rw [← Matrix.vecMul_self_mul_conjTranspose_eq_zero, ← hEE, ← Matrix.vecMul_vecMul, hvE,
      Matrix.zero_vecMul]
  have hw : (Sum.elim (0 : Fin n → ℂ) v) ᵥ* mR y = 0 := by
    funext j
    have := congrFun hL j
    rcases j with j | j <;>
      simpa [vecMul, dotProduct, Fintype.sum_sum_type, C, D, toBlocks₂₁, toBlocks₂₂] using this
  have hdet : (mR y).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero y.1
  have := Matrix.eq_zero_of_vecMul_eq_zero hdet hw
  apply hv
  funext i
  simpa using congrFun this (Sum.inr i)

def detPoly (C D : Matrix (Fin n) (Fin n) ℂ) : Polynomial ℂ :=
  (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C).det

theorem eval_detPoly (C D : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    (detPoly C D).eval z = (C + z • D).det := by
  have := (Polynomial.evalRingHom z).map_det
    (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  rw [detPoly, ← Polynomial.coe_evalRingHom, this]
  congr 1
  ext i j
  simp
  ring

theorem lower_mul_lowG (y : GR n) (t : ℝ) :
    (mR (y * lowG t)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (t : ℂ) • (mR y).toBlocks₂₂ := by
  have h : mR (y * lowG t) = mR y * lowU t := rfl
  rw [h]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  simp [lowU, fromBlocks_multiply]

theorem dense_bigCell : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
  intro n y
  have hP : detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂ ≠ 0 := by
    intro h
    apply det_lower_I_ne y
    rw [← eval_detPoly, h, Polynomial.eval_zero]
  have hfin : {t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0}.Finite :=
    (Polynomial.finite_setOf_isRoot hP).preimage Complex.ofReal_injective.injOn
  have hcl : IsClosed ({t : ℝ | (detPoly (mR y).toBlocks₂₁ (mR y).toBlocks₂₂).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnh := hcl.isOpen_compl.mem_nhds (x := (0 : ℝ)) (by simp)
  have ht : Tendsto (fun t : ℝ => y * lowG t) (𝓝[≠] 0) (𝓝 y) := by
    have hc : Continuous (fun t : ℝ => y * lowG t) := continuous_const.mul continuous_lowG
    have := hc.tendsto 0
    simp only [lowG_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [nhdsWithin_le_nhds hnh, self_mem_nhdsWithin] with t h1 h2
  show ((mR (y * lowG t)).toBlocks₂₁).det ≠ 0
  rw [lower_mul_lowG, ← eval_detPoly]
  intro h3
  exact h1 ⟨h3, h2⟩

end GlobalTheory.CompanionTheory.BigCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnLambdaSubgroup
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusCh

theorem continuous_chi {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) E) : Continuous (chi e : GA E n → Ad E) := by
  unfold chi
  refine Continuous.matrix_det ?_
  exact continuous_const.add (continuous_const.mul (Units.continuous_val.sub continuous_const))

theorem continuousOn_lam (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e)
    (hlog : ∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ))
    (H : Subgroup (GA E n)) (hH : ∀ t ∈ H, t.val * rm e = rm e * t.val) :
    ContinuousOn (lam e) (H : Set (GA E n)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let ψ : ↥(H : Set (GA E n)) → (Ad E)ˣ := fun t =>
    ⟨chi e t.1, chi e t.1⁻¹,
      by rw [← chi_mul e he _ _ (hH _ t.2), mul_inv_cancel, chi_one],
      by rw [← chi_mul e he _ _ (comm_inv (hH _ t.2)), inv_mul_cancel, chi_one]⟩
  have hψ : Continuous ψ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_chi e).comp continuous_subtype_val
    · exact (continuous_chi e).comp (continuous_inv.comp continuous_subtype_val)
  have hm : Continuous fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ) :=
    continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp hψ)
  have heq : (H : Set (GA E n)).domRestrict (lam e) =
      fun t : ↥(H : Set (GA E n)) => Real.log (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t) : ℝ) := by
    funext t
    exact hlog (ψ t)
  rw [heq]
  exact hm.log fun t => (GroundTheory.Global.IdeleGroup.ideleModule E (ψ t)).2.ne'

end GlobalTheory.CompanionTheory.TorusCh

end
end

