module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0875
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0889

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorIner
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.UseFive

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem exists_good_gen (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (g0 : GE N)
    (hw : ∃ w ∈ placesOver H.E (N.l i), g0 ∈ Ine (F := H.E) (N.plOm.1 w))
    (hord : orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) =
      N.l i - 1)
    (hu : ∀ a ∈ Finset.Icc 1 R.t, ∀ b ∈ Finset.Icc 1 R.t, a ≠ b →
      IsUnit (((N.chi i a g0 : (N.O i)ˣ) : N.O i) - ((N.chi i b g0 : (N.O i)ˣ) : N.O i)))
    (eB e1 X0 : N.X i → MatN N i) (hT : CharPolyIn (N.T i) rep)
    (hspan : Submodule.span (N.O i) (Set.range (mat (ρ π))) = ⊤)
    (hid : InRing (N.T i) rep eB ∧ InRing (N.T i) rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧
      e1 * eB = 0 ∧ (∀ x, ((eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((e1 x).map (toK N i)).rank = 1))
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (hd : IsDecomp (t := R.t) (rep π) (ρ π) (N.chi i) e)
    (heB : ∀ u, e (((eB π).map (toK N i)).mulVec u) = (0, (e u).2))
    (hX : InRing (N.T i) rep X0) (hX1 : eB * X0 = X0) (hX2 : X0 * eB = X0)
    (hXπ : ∀ u, e (((X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i) * (e u).2 c))
    (hβ : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c))) :
    ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧ IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition N rep ρ π S := by
  classical
  have hinjχ : Set.InjOn (fun c => ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) (Finset.Icc 1 R.t : Set ℕ) := by
    intro a ha b hb hab
    by_contra hne
    have := hu a ha b hb hne
    simp only at hab
    rw [hab, sub_self] at this
    exact not_isUnit_zero this
  have hβ' : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c)) ∧
      (x = π → ∀ c, β c = ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i)) := by
    intro x
    by_cases hx : x = π
    · subst hx
      refine ⟨fun c => ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i), fun a b hab => ?_, ?_,
        fun _ _ => rfl⟩
      · have := hinjχ (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) hab
        exact Fin.ext (by omega)
      · apply Polynomial.map_injective (toK N i) (IsFractionRing.injective _ _)
        rw [blockPol_map, (_root_.GlobalTheory.CharBlock.rank_blockPol_proj e _ _ _ heB hXπ).2, Polynomial.map_prod]
        simp
    · obtain ⟨β, h1, h2⟩ := hβ x
      exact ⟨β, h1, h2, fun h => absurd h hx⟩
  choose β hβi hβp hβπ using hβ'
  have hrπ : ∀ c ∈ Finset.Icc 1 R.t, root β c (π, 1) = ((N.chi i c g0 : (N.O i)ˣ) : N.O i) := by
    intro c hc
    obtain ⟨a, rfl⟩ := exists_succ hc
    rw [root_succ]
    exact hβπ π rfl a
  have hset : (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ) =
      Set.range fun c : Fin R.t => fun x' : N.X i × Equiv.Perm (Fin R.t) => β x'.1 (x'.2 c) := by
    ext f
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, rfl⟩ := exists_succ hc
      exact ⟨a, funext fun x' => (root_succ β a x').symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℕ) + 1, by simp, funext fun x' => root_succ β a x'⟩
  let T' : Subalgebra (N.O i) (N.X i × Equiv.Perm (Fin R.t) → N.O i) :=
    Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f x'.1) '' (N.T i : Set _) ∪
      (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ))
  have hTT : ∀ f ∈ N.T i, (fun x' : N.X i × Equiv.Perm (Fin R.t) => f x'.1) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  have hT' : CharPolyIn T' (fun x' => rep x'.1) := fun h d => hTT _ (hT h d)
  obtain ⟨ψρ, ψχ, hψ, hψs⟩ := GlobalTheory.T.exists_block_action_of_decomposition T' (fun x' => rep x'.1) (ρ π) (N.chi i) (π, 1) e hspan hd
  have hpol : ∀ x' : N.X i × Equiv.Perm (Fin R.t),
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (root β c x')) =
        blockPol (eB x'.1) (X0 x'.1) := by
    intro x'
    rw [prod_Icc_eq, hβp, ← Equiv.prod_comp x'.2 (fun c => Polynomial.X - Polynomial.C (β x'.1 c))]
    simp only [root_succ]
  have hE := fun x' : N.X i × Equiv.Perm (Fin R.t) =>
    GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain R.nV R.t (eB x'.1) (X0 x'.1) (fun c => root β c x') (two_le_ranks_t R)
      (congrFun hid.2.2.1 _) (congrFun hX1 _) (congrFun hX2 _) (by
        intro c hc c' hc' h
        obtain ⟨a, rfl⟩ := exists_succ hc
        obtain ⟨a', rfl⟩ := exists_succ hc'
        simp only [root_succ] at h
        rw [x'.2.injective (hβi _ h)]) (hpol x')
  refine ⟨{ eB := eB, e1 := e1, g0 := g0, X0 := X0, X' := N.X i × Equiv.Perm (Fin R.t), p := Prod.fst,
            T' := T', rr := root β, π' := (π, 1), e := e, ψρ := ψρ, ψχ := ψχ }, rfl,
    hid, hd, hψ, hψs, hw, hord, ⟨hX, hX1, hX2, hXπ⟩, ⟨hTT, ?_, rfl, ?_, ?_⟩, hpol, ⟨rfl, hrπ⟩,
    ⟨fun x' => (hE x').1, fun x' => (hE x').2, ?_, ?_⟩, _root_.GlobalTheory.SpanRing.coeff_det_generic_sum_mem_of_inRing T' _ hT', _root_.GlobalTheory.SpanRing.blockDet_mem T' _ hT'⟩
  · exact fun c hc => Algebra.subset_adjoin (Or.inr ⟨c, hc, rfl⟩)
  · have := GlobalTheory.SplittingAlgebra.main (N.T i) R.t β hβi (N.T_sep i) (fun j => by
      simpa only [hβp] using blockPol_coeff_mem hT hid.1 hX j)
    simp only [← hset] at this
    exact this
  · intro x
    have : {x' : N.X i × Equiv.Perm (Fin R.t) // x'.1 = x} ≃ Equiv.Perm (Fin R.t) :=
      { toFun := fun a => a.1.2
        invFun := fun σ => ⟨(x, σ), rfl⟩
        left_inv := by rintro ⟨⟨y, σ⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr this).trans (by simp [Fintype.card_perm])
  · refine GlobalTheory.T.prod_other_root_factors_action_first_coordinate e (eB π) (X0 π) (fun c => root β c (π, 1)) (two_le_ranks_t R) heB (fun u => ?_)
    rw [hXπ]
    congr 1
    funext c
    rw [hrπ _ (by simp)]
  · have h2 := two_le_ranks_t R
    have : del51 N (⟨eB, e1, g0, X0, N.X i × Equiv.Perm (Fin R.t), Prod.fst, T', root β, (π, 1), e, ψρ, ψχ⟩ :
        IdempotentChoiceData N i) (π, 1) = ∏ c ∈ Finset.Ioc 1 R.t,
        (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      show root β 1 (π, 1) - root β c (π, 1) = _
      rw [hrπ 1 (by simp; omega), hrπ c (Finset.Ioc_subset_Icc_self hc)]
    rw [this]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun c hc => ?_)
    have hc' := Finset.mem_Ioc.1 hc
    exact hu 1 (by simp; omega) c (Finset.Ioc_subset_Icc_self hc) (by omega)

end Record

theorem objects_globalStep_gen : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), GoodR D.nd i r → TruncatedSeriesCountingIdentities.admG1 i r → TruncatedSeriesCountingIdentities.admG3 i r ρ π → TruncatedSeriesCountingIdentities.FamilyContinuous i r → TruncatedSeriesCountingIdentities.admSS i r → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → TruncatedSeriesCountingIdentities.CyclotomicInertiaImage (D := D) i → ResSpan i ρ π → π ∈ D.nd.Z i → (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) → D.R.t + 1 < D.nd.l i → ∃ S : IdempotentChoiceData D.nd i, IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S := by
  intro D i r ρ π _ hG1 _ _ _ hdec _ hres _ hun ht
  classical
  obtain ⟨e, hd⟩ := hdec
  obtain ⟨w, hw, g0, hg0, hord⟩ := GlobalTheory.T.exists_inertia_cyclotomic_generates_units_mod D.nd i hun
  have hu := GlobalTheory.T.isUnit_sub_charValues_of_cyclotomic_generator D.nd i g0 hord ht
  have hT : CharPolyIn (D.nd.T i) r := hG1
  have hspan : Submodule.span (D.nd.O i) (Set.range (mat (ρ π))) = ⊤ := GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top (ρ π) hres
  obtain ⟨eB, e1, ⟨hB, h1, hBB, h11, hB1, h1B⟩, heB, ε, hε, he1⟩ :=
    GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep (D.nd.l i) (D.nd.T i) r (ρ π) (D.nd.chi i) π e (two_le_r _) hspan hd
  have hl := D.nd.T_local i
  have hXπ : ∀ u, e (((eB π * mat (r π) g0 * eB π).map (toK D.nd i)).mulVec u) =
      (0, fun c : Fin D.R.t => toK D.nd i ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c) := by
    intro u
    rw [Matrix.map_mul, Matrix.map_mul]
    exact corner_act e heB (hd g0) u
  have hat := _root_.GlobalTheory.CharBlock.rank_blockPol_proj e _ _ _ heB hXπ
  have hrB : ∀ x, ((eB x).map (toK D.nd i)).rank = D.R.t := fun x => by
    rw [rank_const hl hT hB hBB x π]; exact hat.1
  have hr1 : ∀ x, ((e1 x).map (toK D.nd i)).rank = 1 := fun x => by
    rw [rank_const hl hT h1 h11 x π, GlobalTheory.T.rank_eq_of_mulVec_through_first_block e _ ε he1, hε]
  have hX : InRing (D.nd.T i) r (fun x => eB x * mat (r x) g0 * eB x) :=
    inRing_mul (inRing_mul hB (inRing_mat g0)) hB
  have hBx : ∀ x, eB x * eB x = eB x := congrFun hBB
  have hX1 : eB * (fun x => eB x * mat (r x) g0 * eB x) = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, ← mul_assoc, hBx]
  have hX2 : (fun x => eB x * mat (r x) g0 * eB x) * eB = fun x => eB x * mat (r x) g0 * eB x := by
    funext x; simp only [Pi.mul_apply, mul_assoc, hBx]
  haveI := D.nd.O_complete i
  have hβ := _root_.GlobalTheory.hensel_roots_of_local_family (t := D.R.t) (D.nd.T i) hl (fun x => blockPol (eB x) (eB x * mat (r x) g0 * eB x))
    (blockPol_coeff_mem hT hB hX)
    (fun x => by
      have hm := blockPol_monic (congrFun hBB x) (hrB x) (congrFun hX1 x) (congrFun hX2 x)
      exact ⟨Polynomial.monic_of_injective (IsFractionRing.injective _ _) hm.1,
        (Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _).symm.trans hm.2⟩)
    π (fun c => ((D.nd.chi i ((c : ℕ) + 1) g0 : (D.nd.O i)ˣ) : D.nd.O i))
    (fun a b hab => hu _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) _ (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (fun h => hab (Fin.ext (by omega))))
    (by
      apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective _ _)
      rw [blockPol_map, hat.2, Polynomial.map_prod]
      simp)
  obtain ⟨S, -, hS⟩ := exists_good_gen D.nd i r ρ π g0 ⟨w, hw, hg0⟩ hord hu eB e1 _ hT hspan
    ⟨hB, h1, hBB, h11, hB1, h1B, hrB, hr1⟩ e hd heB hX hX1 hX2 hXπ hβ
  exact ⟨S, hS⟩

end GlobalTheory.UseFive

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTensorTorsionCocycleOfTorsionLocal
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases.LiftW

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def basisVec (k : ℕ) (j : Fin k) : ↥(stdG O LL k) :=
  ⟨Pi.single j 1, ⟨Pi.single j 1, by
    funext j'
    simp [Pi.single_apply]⟩⟩

def coordQ (k : ℕ) (j : Fin k) : ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL k).mapQ (intO LL) (LinearMap.proj j) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u j, rfl⟩)

theorem coordQ_mk (k : ℕ) (j : Fin k) (v : Fin k → LL) :
    coordQ (O := O) LL k j (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v j) := rfl

theorem iotaW_tmul (lam : O) (a k : ℕ) (t : ↥(stdG O LL k)) (s : LL)
    (hs : (Submodule.Quotient.mk s : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a) :
    iotaW LL lam a k (t ⊗ₜ ⟨Submodule.Quotient.mk s, hs⟩) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := rfl

theorem exists_sum (k : ℕ) {X : Type} [AddCommGroup X] [Module O X] (u : ↥(stdG O LL k) ⊗[O] X) :
    ∃ x : Fin k → X, u = ∑ j, basisVec LL k j ⊗ₜ[O] x j := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t y =>
    obtain ⟨_, c, rfl⟩ := t
    refine ⟨fun j => c j • y, ?_⟩
    simp only [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    apply Subtype.ext
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩

theorem coordQ_iotaW (lam : O) (a k : ℕ) (x : Fin k → ↥(Xq LL lam a)) (j : Fin k) :
    coordQ LL k j (iotaW LL lam a k (∑ j', basisVec LL k j' ⊗ₜ[O] x j')) = x j := by
  have h : ∀ j', coordQ LL k j (iotaW LL lam a k (basisVec LL k j' ⊗ₜ[O] x j')) =
      if j = j' then (x j' : LL ⧸ intO (O := O) LL) else 0 := by
    intro j'
    obtain ⟨y, hy⟩ := x j'
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [iotaW_tmul, coordQ_mk]
    by_cases hj : j = j' <;> simp [basisVec, hj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, h]

theorem iotaW_injective (lam : O) (a k : ℕ) : Function.Injective (iotaW LL lam a k) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨x, rfl⟩ := exists_sum LL k u
  have : x = 0 := by
    funext j
    apply Subtype.ext
    rw [← coordQ_iotaW, hu]
    simp
  simp [this]

theorem exists_iotaW (lam : O) (a k : ℕ) (q : (Fin k → LL) ⧸ stdG O LL k) (hq : lam ^ a • q = 0) :
    ∃ u, iotaW LL lam a k u = q := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : ∀ j, (Submodule.Quotient.mk (v j) : LL ⧸ intO (O := O) LL) ∈ Xq LL lam a := by
    intro j
    have := congrArg (coordQ LL k j) hq
    rw [map_smul, map_zero, coordQ_mk] at this
    exact this
  refine ⟨∑ j, basisVec LL k j ⊗ₜ[O] ⟨_, hx j⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, iotaW_tmul]
  have : v = ∑ j, v j • (basisVec (O := O) LL k j : Fin k → LL) := by
    funext j'
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [this]
  exact (map_sum (stdG O LL k).mkQ _ _).symm

variable {LL}

theorem iotaW_actTw (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (u : ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a)) :
    iotaW LL lam a k (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g u) =
      actD (stdLatG hinj N) g (iotaW LL lam a k u) := by
  induction u using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans
      ((congrArg _ (map_zero _)).trans (map_zero _)).symm)
  | add u v hu hv =>
    have e1 := map_add (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ g) u v
    have e2 := map_add (actD (stdLatG hinj N) g) (iotaW LL lam a k u) (iotaW LL lam a k v)
    refine (congrArg _ e1).trans ((map_add _ _ _).trans ?_)
    rw [map_add (f := _)]
    exact (congrArg₂ (· + ·) hu hv).trans e2.symm
  | tmul t y =>
    obtain ⟨y, hy⟩ := y
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine (map_smul (iotaW LL lam a k) (((θ g)⁻¹ : Oˣ) : O)
      ((show ↥(stdG O LL k) from actT (stdLatG hinj (twistM N θ)) g t) ⊗ₜ[O] ⟨Submodule.Quotient.mk s, hy⟩)).trans ?_
    rw [iotaW_tmul, iotaW_tmul, ← Submodule.Quotient.mk_smul]
    refine congrArg Submodule.Quotient.mk ?_
    show (((θ g)⁻¹ : Oˣ) : O) • s • (((((θ g : Oˣ) : O) • N g).map (algebraMap O LL)).mulVec (t : Fin k → LL)) =
      ((N g).map (algebraMap O LL)).mulVec (s • (t : Fin k → LL))
    have e : (((θ g : Oˣ) : O) • N g).map (algebraMap O LL) = ((θ g : Oˣ) : O) • (N g).map (algebraMap O LL) := by
      ext p q
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [Algebra.smul_def]
    rw [e, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_comm s, smul_smul, Units.inv_mul, one_smul]

theorem exists_twistedCocycle_lift_torsion (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) θ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  choose z hz using fun g => exists_iotaW LL lam a k (f g) (hk g)
  refine ⟨z, ⟨?_, fun g h => ?_⟩, hz⟩
  · refine IsLocallyConstant.desc z (iotaW LL lam a k) ?_ (iotaW_injective LL lam a k)
    have : (iotaW LL lam a k) ∘ z = f := funext hz
    rw [this]
    exact hf.1
  · apply iotaW_injective LL lam a k
    refine (hz _).trans ((hf.2 g h).trans ?_)
    refine Eq.trans ?_ (map_add (iotaW LL lam a k) (z g) _).symm
    rw [hz g, ← hz h]
    exact congrArg _ (iotaW_actTw hinj lam a N θ g (z h)).symm

theorem lift_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (lam : O) (a : ℕ) {k : ℕ} (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : χ = θ)
    (f : G → (Fin k → LL) ⧸ stdG O LL k) (hf : f ∈ divisibleCocycles (stdLatG hinj N)) (hk : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(stdLatG hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaW LL lam a k (z' g) = f g := by
  subst hχ
  exact exists_twistedCocycle_lift_torsion hinj lam a N χ f hf hk

end Gen

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  ext g
  simp [chiT, chiOC]

theorem lift_cocycle : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ)
      (f : Br.G D.nbr i w hw → (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k),
    f ∈ divisibleCocycles (latC C N) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latC C (twistM N θ)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧ ∀ g, iotaW ↥C.LL.1 lam a k (z' g) = f g := by
  intro D i w hw C lam _ k N θ a f hf hk
  exact lift_gen Subtype.val_injective lam a N θ (chiT C θ 1) (chiT_one C θ) f hf hk

end GlobalTheory.UseLoc.Cases.LiftW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReading
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFamRead

set_option autoImplicit false

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

theorem rat_side (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) (hS : ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D) (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i), GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV)
    (hA : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i) (D : D7) (X : RealSide D) (i : Fin D.R.m) : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke X.R.toRealDat i := by
  refine hA D X.Γ X.Pl0 X.T X.A3.A X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.fw i hT X.char.lev X.char.fam X.char.models
    (fun hV => X.inGeo.jEvExists i _ (Formalism.IndefR.FWT.base_embedding_good X.core X.R.toRealDat X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1) hV)
    ?_ (hS D X i)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra h
  have h1 := (X.unif i (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
  exact h1.ne_zero 0 hx

theorem exists_family_one (hrat : ∀ (D : D7) (X : RealSide D) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke X.R.toRealDat i)
    (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
      (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL := by
  obtain ⟨hL, hs, hr⟩ := _root_.GlobalTheory.Adopt.exists_rational_hecke_family_on_rational_datum_forms D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG S YS X.char.lev X.char.allPl (hrat D X)
  refine ⟨fun j k P => if k = 0 then 1 else hL j k P, fun j h1 h2 k P x hx => ?_, fun j P => if_pos rfl, ?_⟩
  · by_cases hk : k = 0
    · simp only [hk, if_true, Module.End.one_apply]
      exact hx
    · simp only [hk, if_false]
      exact hs j h1 h2 k P x hx
  · intro i k P hsp hso hk α Rc hα hdc x
    by_cases h0 : k = 0
    · subst h0
      have e1 := hr i 0 P hsp hso hk α Rc hα hdc x
      have e2 := hr i 0 P hsp hso hk 1 {1} (isHeckeAt_zero_one _ hsp) (isDC_one _) x
      have e3 : ∀ F, heckeOn (X.R.MW i (sg0 D X.A3.A)) {1} F = F := by
        intro F
        ext v g
        simp [heckeOn, postOn, heckeLin]
      rw [e3] at e2
      simp only [pow_zero, zero_mul, inv_one, mul_one, one_smul] at e1 e2 ⊢
      exact e2.symm.trans e1
    · simp only [h0, if_false]
      exact hr i k P hsp hso hk α Rc hα hdc x

theorem exists_family_reads : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D), ∀ (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S), ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL :=
  fun hD hT hR D X S YS => exists_family_one (rat_side hT (_root_.GlobalTheory.HeckeSupReal.readsCusp_realSide hD hR) _root_.GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp) D X S YS

end GlobalTheory.HeckeFamRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedChar
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem chiOC_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) : chiOC C 1 = 1 := by
  ext g; simp [chiOC]

theorem chiT_one {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  rw [chiT, mul_inv_cancel, chiOC_one, one_mul]

theorem repV_eq_inv_smul_twist : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  intro D i w hw C k N θ g
  rw [chiT_one]
  have h : repV C (twistM N θ) g = (algebraMap (↥(OL C.LL)) (↥C.LL.1) (θ g : ↥(OL C.LL))) • repV C N g := by
    simp only [repV, matRep, mapM, twistM]
    simp [RingHom.mapMatrix_apply, Matrix.map_smul', Matrix.toLinAlgEquiv'_apply]
    rw [show ((θ g : ↥(OL C.LL)) • N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)
        = (algebraMap ↥(OL C.LL) ↥C.LL.1 (θ g : ↥(OL C.LL))) • (N g).map (algebraMap ↥(OL C.LL) ↥C.LL.1) from by
          ext a b; simp [Matrix.map_apply], map_smul]
    rfl
  rw [h, smul_smul]
  simp [tableLineDegreeTwo.charL]

end GlobalTheory.UseLoc.Cases
end

