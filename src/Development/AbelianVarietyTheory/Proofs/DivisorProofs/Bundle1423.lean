module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.LocalGeometry.Imports
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalArchimedeanSchwartzFockOperator
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.FockKFinStep
open GlobalTheory.ThK.EvAt0.PolD LineDeriv

theorem lin_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (b x : κ → mixedEmbedding.mixedSpace F) :
    lin b x = ∑ j, (B.repr b j : ℂ) * lin (B j) x := by
  conv_lhs => rw [← B.sum_repr b]
  simp only [lin, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, Finset.mul_sum]

theorem fderiv_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) (x) :
    fderiv ℝ f x a = ∑ j, (B.repr a j : ℂ) * fderiv ℝ f x (B j) := by
  conv_lhs => rw [← B.sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Complex.real_smul]

theorem sumAt {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (s : Finset ι) (g : ι → SInf F κ) (x) :
    (∑ j ∈ s, g j) x = ∑ j ∈ s, g j x := by simp

theorem dOp_expand {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (B : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ) :
    dOp a b f = ∑ j, (B.repr a j : ℂ) • ∂_{B j} f -
      (2 * Real.pi * Complex.I : ℂ) • ∑ j, (B.repr b j : ℂ) • mulOp (B j) f := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [dOp_apply, fderiv_expand B a f x, lin_expand B b x]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, sumAt, smul_eq_mul,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, mulOp_apply, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

theorem dStep_finiteDimensional : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (P : Submodule ℂ (SInf F κ)),
    FiniteDimensional ℂ P → FiniteDimensional ℂ (GlobalTheory.FockKFin.dStep P) := by
  intro F _ _ κ _ P hP
  let B := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let T : Submodule ℂ (SInf F κ) :=
    (⨆ j, P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap) ⊔ ⨆ j, P.map (mulOp (B j)).toLinearMap
  haveI : FiniteDimensional ℂ T := by
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (lineDerivOpCLM ℂ (SInf F κ) (B j)).toLinearMap)
    haveI := Submodule.finiteDimensional_iSup (fun j => P.map (mulOp (B j)).toLinearMap)
    exact Submodule.finiteDimensional_sup _ _
  refine Submodule.finiteDimensional_of_le (S₂ := T) ?_
  rw [GlobalTheory.FockKFin.dStep, Submodule.span_le]
  rintro _ ⟨a, b, f, hf, rfl⟩
  rw [dOp_expand B]
  refine Submodule.sub_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨f, hf, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem (p := fun j => P.map (mulOp (B j)).toLinearMap) j ⟨f, hf, rfl⟩))

end GlobalTheory.FockKFinStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSlowlyIncreasingKilledCapelliPo
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth Filter Topology

theorem GlobalTheory.CapKilled.finite_of_finiteness : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ),
    (∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ),
      FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E b) → ℂ), X.Finite → ∀ N : ℕ,
        FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E b L W X N))) →
    ∀ (L : Subgroup (GL (Fin b) (Af E))), IsOpen (L : Set (GL (Fin b) (Af E))) → ∀ W : Submodule ℂ (Kinf E b → ℂ),
      FiniteDimensional ℂ W → ∀ q : (E →+* ℂ) → ℂ → Polynomial ℂ, (∀ τ u, q τ u ≠ 0) →
      ∃ V : Submodule ℂ (Sm E b), FiniteDimensional ℂ V ∧ ∀ ψ : Sm E b, (∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g) →
        (∀ k ∈ L, finRep E b k ψ = ψ) → (∀ g : GA E b, (fun k : Kinf E b => (cptRep E b k ψ).1 g) ∈ W) →
        (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ.1 (g * infGL E b y)‖ ≤ C * height y ^ N) →
        (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → ψ ∈ V := by
  intro E _ _ _ b hP L hL W hW q hq
  have hfin : FiniteDimensional ℂ (GlobalTheory.CapKilled.space E b L W q) :=
    GlobalTheory.T.tameKilledCapelliSpace_finiteDimensional_of_finiteness E b hP (GlobalTheory.T.capelliDet_eq_linearCombination_nat_nodes E b) L hL W hW q hq (_root_.GlobalTheory.CapKilled.zalg_mem_space E b L W hW q)
  refine ⟨GlobalTheory.CapKilled.space E b L W q, hfin, fun ψ h1 h2 h3 h4 h5 => ?_⟩
  let ν : Measure (Lie E b) := Measure.addHaar
  obtain ⟨α, hα, hlim⟩ := _root_.GlobalTheory.AutGrowth.ApproxId.exists_approx_identity E b ν
  let V' : Submodule ℂ (GA E b → ℂ) := (GlobalTheory.CapKilled.space E b L W q).map (Sm E b).subtype
  have hc : IsClosed (V' : Set (GA E b → ℂ)) := Submodule.closed_of_finiteDimensional V'
  have hM : ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q :=
    ⟨⟨⟨h1, h2⟩, h3⟩, GlobalTheory.CapKilled.mem_killed.2 h5⟩
  have hmem : ∀ n, smoothing ν (α n) ψ.1 ∈ V' := fun n => by
    obtain ⟨h, hv⟩ := _root_.GlobalTheory.CapKilledSmooth.smoothing_mem_space E b ν (α n) (hα n).1 (hα n).2 L W hW q ψ hM h4
    exact ⟨_, hv, rfl⟩
  have hψ : ψ.1 ∈ V' :=
    hc.mem_of_tendsto (tendsto_pi_nhds.2 fun g => hlim ψ.1 ψ.2 g) (Eventually.of_forall hmem)
  obtain ⟨χ, hχ, e⟩ := hψ
  have e' : χ = ψ := Subtype.ext e
  exact e' ▸ hχ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageOfMapEqOneOnInfFiniteIndex
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_image_of_map_eq_one_on_inf_finiteIndex :
    ∀ (G M : Type) [Group G] [Monoid M] (ρ : G →* M) (I H : Subgroup G), H.FiniteIndex →
      (∀ σ ∈ I, σ ∈ H → ρ σ = 1) → (ρ '' (I : Set G)).Finite := by
  intro G M _ _ ρ I H hH hρ
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  classical
  let f : G ⧸ H → M := fun q => if h : ∃ σ ∈ I, (σ : G ⧸ H) = q then ρ h.choose else 1
  apply (Set.finite_range f).subset
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨(σ : G ⧸ H), ?_⟩
  have h : ∃ τ ∈ I, (τ : G ⧸ H) = σ := ⟨σ, hσ, rfl⟩
  simp only [f, dif_pos h]
  obtain ⟨hτI, hτ⟩ := h.choose_spec
  rw [QuotientGroup.eq] at hτ
  have h1 : ρ (h.choose⁻¹ * σ) = 1 := hρ _ (I.mul_mem (I.inv_mem hτI) hσ) hτ
  calc ρ h.choose = ρ h.choose * ρ (h.choose⁻¹ * σ) := by rw [h1, _root_.mul_one]
    _ = ρ σ := by rw [← map_mul, _root_.mul_inv_cancel_left]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.MidBlock

section Alg

variable {A A' : Type} [Ring A] [Algebra ℂ A] [Ring A'] [Algebra ℂ A']

theorem qdet_map (φ : A →ₐ[ℂ] A') {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Function.comp_apply, map_add, apply_ite φ, AlgHom.commutes, map_zero]

theorem qdet_mem (S : Subalgebra ℂ A) {n : ℕ} {E : Fin n → Fin n → A} (h : ∀ a b, E a b ∈ S) (u : ℂ) :
    Formalism.REAL.qdet E u ∈ S := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (Subalgebra.list_prod_mem _ ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine Subalgebra.add_mem _ ?_ (h _ _)
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.zero_mem _

theorem comm_qdet {n : ℕ} {E : Fin n → Fin n → A} {z : A} (h : ∀ a b, Commute z (E a b)) (u : ℂ) :
    Commute z (Formalism.REAL.qdet E u) := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_right _ _ _ fun σ _ => Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Formalism.REAL.Tm
  exact Commute.add_right (GlobalTheory.CapHC.ite_algebraMap_comm _ _ _).symm (h _ _)

theorem glComm {n : ℕ} {X : Fin n → Fin n → A} (hX : Formalism.REAL.GlRel X) {a b c d : Fin n} (hbc : b ≠ c)
    (hda : d ≠ a) : Commute (X a b) (X c d) := by
  have h := hX a b c d
  rw [if_neg hbc, if_neg hda, sub_zero] at h
  exact sub_eq_zero.1 h

end Alg

section Stab

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ N, f x ∈ N}
  mul_mem' := fun ha hb x hx => ha _ (hb x hx)
  add_mem' := fun ha hb x hx => N.add_mem (ha x hx) (hb x hx)
  algebraMap_mem' := fun c x hx => by simpa [Module.algebraMap_end_apply] using N.smul_mem c hx

theorem mem_stab {N : Submodule ℂ M} {f : Module.End ℂ M} : f ∈ stab N ↔ ∀ x ∈ N, f x ∈ N := Iff.rfl

theorem upperSpan_maps {N K : Submodule ℂ M} {r m : ℕ} (Y : Fin (r + m) → Fin (r + m) → stab N)
    (hY : ∀ p q, ∀ x ∈ N, (Y (Fin.castAdd m p) (Fin.natAdd r q) : Module.End ℂ M) x ∈ K)
    {y : stab N} (hy : y ∈ GlobalTheory.CapHC.upperSpan Y) : ∀ x ∈ N, (y : Module.End ℂ M) x ∈ K := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, rfl⟩ := hy
    intro x hx
    exact hY p q _ (mem_stab.1 w.2 x hx)
  | zero => intro x _; simp
  | add a b _ _ ha hb => intro x hx; simpa using K.add_mem (ha x hx) (hb x hx)
  | smul c a _ ha => intro x hx; simpa using K.smul_mem c (ha x hx)

end Stab

section Main

end Main

end GlobalTheory.LeviHC.MidBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPointsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (K : Over S) (i : K ⟶ A) (c : ℕ), Mono i → IsFinite K.hom → Flat K.hom → i ^ c = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (y : Sp k ⟶ S) (z : Sp k), K.hom.finrank (y z) = Nat.card (Over.mk y ⟶ K) := by
  first | (exact @GlobalTheory.TorsionRank.finrank_eq_card) | (exact GlobalTheory.TorsionRank.finrank_eq_card) | (intros; apply GlobalTheory.TorsionRank.finrank_eq_card  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagUnipotentRadicalLeStandardParabolicUnipotentStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentRadical_le_standardParabolicUnipotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.FlagRad.unipFlag_le_unip | exact GlobalTheory.FlagRad.unipFlag_le_unip | (intros; apply GlobalTheory.FlagRad.unipFlag_le_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteFlatGeometricFibresOverBaseStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base : ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left := by
  first | (exact @GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (exact GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveSpMapOfDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_surjective_spMap_of_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → Flat (spMap (algebraMap R W)) ∧ Surjective (spMap (algebraMap R W)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hinj : Function.Injective (algebraMap R W) := by
    have h1 : (algebraMap W K').comp (algebraMap R W) = (algebraMap K K').comp (algebraMap R K) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have h2 : Function.Injective ((algebraMap K K').comp (algebraMap R K)) :=
      (algebraMap K K').injective.comp (IsFractionRing.injective R K)
    rw [← h1] at h2
    exact Function.Injective.of_comp h2
  have hfl : Module.Flat R W := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change a • x = 0 at hax
    rw [Algebra.smul_def] at hax
    rcases mul_eq_zero.1 hax with h0 | h0
    · exact absurd (hinj (h0.trans (map_zero _).symm)) ha0
    · simp [h0]
  have hloc : IsLocalHom (algebraMap R W) := by
    refine ((IsLocalRing.local_hom_tfae (algebraMap R W)).out 1 3).2 ?_
    rw [h]
  have hff : Module.FaithfullyFlat R W := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hrf : (algebraMap R W).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 hff
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R W))).2 hrf
  exact ⟨h1, h2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationUnconditional
section
namespace GlobalTheory

theorem geometricLemmaFiltration_unconditional : GlobalTheory.Published.GeometricLemmaFiltration :=
  CompanionTheory.Geo.geometricLemmaFiltration

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedQuotientMapFiniteFlatSurjectiveStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedQuotientMap_finite_flat_surjective : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A G : Over S) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) →
    (∀ j, IsFinite (q j).left) → (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) →
    IsFinite Q.left ∧ Flat Q.left ∧ Surjective Q.left := by
  first | (exact @GlobalTheory.QuotGlue.finite_flat_surjective) | (exact GlobalTheory.QuotGlue.finite_flat_surjective) | (intros; apply GlobalTheory.QuotGlue.finite_flat_surjective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodStableOfIrr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.GoodStableDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare GlobalTheory.BI

theorem isChar_dual {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]


open Formalism.L2.DIV in
theorem coeff_idemOf_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hrec : R.grp_record) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (g : G) :
    (idemOf A.X).coeff g⁻¹ = (idemOf A.X).coeff g := by
  obtain ⟨eR, plg, iso, h1, -, -⟩ := hrec
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  apply D.what₂.embLL.injective
  rw [h1, h1, ← hφ, ← hφ, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ (φ g) (φ g⁻¹)
    (fun v _ => by rw [map_inv, Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)


open Formalism.L2.DIV in
theorem goodStable_of_irr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hirr : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hG : R.IsGrp F) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hI : IdemTie D om) : GoodStable A.X := by
  classical
  have hsym := coeff_idemOf_inv R hG.record hI
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hirr A.X
    (fun ψ g => D.what₂.embLL (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hirr ψ hψ)
      exact isChar_dual ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
        map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply D.what₂.embLL.injective
  simpa using hψe g⁻¹

end GlobalTheory.GoodStableDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCardKilledByIdealEqAbsNormPowStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ o.A // GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) y} = Ideal.absNorm 𝔟 ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (exact GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow) | (intros; apply GlobalTheory.HTTorsCount.card_killedBy_eq_absNorm_pow <;> assumption)
end

