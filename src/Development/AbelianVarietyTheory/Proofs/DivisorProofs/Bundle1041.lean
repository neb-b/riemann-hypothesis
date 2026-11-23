module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Formalism.PieriBlockIdeals.PieriColumnMinors.DepthNonnegative
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh


set_option maxHeartbeats 1000000 in
theorem models_at_record_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.toCore.σ₀ → ∀ k : (T.U ((i : ℕ) + 1) σ).Comp, IsMod (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) ∧ IsONFr ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) ∧ IsInvOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (cart (R.MW i (sg0 D A))) ∧ ((T.U ((i : ℕ) + 1) σ).X k).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q ∧ (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q ∧ 1 ≤ D.R.r ∧ (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ ((T.U ((i : ℕ) + 1) σ).X k).Ψ ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0) ∧ (∀ hq : ((T.U ((i : ℕ) + 1) σ).X k).p0 + (T.Q.Dw ((i : ℕ) + 1)).p = D.R.r, IsBasOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) hq (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (onb (R.MW i (sg0 D A)))) ∧ Dom (wtA (κ i)) (Vc D i).rank ∧ (κ i).n = (Vc D i).rank ∧ LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i σ hσ k
  subst hσ
  have hj := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  have hP := hL.pins
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hdq : (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 := (hP.2.2.2 _ hj).2.1
  have hp0 := (hU.2.1 k).1
  have hΨ := (hU.2.1 k).2
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hC.models.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k) := by
    obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hg
    have hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i := hL.spaceW _ hj _ hg
    have h1 := hm k
    revert hr
    rw [hV]
    exact fun _ _ h => h
  have hn : (κ i).n = (Vc D i).rank := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨τ', hτ'⟩ : ∃ τ', τ' ∈ ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ ∈ ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ, (((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).cmType τ).2 h⟩
    obtain ⟨t, -⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ' ((hΨ τ').1 hτ')
    rw [(hT.kap i t).2.2, D.sp.V_rank _ hj.1 hj.2]
  refine ⟨⟨hM, fun τ => ?_, ?_⟩, fun τ => hL.familyUniformisationBasePointOrthogonal _ hj _ hg k τ.1 τ.2, ?_, hp0, hU.1, ?_, hr1, hP.1.2.1, hΨ,
    fun hq => isBasOf_onb _ _ _ hx hq hε, hn ▸ dom_wtA (κ i), hn,
    lastPos_wtA_of_pins T.Q hP hj _ (lastPos_of_kapIs hT.kap i)⟩
  · rw [hΨ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).κ0 = 2 * ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hg) hU' hr1 w k).1
    rw [h1, hM.2, mul_neg]
  · exact isInvOf_cart _ _ _ hx (by have := hU.1; omega) hε
  · rw [hdp, hdq]
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleFiniteFrameLatticeForms
section
set_option autoImplicit false

open GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.UG Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD

namespace GlobalTheory.ExpFrame

theorem finite_forms_of_classes {O : Type} [CommRing O] {W : Type} [AddCommGroup W] [Module O W] [IsNoetherian O W]
    {G : Type} [Group G] (Γ K : Subgroup G) (ρ : Representation O K W)
    (h : ∃ S : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ κ ∈ K, g = γ * s * κ) : Module.Finite O (AMFK O Γ K ρ) := by
  obtain ⟨S, hS⟩ := h
  let ev : AMFK O Γ K ρ →ₗ[O] (S → W) :=
    (LinearMap.funLeft O W (Subtype.val : S → G)).comp (AMFK O Γ K ρ).subtype
  refine Module.Finite.of_injective ev ?_
  intro f f' hff
  ext g
  obtain ⟨γ, hγ, s, hs, κ, hκ, rfl⟩ := hS g
  have h1 := f.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h2 := f'.2 ⟨γ, hγ⟩ s ⟨κ, hκ⟩
  have h3 : (f : G → W) s = (f' : G → W) s := congrFun hff ⟨s, hs⟩
  exact h1.trans ((congrArg _ h3).trans h2.symm)

theorem Frame.finite_latticeForms : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N mu), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N mu) F.Γ jK (NablaT F.O N mu)) := by
  intro l _ ι _ _ N F mu jK hF
  have : ∀ τ : ι, Module.Finite F.O (dualWeyl F.O N N (res N (mu τ))) :=
    fun τ => dualWeyl_module_finite F.O N N _
  have : IsNoetherian F.O (NablaT F.O N mu) := inferInstance
  exact finite_forms_of_classes F.Γ F.K _ hF.classes

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
section
noncomputable section

open NumberField GlobalTheory.BCT GlobalTheory.CuspRep Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def mulMat (a : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)).map e

def gram (β : B.A) : Matrix (Fin m) (Fin m) (w.adicCompletion E) :=
  Matrix.of fun i j => e (B.herm β (b i) (b j))

def dlt (β : B.A) : GLw m w :=
  if h : IsUnit (gram e b β) then invT m _ h.unit * (PhiU m _)⁻¹ else 1

def lat (g : GLw m w) : Submodule K.O B.A :=
  Submodule.span K.O (Set.range fun j => ∑ i, e.symm (g.val i j) • b i)

end GlobalTheory.TwLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory

theorem nat_le_four_of_dvd_of_embeddings_le_four :
    ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  intro F _ _ y m r hy hyr hφ
  set d := Module.finrank ℚ F with hd
  have hr : (r : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, mul_zero]
  have hm : (m : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, zero_mul]
  have hN : Algebra.norm ℚ y = (m : ℚ) ^ d * (Algebra.norm ℤ r : ℚ) := by
    rw [hyr, map_mul, Algebra.coe_norm_int]
    congr 1
    rw [show ((m : F)) = algebraMap ℚ F (m : ℚ) by simp, Algebra.norm_algebraMap]
  have hr0 : (Algebra.norm ℤ r : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]; exact (Algebra.norm_ne_zero_iff).2 hr
  have hr1 : (1 : ℝ) ≤ |((Algebra.norm ℤ r : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Int.one_le_abs this
  have hlow : (m : ℝ) ^ d ≤ |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    rw [hN]; push_cast
    rw [abs_mul, abs_pow, Nat.abs_cast]
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) d]
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have hup : |((Algebra.norm ℚ y : ℚ) : ℝ)| ≤ 4 ^ d := by
    have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ y)‖ = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
      simp
    rw [← h1, hprod, norm_prod]
    calc ∏ σ : F →ₐ[ℚ] ℂ, ‖σ y‖ ≤ ∏ _σ : F →ₐ[ℚ] ℂ, (4 : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun σ _ => hφ σ.toRingHom)
      _ = 4 ^ d := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have : (m : ℝ) ≤ 4 := (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by norm_num) hd0).1 (hlow.trans hup)
  exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelOfPresents
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.Presents

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ}

def genChart (h : Presents D L r) : L.ι := (exists_chart h.isLB (genericPoint X)).choose

theorem gen_mem_genChart (h : Presents D L r) : genericPoint X ∈ L.U h.genChart :=
  (exists_chart h.isLB (genericPoint X)).choose_spec

def secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(LB.toMod L, U) →+ X.functionField :=
  AddMonoidHom.mk' (fun s => fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField)) fun s t => by
    rw [LB.coord_add, map_add (f := _), add_div]

theorem secVal_apply (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U)) :
    h.secVal U hU s = fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField) := rfl

theorem secVal_mul (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U))
    (i : L.ι) (hi : genericPoint X ∈ U ⊓ L.U i) :
    h.secVal U hU s * r i = fnOf _ hi (LB.coord s i) := by
  have h₀ := h.gen_mem_genChart
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U h.genChart := ⟨hi, h₀⟩
  have e := congrArg (fnOf _ hW) (LB.coord_rel s i h.genChart
    (inf_le_left : U ⊓ L.U i ⊓ L.U h.genChart ≤ U ⊓ L.U i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e
  rw [e, secVal_apply, h.isRatSec i h.genChart (memInf hi.2 h₀), mul_left_comm]
  exact congrArg _ (div_mul_cancel₀ _ (Units.ne_zero _))

theorem secVal_injective (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective (h.secVal U hU) := fun s t e =>
  LB.sec_ext fun i => fn_ext fun hi => by rw [← h.secVal_mul U hU s i hi, ← h.secVal_mul U hU t i hi, e]

theorem mem_range_secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (f : X.functionField) :
    f ∈ (h.secVal U hU).range ↔ ∀ y ∈ U, D.RegularAt y f := by
  constructor
  · rintro ⟨s, rfl⟩ y hy
    obtain ⟨i, hi⟩ := exists_chart h.isLB y
    have hyi : y ∈ U ⊓ L.U i := ⟨hy, hi⟩
    refine (h.isEqn i y hi).regularAt_iff.2 ?_
    rw [h.secVal_mul U hU s i (gen_mem hyi)]
    exact regAt_fnOf hyi _ _
  · intro hf
    have key (i : L.ι) : ∃ a : Γ(X, U ⊓ L.U i), ∀ hi, fnOf _ hi a = f * r i := by
      by_cases hi : genericPoint X ∈ U ⊓ L.U i
      · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
          (h.isEqn i x hx.2).regularAt_iff.1 (hf x hx.1)
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h' => (hi h').elim⟩
    choose a ha using key
    have hmem : a ∈ secOn L U := fun i j => fn_ext fun hij => by
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha,
        h.isRatSec i j (memInf hij.1.2 hij.2), mul_left_comm]
    refine ⟨LB.mkSec a hmem, ?_⟩
    rw [secVal_apply, LB.coord_mkSec, ha]
    exact mul_div_cancel_right₀ _ (Units.ne_zero _)

def latModel (h : Presents D L r) :
    LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L) where
  val := h.secVal
  inj := h.secVal_injective
  range U hU := by
    ext f
    rw [h.mem_range_secVal U hU f]
    simp only [latSec, AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, CartierDiv.mem_secOn,
      Set.mem_singleton_iff, forall_eq]
  res U W e hW s := by
    rw [secVal_apply, secVal_apply, LB.coord_map, fnOf_resG]
  smul U hU a s := by
    rw [secVal_apply, secVal_apply, LB.coord_smul, map_mul, fnOf_resG, smul_eq_mul, mul_div_assoc]

end GlobalTheory.Cartier.Presents

theorem GlobalTheory.Cartier.nonempty_latModel_of_presents : ∀ (X : Scheme.{0}) [IsIntegral X] (D : CartierDiv X) (L : LB X)
    (r : L.ι → X.functionFieldˣ), Presents D L r →
    Nonempty (LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L)) :=
  fun _ _ _ _ _ h => ⟨h.latModel⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {L : LB X} {r : L.ι → X.functionFieldˣ}

theorem sec_eq_of_not_gen {W : X.Opens} (hW : genericPoint X ∉ W) (s t : Γ(F, W)) : s = t :=
  sec_ext_of_cover (ι := PEmpty.{1}) (fun k => k.elim) (fun k => k.elim)
    (by intro x hx; exact (hW (gen_mem hx)).elim) (fun k => k.elim)

theorem val_resM (hM : LatModel M F) {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W)
    (s : Γ(F, U)) : hM.val W h (resM F e s) = hM.val U (e h) s :=
  hM.res U W e h s


variable (r) in
def tval (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) : Γ(twist F L, U) →+ V where
  toFun s := (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i)
  map_zero' := by rw [coord_zero, map_zero, smul_zero]
  map_add' s t := by rw [coord_add, map_add (f := _), smul_add]

theorem tval_apply (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(twist F L, U)) :
    tval r hM i hi U h s = (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i) := rfl

theorem val_coord_rel (hM : LatModel M F) {U : X.Opens} (s : Γ(twist F L, U)) (i j : L.ι)
    (hU : genericPoint X ∈ U) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    hM.val (U ⊓ L.U i) (memInf hU hi) (coord s i) =
      fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        hM.val (U ⊓ L.U j) (memInf hU hj) (coord s j) := by
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := memInf (memInf hU hi) hj
  have e := coord_rel s i j (W := U ⊓ L.U i ⊓ L.U j) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_inf_right _ inf_le_right)
  have e1 := val_resM hM (inf_le_left : U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U i) hW (coord s i)
  have e2 := val_resM hM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U j) hW (coord s j)
  rw [← e1, ← e2, e, hM.smul, fnOf_resG]

theorem tval_eq (hM : LatModel M F) (hr : IsRatSec L r) {U : X.Opens} (h : genericPoint X ∈ U)
    (i j : L.ι) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j)
    (s : Γ(twist F L, U)) : tval r hM i hi U h s = tval r hM j hj U h s := by
  rw [tval_apply, tval_apply, val_coord_rel hM s i j h hi hj, Units.smul_def, Units.smul_def,
    smul_smul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j (memInf hi hj)]
  congr 1
  have hg : fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 :=
    ((L.g i j).isUnit.map (fnOf (L.U i ⊓ L.U j) (memInf hi hj))).ne_zero
  have hrj : (r j : X.functionField) ≠ 0 := (r j).ne_zero
  field_simp

end LatTwist

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {D : CartierDiv X} {L : LB X}
  {r : L.ι → X.functionFieldˣ}

theorem mem_of_mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : v ∈ latSec N U)
    {y : X} (hy : y ∈ U) : v ∈ N y :=
  AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv y) hy

theorem mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : ∀ y ∈ U, v ∈ N y) :
    v ∈ latSec N U :=
  AddSubgroup.mem_iInf.2 fun y => AddSubgroup.mem_iInf.2 fun hy => hv y hy

def twistModel (hP : Presents D L r)
    (hE : ∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y))
    (hM : LatModel M F) (i₀ : L.ι) (hi₀ : genericPoint X ∈ L.U i₀) :
    LatModel M' (twist F L) where
  val U h := tval r hM i₀ hi₀ U h
  inj U h := by
    intro s t e
    refine sec_ext fun i => ?_
    by_cases hi : genericPoint X ∈ L.U i
    · have e' : tval r hM i hi U h s = tval r hM i hi U h t := by
        rw [← tval_eq hM hP.isRatSec h i₀ i hi₀ hi, ← tval_eq hM hP.isRatSec h i₀ i hi₀ hi]
        exact e
      rw [tval_apply, tval_apply] at e'
      exact hM.inj (U ⊓ L.U i) (memInf h hi) (MulAction.injective _ e')
    · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i => hi hh.2) _ _
  range U h := by
    ext v
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine mem_latSec fun y hy => ?_
      obtain ⟨i, hi⟩ := exists_chart hP.isLB y
      have hgi : genericPoint X ∈ L.U i := gen_mem hi
      rw [tval_eq hM hP.isRatSec h i₀ i hi₀ hgi, hE y (r i) _ (hP.isEqn i y hi), tval_apply,
        ← Units.smul_def, smul_inv_smul]
      have hw : hM.val (U ⊓ L.U i) (memInf h hgi) (coord s i) ∈ (hM.val (U ⊓ L.U i) (memInf h hgi)).range :=
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hM.range] at hw
      exact mem_of_mem_latSec hw (memInf hy hi)
    · intro hv
      have key : ∀ i, ∃ t : Γ(F, U ⊓ L.U i),
          ∀ hi : genericPoint X ∈ L.U i, hM.val (U ⊓ L.U i) (memInf h hi) t = r i • v := by
        intro i
        by_cases hi : genericPoint X ∈ L.U i
        · have hm : r i • v ∈ latSec M (U ⊓ L.U i) := mem_latSec fun y hy => by
            rw [Units.smul_def, ← hE y (r i) v (hP.isEqn i y hy.2)]
            exact mem_of_mem_latSec hv hy.1
          rw [← hM.range (U ⊓ L.U i) (memInf h hi)] at hm
          obtain ⟨t, ht⟩ := hm
          exact ⟨t, fun _ => ht⟩
        · exact ⟨0, fun h' => (hi h').elim⟩
      choose t ht using key
      have hmem : t ∈ Twist.secGroup F L U := by
        intro i j
        by_cases hij : genericPoint X ∈ L.U i ⊓ L.U j
        · have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := (memInf (memInf h hij.1) hij.2)
          apply hM.inj (U ⊓ L.U i ⊓ L.U j) hW
          rw [hM.smul, val_resM, val_resM, fnOf_resG, ht i hij.1, ht j hij.2, Units.smul_def,
            Units.smul_def, smul_smul, hP.isRatSec i j hij]
        · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j => hij (memInf hh.1.2 hh.2)) _ _
      exact ⟨mkSec t hmem, by rw [tval_apply, coord_mkSec, ht i₀ hi₀, inv_smul_smul]⟩
  res U W e h s := by
    change tval r hM i₀ hi₀ W h (resM (twist F L) e s) = tval r hM i₀ hi₀ U (e h) s
    rw [tval_apply, tval_apply, coord_resM, val_resM]
  smul U h a s := by
    change tval r hM i₀ hi₀ U h (a • s) = fnOf U h a • tval r hM i₀ hi₀ U h s
    rw [tval_apply, tval_apply, coord_smul, hM.smul, fnOf_resG, Units.smul_def, Units.smul_def,
      smul_smul, smul_smul, mul_comm]

end LatTwist

theorem nonempty_latModel_twist : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M M' : X → AddSubgroup V) (F : X.Modules) (D : CartierDiv X)
    (L : LB X) (r : L.ι → X.functionFieldˣ), Presents D L r →
    (∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y)) →
    LatModel M F → Nonempty (LatModel M' (twist F L)) := by
  intro X _ V _ _ M M' F D L r hP hE hM
  obtain ⟨i₀, hi₀⟩ := exists_chart hP.isLB (genericPoint X)
  exact ⟨LatTwist.twistModel hP hE hM i₀ hi₀⟩

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicDenominatorBound
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_denominator_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  first | (exact @GlobalTheory.AtP.main) | (exact GlobalTheory.AtP.main) | (intros; apply GlobalTheory.AtP.main <;> assumption)
end

