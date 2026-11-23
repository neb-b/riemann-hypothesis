module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensSpanOfKilled
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR MvPolynomial

namespace GlobalTheory.HoweR

theorem coinv_stab_snd (P Q R S : ℕ) (x : ℂ) : Stab (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro Z y hy
  have hcomm := (_root_.GlobalTheory.HoweR.fock_lie_wts_comm P Q R S).2.2.2.2
  induction hy using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨X, f, rfl⟩ := hg
    refine Submodule.subset_span ⟨X, fockAct2 P Q R S Z f, ?_⟩
    rw [map_sub, map_smul, hcomm]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem degW_le_of_abs_le {p q : ℕ} (c : ℚ) (μ : Ix p q → ℚ) (B : ℚ) (hμ : ∀ a, |μ a| ≤ B) :
    degW c μ ≤ ((p + q : ℕ) : ℚ) * (B + |c|) := by
  unfold degW
  have h : ∀ a, |shiftNu c μ a| ≤ B + |c| := by
    intro a
    rcases a with i | j
    · simp only [shiftNu]; exact (abs_sub _ _).trans (add_le_add (hμ _) le_rfl)
    · simp only [shiftNu]; exact (abs_add_le _ _).trans (add_le_add (hμ _) le_rfl)
  calc ∑ a, |shiftNu c μ a| ≤ ∑ _a : Ix p q, (B + |c|) := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [Finset.card_univ, Fintype.card_sum]; ring

theorem fockCoinvariantKernel_highestWeight_admissible (P Q R S : ℕ) (x : ℂ) : AdmMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro B
  refine ⟨restrictTotalDegree (Ln P Q R S) ℂ ⌊((R + S : ℕ) : ℚ) * (B + |cPair P Q|)⌋₊, inferInstance, ?_⟩
  intro μ hμ v hv
  obtain ⟨-, hL2, -, hw2, -⟩ := _root_.GlobalTheory.HoweR.fock_lie_wts_comm P Q R S
  have hgood : Good (fockAct2 P Q R S) := ⟨hL2, hw2, _root_.GlobalTheory.HoweR.fock_locU P Q R S⟩
  obtain ⟨hspan, -, hK2, -⟩ := GlobalTheory.FockAlg.harm_graded_stable P Q R S _ (Or.inr (Or.inl rfl))
  have hKc : KStable (fockAct2 P Q R S) (coinv P Q R S x) := fun X _ w hw => coinv_stab_snd P Q R S x X w hw
  have hv' : v ∈ (Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x) ⊓ hwSub (fockAct2 P Q R S) μ :=
    ⟨by rw [_root_.GlobalTheory.HoweR.span_harm2_sup_coinv_eq_univ]; exact Submodule.mem_top, hv⟩
  have hsplit := GlobalTheory.T.howeHighestWeight_sup_stable_le R S _ (fockAct2 P Q R S) hgood _ _ hK2 hKc μ hv'
  obtain ⟨h, hh, c, hc, rfl⟩ := Submodule.mem_sup.1 hsplit
  refine Submodule.add_mem_sup ?_ hc.1
  rw [mem_restrictTotalDegree]
  have hh2 : h ∈ harm2 P Q R S := by rw [← hspan]; exact hh.1
  exact (GlobalTheory.DegKeep.deg_le_of_harm hh2 hh.2).trans (Nat.floor_mono (degW_le_of_abs_le _ μ B hμ))

theorem coinv_stab_adm : ∀ (P Q R S : ℕ) (x : ℂ),
    Stab (fockAct2 P Q R S) (coinv P Q R S x) ∧ AdmMod (fockAct2 P Q R S) (coinv P Q R S x) :=
  fun P Q R S x => ⟨coinv_stab_snd P Q R S x, fockCoinvariantKernel_highestWeight_admissible P Q R S x⟩

end GlobalTheory.HoweR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
section
noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine AlgebraicGeometry GlobalTheory.CompHt GlobalTheory.FlatCore

theorem framesOn_eq_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∃ k, framesOn (U σ) Z = {z | z.1 = k ∧ z.2 ∈ ((U σ).X z.1).dom} := by
  intro E _ _ _ H Dw l Xo c r U x hL Z σ hσ
  obtain ⟨q, hq⟩ : ∃ q : (U σ).Comp ≃ Comp Xo c, ∀ k (y : ((U σ).X k).dom) (s : Sp (CAt σ)),
      ptF ((U σ).un k y) s ∈ (q k).1 :=
    GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ r (Formalism.L2.PjFree.Unf.ofPj (U σ)) hσ (hL.unf σ hσ)
      (fun k => GlobalTheory.CompBij.frames_nonempty _) hL.geo
  refine ⟨q.symm Z, Set.ext fun ⟨k, y⟩ => ⟨?_, ?_⟩⟩
  · rintro ⟨hy, hl⟩
    refine ⟨?_, hy⟩
    have hk : q k = Z := by
      by_contra hne
      let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) (hq k ⟨y, hy⟩ s) (hl s)
    exact (Equiv.eq_symm_apply q).2 hk
  · rintro ⟨hk, hy⟩
    obtain rfl : k = q.symm Z := hk
    refine ⟨hy, fun s => ?_⟩
    have := hq (q.symm Z) ⟨y, hy⟩ s
    rwa [Equiv.apply_symm_apply] at this

end GlobalTheory.FlatCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoActOfTiesOfEquivAll
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem geoAct_of_ties_of_equivAll : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → EquivAll T R κ O → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hl hi hw ht hpb hp he
  exact _root_.GlobalTheory.geoAct_of_eqAt T R κ v₀ O hi hw ht hp fun i σ hσ hV =>
    he i σ hσ hV (_root_.GlobalTheory.EquivConst.exists_equivariant_constants T R κ v₀ O hl ht hpb hp i σ hσ hV)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIrrGLTransportAlongFieldIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RecTTransport.good_of_repRel : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → UpperTheory.Zero.LLC.Good x → UpperTheory.Zero.LLC.Good x' :=
  GlobalTheory.GoodTransport.good_transport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DiagUniq

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

theorem glue_shiftOf (x : κ → AF F) : glue (shiftOf x) = x := by
  have h := glue_add_shiftOf (0 : Vi F κ × Vf F κ) x
  rwa [zero_add, GlobalTheory.DiagNonvan.glue_zero, zero_add] at h

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  refine (eI F κ).injective ?_
  show eI F κ ((eI F κ).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AF F) → Vi F κ × Vf F κ) :=
  ((eI F κ).symm.continuous.comp (continuous_pi fun i =>
    continuous_toMixed.comp (continuous_fst.comp (continuous_apply i)))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))


variable (F κ) in
def glueE : (Vi F κ × Vf F κ) ≃ₜ+ (κ → AF F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := GlobalTheory.DiagNonvan.glue_add
  continuous_toFun := GlobalTheory.DiagNonvan.continuous_glue
  continuous_invFun := continuous_shiftOf

theorem lDiag_eq (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), lDiag F κ Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : ((mu F κ).map (glueE F κ)).IsAddHaarMeasure := (glueE F κ).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueE F κ)) μ
  refine ⟨((Measure.addHaarScalarFactor ((mu F κ).map (glueE F κ)) μ : ℝ) : ℂ), fun Φ hΦ => ?_⟩
  have e := (glueE F κ).toHomeomorph.measurableEmbedding.integral_map (μ := mu F κ) (fun u => Φ (Sum.elim u u))
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD hΦ)]
  refine e.symm.trans ?_
  change ∫ u, Φ (Sum.elim u u) ∂((mu F κ).map (glueE F κ)) = _
  conv_lhs => rw [h]
  rw [integral_smul_nnreal_measure]
  rfl


variable (F κ) in
def diagL : ((κ → F) × (κ → F)) →ₗ[F] ((κ ⊕ κ → F) × (κ ⊕ κ → F)) where
  toFun p := (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2))
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [add_comm]
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

omit [NumberField F] [Fintype κ] in
theorem diagL_injective : Function.Injective (diagL F κ) := by
  intro p q h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrFun (congrArg Prod.fst h) (Sum.inl i)
  · exact congrFun (congrArg Prod.snd h) (Sum.inl i)

theorem eq_mul_diagInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro F _ _ ψ hψ κ _ l hl hinv μ hμ
  have key : ∀ l' : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l' (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l' Φ) →
      ∀ (t : AF F), ∀ w ∈ LinearMap.range (diagL F κ), ∀ φ ∈ schA F (κ ⊕ κ),
        l' (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    rintro l' h t _ ⟨p, rfl⟩ φ hφ
    have e : t • ((fun i => algebraMap F (AF F) ((diagL F κ p).1 i)), (fun i => algebraMap F (AF F) ((diagL F κ p).2 i))) =
        (Sum.elim (fun i => t * algebraMap F (AF F) (p.1 i)) (fun i => t * algebraMap F (AF F) (p.1 i)),
          Sum.elim (fun i => t * algebraMap F (AF F) (p.2 i)) (-fun i => t * algebraMap F (AF F) (p.2 i))) := by
      refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [diagL]
    rw [e]
    exact h _ _ φ hφ
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.AdelicSvN.main F ψ hψ (κ ⊕ κ) (LinearMap.range (diagL F κ))
    (by
      rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
      simp [diagL, dotProduct, Fintype.sum_sum_type])
    (by
      rw [LinearMap.finrank_range_of_inj diagL_injective]
      simp)
    l hl (lDiag F κ) lDiag_adm (key l hinv) (key _ fun x y Φ hΦ => lDiag_schr ψ x y hΦ) exists_lDiag_ne
  obtain ⟨d, hd⟩ := lDiag_eq μ hμ
  exact ⟨c * d, fun Φ hΦ => by rw [hc Φ hΦ, hd Φ hΦ, mul_assoc]⟩

end GlobalTheory.DiagUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HwSubStableOfComm
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem hwSub_stable_of_comm {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (f : Module.End ℂ V)
    (hf : ∀ Z v, f (act Z v) = act Z (f v)) (μ : Ix p q → ℚ) :
    ∀ v ∈ hwSub act μ, f v ∈ hwSub act μ := by
  intro v hv
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have := congrArg f (h1 a)
    simpa [hf, map_sub, map_smul] using this
  · rw [← hf, h2 a b hab, map_zero]

theorem hw_joint_split : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) →
    ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') →
    ∀ μ : ∀ w, Ix (R w) (S w) → ℚ,
    (N ⊔ N') ⊓ (⨅ w, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w, hwSub (a w) (μ w)) := by
  intro T _ _ R S V _ _ a hg hc N N' hN hN' μ
  have key : ∀ s : Finset T, (N ⊔ N') ⊓ (⨅ w ∈ s, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih =>
      set H := ⨅ w ∈ s, hwSub (a w) (μ w) with hH
      have hHst : ∀ X, ∀ v ∈ H, a w X v ∈ H := by
        intro X v hv
        rw [hH, Submodule.mem_iInf] at hv ⊢
        intro w'
        have hv' := hv w'
        rw [Submodule.mem_iInf] at hv' ⊢
        intro hw'
        have hne : w ≠ w' := fun h => hws (h ▸ hw')
        exact hwSub_stable_of_comm (a w') (a w X) (fun Z u => hc w w' hne X Z u) (μ w') v (hv' hw')
      have hK : ∀ M : Submodule ℂ V, (∀ Z, ∀ y ∈ M, a w Z y ∈ M) → KStable (a w) (M ⊓ H) := by
        intro M hM X _ v hv
        exact Submodule.mem_inf.mpr ⟨hM X v (Submodule.mem_inf.mp hv).1, hHst X v (Submodule.mem_inf.mp hv).2⟩
      have hsp := GlobalTheory.T.howeHighestWeight_sup_stable_le (R w) (S w) V (a w) (hg w) (N ⊓ H) (N' ⊓ H) (hK N (hN w)) (hK N' (hN' w)) (μ w)
      rw [Finset.iInf_insert]
      calc (N ⊔ N') ⊓ (hwSub (a w) (μ w) ⊓ H) = ((N ⊔ N') ⊓ H) ⊓ hwSub (a w) (μ w) := by
              rw [inf_comm (hwSub (a w) (μ w)) H, inf_assoc]
        _ ≤ ((N ⊓ H) ⊔ (N' ⊓ H)) ⊓ hwSub (a w) (μ w) := inf_le_inf_right _ ih
        _ ≤ ((N ⊓ H) ⊓ hwSub (a w) (μ w)) ⊔ ((N' ⊓ H) ⊓ hwSub (a w) (μ w)) := hsp
        _ = (N ⊓ (hwSub (a w) (μ w) ⊓ H)) ⊔ (N' ⊓ (hwSub (a w) (μ w) ⊓ H)) := by
              rw [inf_assoc, inf_assoc, inf_comm H]
  simpa using key Finset.univ

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityTransportsComponentToItself
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lact_one_self {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ) = y τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

theorem isTransp_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp), IsTransp p r i v ψ 1 k k 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hm r h ho i v ψ k
  have hl := h.laws v
  obtain ⟨-, hA, -, -, -, -, hj⟩ := GlobalTheory.PinNum.numerics_of_pins D (r.used v).full.Q hl.p.pins
  obtain ⟨hpq, hr, -⟩ := hj ((i : ℕ) + 1) ⟨by omega, by omega⟩
  have hL := GlobalTheory.FullLevelAction.actLev_levFull D (r.used v).full.Q ((i : ℕ) + 1) (by rw [hpq]; exact hr) hA
  refine ⟨GlobalTheory.LevelCusp.isMatch_of_isUStab _ ⟨fun x y => by simp, fun x => by simp⟩, fun x hx => ?_, fun w => ?_⟩
  · have e : castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x) = x := by
      rw [lact_one_self]; rfl
    refine ⟨by rw [e]; exact hx, 1, ?_⟩
    have ey : (uAt r v i).un k ⟨castFrame (rfl : ((uAt r v i).X k).Ψ = ((uAt r v i).X k).Ψ) (lact 1 x), by rw [e]; exact hx⟩ =
        (uAt r v i).un k ⟨x, hx⟩ := congrArg _ (Subtype.ext e)
    have hf := hL.func 1 _ ((uAt r v i).un k ⟨x, hx⟩) ((uAt r v i).un k ⟨x, hx⟩)
      (mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩))
      (hL.one _ _) (Formalism.L2.Pj.mvPt_spec hL.total 1 _)
    have hy : (uAt r v i).un k ⟨x, hx⟩ =
        mvLev ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c 1 ((uAt r v i).un k ⟨x, hx⟩) :=
      (GlobalTheory.LevelLawsCompare.frMap_id_iff _ _).1 hf
    rw [ey]
    exact (congrArg (FrBor 1 ((uAt r v i).un k ⟨x, hx⟩)) hy).mp (GlobalTheory.ShFam.Descent.frBor_one _)
  · have hw : Matrix.mulVec ((1 : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (w : Fin D.R.r → D.host.E) ∈ ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.lattice₂ D ((uAt r v i).X k).Λ := by
      rw [Units.val_one, Matrix.one_mulVec]; exact w.2
    refine ⟨hw, ?_⟩
    calc Submodule.Quotient.mk ⟨_, hw⟩ = Submodule.Quotient.mk w :=
          congrArg _ (Subtype.ext (Matrix.one_mulVec _))
      _ = ψ k ((ψ k).symm (Submodule.Quotient.mk w)) := ((ψ k).apply_symm_apply _).symm
      _ = _ := rfl
end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProductStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_definiteUnitary_restricted_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) → IsCompact {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  first | exact @GlobalTheory.BCT.LocCpt.loc_cpt | exact GlobalTheory.BCT.LocCpt.loc_cpt | (intros; apply GlobalTheory.BCT.LocCpt.loc_cpt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobHecke

theorem isHecke_globFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f →
    IsHecke (globLev S K') (globFn S f) := by
  intro E _ _ _ hU n _ S hS K' hK' f hf
  refine ⟨?_, globFn_inv S K' f fun w => (hf.1 w).2⟩
  have hC : ∀ᶠ w in cofinite, tsupport (f w) = (KL n w : Set (UL n w)) := by
    filter_upwards [hK'.2, hf.2] with w h1 h2
    have ho : IsOpen (KL n w : Set (UL n w)) := h1 ▸ (hK'.1 w).1
    have hc : IsClosed (KL n w : Set (UL n w)) := Subgroup.isClosed_of_isOpen _ ho
    rw [h2, tsupport, Set.support_indicator]
    have : Function.support (1 : UL n w → ℂ) = Set.univ := by
      ext x; simp
    rw [this, Set.inter_univ, hc.closure_eq]
  have hcpt := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => tsupport (f w)) (fun w => (hf.1 w).1) hC
  set_option synthInstance.maxHeartbeats 200000 in
  refine HasCompactSupport.intro hcpt fun x hx => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  have hfin : (S ∩ Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf.2
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u ⟨-, hu⟩ ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  rw [finprod_mem_eq_prod _ hfin]
  have h0 : f w (toSub (UL n w) (cLoc w (x : UA E n))) = 0 := image_eq_zero_of_notMem_tsupport hxw
  refine Finset.prod_eq_zero (i := w) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw, ?_⟩
  show f w _ ≠ 1
  rw [h0]
  exact zero_ne_one

end GlobalTheory.BCT.GlobHecke
end

