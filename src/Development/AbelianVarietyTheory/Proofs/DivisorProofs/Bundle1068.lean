module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeightDescentMinors
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
public import Formalism.LocalToGlobal.NumberFieldFamilies.IdTransSM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusMatrixCofactorEqQPowFrame
section
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace.FrameHeight

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}
    (W : LocWach PD LL O v f)

theorem φD_smul_A (T : LocLat G Qp LL O) (a : LetA O f) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O f) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

theorem φpull_le_span {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) :
    W.φpull T ≤ Submodule.span (LetA O f) (Set.range fun j => W.φD T (b j : W.DD T)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [φD_smul_A]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_inv {n : ℕ} (T : LocLat G Qp LL O) (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T))
    (PA : Matrix (Fin n) (Fin n) (LetA O f))
    (hφ : ∀ k, W.φD T (b k : W.DD T) = ∑ m, PA m k • (b m : W.DD T)) (h : ℕ) (i : ZMod f)
    (h5 : ∀ y ∈ W.Nl T i, W.Q ^ h • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1))) :
    ∃ Qm : Matrix (Fin n) (Fin n) (PowerSeries O),
      (PA.map fun a => a i) * Qm = (W.Q i ^ h) • (1 : Matrix (Fin n) (Fin n) (PowerSeries O)) := by
  have hsp : ∀ k, ∃ c : Fin n → LetA O f,
      ∑ j, c j • W.φD T (b j : W.DD T) = W.Q ^ h • (letE i : LetA O f) • (b k : W.DD T) := by
    intro k
    have hy : (letE i : LetA O f) • (b k : W.DD T) ∈ W.Nl T i :=
      Submodule.mem_map_of_mem (b k).2
    have h1 := h5 _ hy
    have hle : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤ W.φpull T :=
      Submodule.span_mono (Set.image_mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact (W.N T).smul_mem _ hx))
    exact (Submodule.mem_span_range_iff_exists_fun (LetA O f)).1 (φpull_le_span W T b (hle h1))
  choose c hc using hsp
  have hli : LinearIndependent (LetA O f) fun m => (b m : W.DD T) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key : ∀ k m, ∑ j, c k j * PA m j = if m = k then W.Q ^ h * (letE i : LetA O f) else 0 := by
    intro k
    have e1 : ∑ m, (∑ j, c k j * PA m j - if m = k then W.Q ^ h * (letE i : LetA O f) else 0) •
        (b m : W.DD T) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_smul, mul_smul]
      rw [← hc k, sub_eq_zero, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hφ, Finset.smul_sum]
    intro m
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ e1 m)
  refine ⟨Matrix.of fun j k => c k j i, ?_⟩
  refine Matrix.ext fun m k => ?_
  have e2 := congrFun (key k m) i
  simp only [Finset.sum_apply, Pi.mul_apply] at e2
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [show (∑ j, PA m j i * c k j i) = ∑ j, c k j i * PA m j i from
    Finset.sum_congr rfl fun j _ => mul_comm _ _, e2]
  by_cases hmk : m = k
  · simp [hmk, letE]
  · simp [hmk]

end Generic

end GlobalTheory.WachPlace.FrameHeight

namespace GlobalTheory.WachPlace.FrameHeight

theorem frame_height : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (n h : ℕ) (γ : ((HW l).W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)), GlobalTheory.AdmLoc.CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ (h : ℤ)) → IsFrame ((HW l).W K 1 LL hA.2.2) T γ b N → ∀ i, ∃ Q : Mx (PowerSeries ↥(OL LL)) n n, (N.P i).map (inc l ↥(OL LL)) * Q = (q l ↥(OL LL) ^ h) • (1 : Mx (PowerSeries ↥(OL LL)) n n) := by
  intro D HW F Cm l _ K LL hA T U n h γ b N hU hb hfr i
  have hJ : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet ((HW l).W K 1 LL hA.2.2) T (fun _ => 0) (fun _ => h) := by
    intro τ i' hτ a ha
    haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
    have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite ((D.loc l).PD K) T.ρ τ a).2.2.1 ha
    rw [hU.2 i' τ (fun x => DFunLike.congr_fun hτ x) a] at h1
    have h2 := hb i' a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))
    exact ⟨by simpa using h2.1, h2.2⟩
  have h5 := (GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm l K 1 LL hA.2.2 T (fun _ => 0) (fun _ => h)
    hU.1 hJ).2.1 i
  obtain ⟨Qm, hQm⟩ := exists_inv ((HW l).W K 1 LL hA.2.2) T b
    (fun m k => fun i => inc l ↥(OL LL) (N.P i m k)) hfr.2.1 h i h5
  have hq : ((HW l).W K 1 LL hA.2.2).Q i = q l ↥(OL LL) := by
    have e1 : ((HW l).W K 1 LL hA.2.2).Q = ((HW l).W K 1 LL hA.2.2).q := by
      unfold LocWach.Q
      rw [(HW l).W_s K 1 LL hA.2.2]
      rfl
    rw [e1]
    change ((HW l).W K 1 LL hA.2.2).q₀ = q l ↥(OL LL)
    have e2 := ((HW l).W K 1 LL hA.2.2).q₀_def
    rw [(D.loc l).PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e2
    refine PowerSeries.ext fun j => ?_
    have e3 := congrArg (PowerSeries.coeff (j + 1)) e2
    simpa only [PowerSeries.coeff_succ_X_mul] using e3
  refine ⟨Qm, ?_⟩
  rw [← hq]
  exact hQm

end GlobalTheory.WachPlace.FrameHeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenFibreDim

section

attribute [local instance low] specializationOrder

theorem le_height_of_specializingMap {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T0Space X] [T0Space Z] {f : X → Z} (hf : SpecializingMap f) (n : ℕ) :
    ∀ y : X, (n : ℕ∞) ≤ Order.height (f y) → (n : ℕ∞) ≤ Order.height y := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hex : ∃ b < f y, (n : ℕ∞) ≤ Order.height b := by
      by_contra hne
      push_neg at hne
      have h1 : Order.height (f y) ≤ n := by
        rw [Order.height_eq_iSup_lt_height]
        exact iSup₂_le fun b hb => Order.add_one_le_of_lt (hne b hb)
      have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ n := hy.trans h1
      have h3 : n + 1 ≤ n := by exact_mod_cast h2
      omega
    obtain ⟨b, hb, hnb⟩ := hex
    obtain ⟨y', hyy', rfl⟩ := hf hb.le
    have hlt : y' < y := lt_of_le_of_ne hyy' (fun h => hb.ne (by rw [h]))
    have h4 := Order.height_add_one_le hlt
    have h5 := ih y' hnb
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.height y' + 1 := by gcongr
      _ ≤ Order.height y := h4

end

end GlobalTheory.GenFibreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricActionCoveringGroupOfCoreEquivariance
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.geoAct_of_eqAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ hm ht hp he i
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  have hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k := fun g =>
    ((hp i).2.lift.lev g).imp fun _ h => h.1
  have hs : GoodEmb T.Q.c (O i).s0 := by
    have e : (O i).s0 = T.toCore.σ₀ := sOv_eq T.toCore (O i).c' (O i).hle
    rw [e]
    exact T.toCore.good_σ₀
  obtain ⟨ρC, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 ht.laws hact
    (fun g f hf => (hlift g).elim fun k hk =>
      (he i (O i).s0 hs (O i).hV g k hk f hf).1)
  refine ⟨ρC, fun σ g f => ?_, fun g f hf => ?_⟩
  · by_cases hσ : GoodEmb T.Q.c (res T σ)
    · exact _root_.GlobalTheory.ReadingEquivGood.reading_equivariant T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
    · exact GlobalTheory.T.cuspFormReading_equivariant_not_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
  · exact GlobalTheory.T.level_action_preserves_integral_cusp_forms T κ i (O i).lev2 ht.laws hact g f (ρC g f) (hρ g f) hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixTraceFormBasisChange
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramChange

open GlobalTheory.UnitLemma

theorem herm_sum_sum (K : UQ) (B : InvAlg K) (β : B.A) {a : ℕ} (b : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (i j : Fin a) :
    B.herm β (∑ k, M k i • b k) (∑ l, M l j • b l) =
      ∑ k, ∑ l, M k i * B.herm β (b k) (b l) * K.c (M l j) := by
  have hσ : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hσ, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    LinearMap.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_of_sum (K : UQ) (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (he : ∀ x, e (K.c x) = c (e x)) {a : ℕ} (β : B.A) (b v : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (hv : ∀ j, v j = ∑ i, M i j • b i) :
    (Matrix.of fun i j => e (B.herm β (v i) (v j))) =
      (M.map e)ᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * (M.map e).map c := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.of_apply, hv, herm_sum_sum, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, he, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  intro K B L _ e c he a β b
  refine ⟨fun P => ?_, fun b' => ?_⟩
  · set M : Matrix (Fin a) (Fin a) K.E := P.val.map e.symm with hM
    have hMe : M.map e = P.val := by
      ext i j; simp [hM]
    have hdet : IsUnit M.det := by
      have h1 : e M.det = P.val.det := by
        rw [← hMe]; exact RingHom.map_det (e : K.E →+* L) M
      have h2 : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      rw [← h1] at h2
      exact (isUnit_map_iff e _).mp h2
    refine ⟨b.map (Matrix.toLinearEquiv b M hdet), ?_⟩
    rw [gram_of_sum K B L e c he β b _ M, hMe]
    intro j
    simp [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  · have hdet : IsUnit ((b.toMatrix b').map e).det := by
      have h1 : e (b.toMatrix b').det = ((b.toMatrix b').map e).det :=
        RingHom.map_det (e : K.E →+* L) _
      rw [← h1]
      exact (isUnit_map_iff e _).mpr (b.isUnit_det b')
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet.ne_zero, ?_⟩
    rw [gram_of_sum K B L e c he β b b' (b.toMatrix b')]
    · rfl
    · intro j; rw [b.sum_toMatrix_smul_self]

end GlobalTheory.GramChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.WeilDatumF

theorem fst_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0) : fstA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (fstA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem snd_symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : sndA F (symplOF σ JS JT ξ₀ y z) = 0 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.OrientedHeis.map_trace_hO_zero (sndA F) σ (incAF F E ξ₀) (fun a b => incAF F E (JS⁻¹ a b))
    (fun c d => incAF F E (JT c d)) y z h

theorem symplOF_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (y z : WOF F E nS nT)
    (h1 : y.map (infPartF F E) = 0 ∨ z.map (infPartF F E) = 0)
    (h2 : y.map (finPartF F E) = 0 ∨ z.map (finPartF F E) = 0) : symplOF σ JS JT ξ₀ y z = 0 :=
  Prod.ext (fst_symplOF_eq_zero σ JS JT ξ₀ y z h1) (snd_symplOF_eq_zero σ JS JT ξ₀ y z h2)

theorem symplOHF_fin_real_orth (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT) :
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  intro hu hx
  have e1 := symplOF_eq_zero σ JS JT ξ₀ u x (Or.inl hu) (Or.inr hx)
  have e2 := symplOF_eq_zero σ JS JT ξ₀ x u (Or.inr hu) (Or.inl hx)
  unfold symplOHF
  rw [e1, e2, mul_zero]
  exact ⟨rfl, rfl⟩

end GlobalTheory.WeilDatumF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
section
open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LFun.SphComp

theorem hasSatake_of_isLocComp : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} (π : GlobalTheory.CuspRep.CuspSub E m) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}, GlobalTheory.LFun.HasSatGL w (π.locRep w) B → ∀ {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin m) (w.adicCompletion E))}, π.IsLocComp w σ → ∃ α : Fin m → ℂˣ, Finset.univ.val.map α = B ∧ GlobalTheory.SmGL.HasSatake σ.ρ α := by
  intro E _ _ _ m π w B hB σ hσ
  obtain ⟨f, hf0, hf⟩ := hσ
  obtain ⟨x, hx⟩ := hB.exists_vec

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g u hu => ?_).resolve_right fun h => hf0 ?_
    · rw [LinearMap.mem_ker] at hu ⊢; rw [hf, hu, map_zero]
    · exact LinearMap.ext fun u => by
        have : u ∈ LinearMap.ker f := h ▸ Submodule.mem_top
        simpa using this

  obtain ⟨v, hv0, hvK⟩ : ∃ v : σ.V, v ≠ 0 ∧ ∀ k ∈ (GlobalTheory.LFun.KGL w (n := m) : Set _), σ.ρ k v = v := by
    refine GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup ((GlobalTheory.CuspRep.finRep E m).comp (GlobalTheory.CuspRep.locGL E m w)) σ.ρ
      σ.irred (fun i : GlobalTheory.CuspRep.LocSph.Maps π w σ => i.1) (fun i g u => i.2.2 g u) _ (x : GlobalTheory.CuspRep.Sm E m)
      (fun h => hx.1 (Subtype.ext h)) (fun k hk => ?_) ?_
    · exact congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx.2.1 k hk)
    · rw [GlobalTheory.CuspRep.LocSph.iSup_range_eq π w σ ⟨f, hf0, hf⟩]; exact x.2
  have hfv : f v ≠ 0 := fun h => hv0 (hinj (h.trans (map_zero f).symm))
  have hs : GlobalTheory.LFun.IsSatVecGL w σ.ρ v B := GlobalTheory.LFun.IsSatVecGL.of_map f hf hinj
    (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hf, hvK k hk]) hfv)
  exact (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ (Fin m) σ.V σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL ⟨σ.smooth, σ.irred⟩ hs)

end GlobalTheory.LFun.SphComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HCharUnit

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (k : Eˣ) (v : HeightOneSpectrum (𝓞 E))
    (hu : χ.UnrAt v) (ho : ordF v k = 0) : χ.locK v k = 1 := by
  apply hu
  show Valued.v (((k : E) : v.adicCompletion E)) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have h0 : v.valuation E (k : E) ≠ 0 := by simp
  have hl : WithZero.log (v.valuation E (k : E)) = 0 := by
    unfold ordF at ho; omega
  rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]

theorem finprod_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ),
    (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  intro E _ _ χ k
  have hT : ({v | ¬ χ.UnrAt v} ∪ {v : HeightOneSpectrum (𝓞 E) | ordF v k ≠ 0}).Finite :=
    Set.Finite.union (Filter.eventually_cofinite.mp (Formalism.L2.Fam.IdTrans.unrAe χ)) (GlobalTheory.HeckeProduct.finite_ordF k)
  set S := hT.toFinset with hSdef
  have hsub : (Function.mulSupport fun w : Pl E => χ.locK w k) ⊆ (S : Set (HeightOneSpectrum (𝓞 E))) := by
    intro v hv
    rw [hSdef, Set.Finite.coe_toFinset]
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (locK_eq_one χ k v h.1 h.2)
  refine ⟨S.finite_toSet.subset hsub, ?_⟩
  have hS : ∀ v, v ∉ S → χ.UnrAt v := by
    intro v hv
    by_contra h
    exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inl h)
  have hpr := Formalism.L2.Host.HChar.productRule χ S hS k
  have hrest : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    have : ordF v k = 0 := by
      by_contra h
      exact hv (by rw [hSdef, Set.Finite.mem_toFinset]; exact Or.inr h)
    rw [this, zpow_zero]
  rw [hrest, mul_one] at hpr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, mul_comm]
  exact hpr

end GlobalTheory.HCharUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SpanParts

theorem iSup_rows_eigenparts_principal_level_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → (⨆ p, R.EEp3 p) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hS hC
  obtain ⟨hCore, hSF, hE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  obtain ⟨h, -, -, hTop, -⟩ := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore hS R.SF hSF
  rw [eq_top_iff, ← hTop]
  refine iSup_le fun c => ?_
  by_cases h0 : R.EEc c = ⊥
  · rw [← hE c, h0]; exact bot_le
  · obtain ⟨p, hp⟩ := hC c h0
    rw [← hE c]
    refine le_trans ?_ (le_iSup _ p)
    exact le_iSup₂_of_le c hp le_rfl

end GlobalTheory.SpanParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAffineAbsPowBoundStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_affine_abs_pow_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), s < 0 → ∀ a b : k,
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  first | exact @GlobalTheory.KSplit.lintegral_absPow_affine_le | exact GlobalTheory.KSplit.lintegral_absPow_affine_le | (intros; apply GlobalTheory.KSplit.lintegral_absPow_affine_le <;> assumption)
end

