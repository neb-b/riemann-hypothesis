module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstMapInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InhabitedStage
section
noncomputable section

namespace GlobalTheory.Mem.GJInhab

open Formalism.BasicNotions NumberField IsDedekindDomain

def baseVol (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : ℝ :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

theorem baseVol_pos (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : 0 < baseVol B cd W :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol_pos B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

def noJet {R : Ranks} (H : Host R) : ThetaJet R H where
  Sit := Empty
  loc := fun i => i.elim
  l_inert := fun i => i.elim
  jOf := fun i => i.elim
  j_mem := fun i => i.elim
  N0_eq := fun i => i.elim
  N1_eq_exponentN1 := fun i => i.elim
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

def oneJet {R : Ranks} (H : Host R) (hm : 1 ≤ R.m) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (hc : H.cls l = .signal ∨ H.cls l = .inertClass) : ThetaJet R H where
  Sit := Unit
  loc := fun _ =>
    haveI : Fact l.Prime := ⟨hl⟩
    { l := l
      five_le_l := h5
      d := 2
      d_even := even_two
      two_le_d := le_rfl
      N0 := R.N 0
      N1 := R.N 1
      Th := 1 }
  l_inert := fun _ => hc
  jOf := fun _ => 1
  j_mem := fun _ => ⟨le_rfl, hm⟩
  N0_eq := fun _ => rfl
  N1_eq_exponentN1 := fun _ => rfl
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

theorem exists_noJet (B : Base) (C : Cols B) (cd : CDHaar) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = noJet B.host ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (noJet B.host) (GJModel.gxOne B) (fun i => i.elim) (fun i => i.elim)
  exact ⟨J, hcd, by rw [hv, hcd], hj, hf⟩

theorem exists_oneJet (B : Base) (C : Cols B) (cd : CDHaar) (hm : 1 ≤ B.R.m) (u : B.Word)
    (h0 : Nonempty ((C.mem u).C.cls 0)) (h1 : Nonempty ((C.mem u).C.cls 1))
    (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) (hc : B.host.cls l = .signal ∨ B.host.cls l = .inertClass) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = oneJet B.host hm l hl h5 hc ∧
      (∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
        B.places.resChar (J.jetW i) = l) ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (oneJet B.host hm l hl h5 hc) (GJModel.gxOne B) (fun _ => ⟨u, h0, h1⟩) (fun i => i.elim)
  have key : ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 := by
    rw [hj]
    exact ⟨(), rfl, rfl, rfl⟩
  obtain ⟨i, hi1, hil, hid⟩ := key
  exact ⟨J, hcd, by rw [hv, hcd], hj, ⟨i, hi1, hil, hid, (J.jetW_l i).trans hil⟩, hf⟩

theorem nonempty_stage (B : Base) (C : Cols B) : Nonempty (GJStage B C) := by
  obtain ⟨cd⟩ := _root_.GlobalTheory.CompactDualExists.nonempty_cdHaar
  obtain ⟨J, -⟩ := exists_noJet B C cd
  exact ⟨J⟩

theorem inhabited_stage (B : Base) (C : Cols B) :
    (∃ J : GJStage B C, J.vol = baseVol B J.cd) ∧
    (1 ≤ B.R.m → Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∀ l : ℕ, l.Prime → 5 ≤ l → (B.host.cls l = .signal ∨ B.host.cls l = .inertClass) →
        ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit ∧
          ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
            B.places.resChar (J.jetW i) = l) ∧
    (Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit) := by
  obtain ⟨cd⟩ := _root_.GlobalTheory.CompactDualExists.nonempty_cdHaar
  refine ⟨?_, fun hm h0 h1 l hl h5 hc => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨J, -, hv, -⟩ := exists_noJet B C cd
    exact ⟨J, hv⟩
  · obtain ⟨J, -, hv, -, ⟨i, hi⟩, -⟩ := exists_oneJet B C cd hm B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩, i, hi⟩
  · obtain ⟨l, hl, h5, hc⟩ := GJModel.exists_inert B.host
    have hm := B.R.two_le_m
    obtain ⟨J, -, hv, -, ⟨i, -⟩, -⟩ := exists_oneJet B C cd (by omega) B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩⟩

end GlobalTheory.Mem.GJInhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerProductPositiveDefinite
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem re_pos_of_majAt {K V ι M : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (σ : K →+* ℂ) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : IsUnit (X (InfinitePlace.mk σ)).det) (e : V →ₛₗ[σ] M) (Q : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h : ∀ x, (Formalism.HermitianLatticesTheory.majAt b X (InfinitePlace.mk σ) x x).re = (Q (e x) (e x)).re)
    (φ : M) (hφ : φ ∈ Submodule.span ℂ (Set.range fun a => e (b a))) (h0 : φ ≠ 0) :
    0 < (Q φ φ).re := by
  set v := InfinitePlace.mk σ with hv
  obtain ⟨ρ, hρc, hρρ, hρσ⟩ : ∃ ρ : ℂ →+* ℂ, Continuous ρ ∧ (∀ z, ρ (ρ z) = z) ∧
      ∀ x, ρ (v.embedding x) = σ x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact ⟨RingHom.id ℂ, continuous_id, fun _ => rfl, fun x => by rw [hv, h1]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun z => Complex.conj_conj z, fun x => by
        rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]⟩
  have hd0 : DenseRange (Pi.map (fun _ : ι => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have key : ∀ w : ι → ℂ, (Q (∑ a, ρ (w a) • e (b a)) (∑ a, ρ (w a) • e (b a))).re =
      ∑ i, ‖((X v)⁻¹.mulVec w) i‖ ^ 2 := by
    intro w
    induction w using hd0.induction_on with
    | hp =>
      apply isClosed_eq
      · set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply]
        have hρ : ∀ i : ι, Continuous (fun y : ι → ℂ => ρ (y i)) :=
          fun i => hρc.comp (continuous_apply i)
        fun_prop
      · have : Continuous fun w : ι → ℂ => (X v)⁻¹.mulVec w :=
          Continuous.matrix_mulVec continuous_const continuous_id
        fun_prop
    | ih y =>
      have h1 := h (b.equivFun.symm y)
      have h2 : e (b.equivFun.symm y) =
          ∑ a, ρ (Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y a) • e (b a) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [b.equivFun_symm_apply, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [LinearMap.map_smulₛₗ, Pi.map_apply, hρσ]
      have h3 : Formalism.HermitianLatticesTheory.vecAt b v (b.equivFun.symm y) = Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y := by
        funext a
        have : b.repr (b.equivFun.symm y) a = y a := by
          rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
        simp only [Formalism.HermitianLatticesTheory.vecAt, this, Pi.map_apply]
      rw [← h2, ← h1, ← normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Formalism.HermitianLatticesTheory.fcoord, h3]
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hφ
  have hk := key fun a => ρ (z a)
  simp only [hρρ] at hk
  rw [hk]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => by positivity) fun hs => h0 ?_
  have h4 : (X v)⁻¹.mulVec (fun a => ρ (z a)) = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hs.symm i (Finset.mem_univ i)
    simpa using this
  have h5 : (fun a => ρ (z a)) = 0 := by
    have := congrArg (X v).mulVec h4
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  refine Finset.sum_eq_zero fun a _ => ?_
  have h6 : z a = 0 := by
    rw [← hρρ (z a), show ρ (z a) = 0 from congrFun h5 a, map_zero]
  rw [h6, zero_smul]

theorem ipC_zero_re_pos : ∀ (B : Base) (C : Cols B) (u : B.Word), (∀ φ ψ : (C.mem u).A.Mu0, (C.fm u).ipC 0 ψ φ = star ((C.fm u).ipC 0 φ ψ)) → ∀ φ : (C.mem u).A.Mu0, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re := by
  intro B C u _ φ hφ
  let Q : ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ⋆[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) ((C.fm u).ipC 0)
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  refine re_pos_of_majAt B.embLL ((C.fm u).lat 0).b ((C.fm u).lat 0).X (((C.fm u).lat_good 0).1 _)
    ((C.fm u).emb 0) Q ((C.fm u).emb_norm 0) φ ?_ (fun h => hφ (Subtype.ext h))
  rw [((C.fm u).emb_basis 0).2, (C.fm u).Fi_zero]
  exact φ.2

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory

theorem isCompact_matInt_set (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} := by
  have hO : IsCompact ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) :
      Set (FiniteAdeleRing (𝓞 F) F)) := PI.WAU.isCompact_Ohat (F := F)
  have h := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hO))
  have he : {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) | PIW.ClassFinD.MatInt M} =
      Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n =>
        ((PIW.ClassFinD.Ohat F : Subring (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F)))) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [he]
  exact h

theorem isCompact_KGL (F : Type) [Field F] [NumberField F] (n : ℕ) :
    IsCompact (PIW.ClassFinD.KGL F n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 F) F))) := by
  have hA := isCompact_matInt_set F n
  have hA' := (MulOpposite.opHomeomorph
    (M := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).symm.isCompact_preimage.2 hA
  have h := (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))).isCompact_preimage (hA.prod hA')
  convert h using 1
  ext g
  exact Iff.rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitian
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom.IsoMat

open Formalism.UG (cT cT_mul cT_one)

section Gen

variable {A : Type} [CommRing A] {k n m : ℕ}

theorem conj_right_zero {r : ℕ} {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {c : Matrix (Fin n) (Fin r) A} (h : x * c = 0) : aP * x * aQ * (aP * c) = 0 := by
  calc _ = aP * (x * ((aQ * aP) * c)) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.mul_zero]

theorem conj_left_zero {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hQP : aQ * aP = 1)
    {x : Matrix (Fin n) (Fin n) A} {y : Matrix (Fin k) (Fin n) A} (h : y * x = 0) : y * aQ * (aP * x * aQ) = 0 := by
  calc _ = (y * ((aQ * aP) * x)) * aQ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hQP, Matrix.one_mul, h, Matrix.zero_mul]

theorem conj_mulVec {r : ℕ} (aP : Matrix (Fin m) (Fin n) A) (aQ : Matrix (Fin n) (Fin m) A)
    (x : Matrix (Fin n) (Fin n) A) (c : Matrix (Fin n) (Fin r) A) (v : Fin m → A) (a : Fin r → A)
    (h : x.mulVec (aQ.mulVec v) = c.mulVec a) : (aP * x * aQ).mulVec v = (aP * c).mulVec a := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]

theorem conj_sub_one {aP : Matrix (Fin m) (Fin n) A} {aQ : Matrix (Fin n) (Fin m) A} (hPQ : aP * aQ = 1)
    (x : Matrix (Fin n) (Fin n) A) : aP * x * aQ - 1 = aP * (x - 1) * aQ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ]

end Gen

variable {D : D7} {V V' : HSp D} (I : IsoMat V V')

theorem cT_P_gram : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q := by
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

theorem mat_kap_sub (g : GA D V) :
    (matHom V' (I.kap g)).1 - 1 = HMul.hMul (HMul.hMul I.aP ((matHom V g).1 - 1)) I.aQ :=
  conj_sub_one I.aP_aQ _

theorem kap_mem_NI {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {x : GA D V} (hx : x ∈ NI V C) :
    I.kap x ∈ NI V' (I.P * C) := by
  have key : NI V C ≤ (NI V' (I.P * C)).comap I.kap.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    intro g hg
    show I.kap g ∈ NI V' (I.P * C)
    obtain ⟨h1, h2, h3⟩ := hg
    refine Subgroup.subset_closure ?_
    have hm := I.mat_kap_sub g
    have hPC : (I.P * C).map (incA D) = I.aP * C.map (incA D) := Matrix.map_mul
    have hG : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram =
        cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram * I.Q := by
      rw [cT_mul, Matrix.mul_assoc, I.cT_P_gram, Matrix.mul_assoc]
    have hGm : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (incA D) * I.aQ := by
      rw [hG, Matrix.map_mul]; rfl
    refine ⟨?_, ?_, fun x' hx' => ?_⟩
    · show HMul.hMul ((matHom V' (I.kap g)).1 - 1) ((I.P * C).map (incA D)) = 0
      rw [hm, hPC]
      exact conj_right_zero I.aQ_aP h1
    · show HMul.hMul ((cT (D.sp.cm.sig : D.host.E →+* D.host.E) (I.P * C) * V'.gram).map (incA D))
        ((matHom V' (I.kap g)).1 - 1) = 0
      rw [hGm, hm]
      exact conj_left_zero I.aQ_aP h2
    · have hx : (cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).mulVec (I.Q.mulVec x') = 0 := by
        rw [Matrix.mulVec_mulVec, ← hG]
        exact hx'
      obtain ⟨a, ha⟩ := h3 _ hx
      refine ⟨a, ?_⟩
      have hQx : I.aQ.mulVec (fun i => incA D (x' i)) = fun i => incA D (I.Q.mulVec x' i) :=
        funext fun i => (RingHom.map_mulVec (incA D) I.Q x' i).symm
      show ((matHom V' (I.kap g)).1 - 1).mulVec (fun i => incA D (x' i)) = ((I.P * C).map (incA D)).mulVec a
      rw [hm, hPC]
      refine conj_mulVec _ _ _ _ _ _ ?_
      rw [hQx]
      exact ha
  exact key hx

theorem isIsoFrame_Q {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} (h : IsIsoFrame V' C') :
    IsIsoFrame V (I.Q * C') := by
  obtain ⟨hr, hli, hiso⟩ := h
  refine ⟨hr, ?_, ?_⟩
  · have e : (I.Q * C').transpose = (Matrix.mulVecLin I.Q) ∘ C'.transpose := by
      funext i j
      rfl
    rw [e]
    refine hli.map' _ (LinearMap.ker_eq_bot.2 fun a b hab => ?_)
    have := congrArg I.P.mulVec hab
    simpa [Matrix.mulVec_mulVec, I.PQ] using this
  · have hg : cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q = V'.gram := I.symm.gram
    rw [cT_mul]
    calc _ = cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' *
          (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q * V.gram * I.Q) * C' := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hg]; exact hiso

theorem kap_mem_NI' {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {x : GA D V} (hx : x ∈ NI V (I.Q * C')) :
    I.kap x ∈ NI V' C' := by
  have := I.kap_mem_NI (I.Q * C') hx
  rwa [← Matrix.mul_assoc, I.PQ, Matrix.one_mul] at this

theorem kap_symm_mem_NI {r : ℕ} {C' : Matrix (Fin V'.rank) (Fin r) D.host.E} {y : GA D V'} (hy : y ∈ NI V' C') :
    I.kap.symm y ∈ NI V (I.Q * C') :=
  I.symm.kap_mem_NI C' hy

end GlobalTheory.Mem.Isom.IsoMat


open GlobalTheory.Mem.Isom GlobalTheory.Mem.Isom.IsoMat in
theorem GlobalTheory.Mem.Isom.isCuspFun_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ),
    IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  intro D V V' I φ hφ r C' hC' μ 𝓕 hμ h𝓕 g
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V (I.Q * C')
  haveI := GlobalTheory.AutFunCounterexample.borel_NI D V' C'
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V'
  let T : NI V (I.Q * C') ≃ₜ* NI V' C' :=
    { toFun := fun x => ⟨I.kap (x : GA D V), I.kap_mem_NI' x.2⟩
      invFun := fun y => ⟨I.kap.symm (y : GA D V'), I.kap_symm_mem_NI y.2⟩
      left_inv := fun x => Subtype.ext (I.kap.symm_apply_apply (x : GA D V))
      right_inv := fun y => Subtype.ext (I.kap.apply_symm_apply (y : GA D V'))
      map_mul' := fun x y => Subtype.ext (map_mul I.kap (x : GA D V) (y : GA D V))
      continuous_toFun := (I.continuous_kap.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (I.continuous_kap_symm.comp continuous_subtype_val).subtype_mk _ }
  let e : NI V (I.Q * C') ≃ᵐ NI V' C' := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e (μ.map e.symm) μ :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hH : (μ.map e.symm).IsHaarMeasure := T.symm.isHaarMeasure_map μ
  have hF : IsFundamentalDomain (NIQ V (I.Q * C')) (e ⁻¹' 𝓕) (μ.map e.symm) := by
    refine h𝓕.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun γ => ⟨T.symm γ, I.symm.kap_mem_GQ γ.2⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun γ x => ?_
    · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
    · exact ⟨⟨T b.1, I.kap_mem_GQ b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
    · change T (T.symm γ * x) = γ * T x
      rw [map_mul, T.apply_symm_apply]
  have key := hφ r (I.Q * C') (I.isIsoFrame_Q hC') (μ.map e.symm) (e ⁻¹' 𝓕) hH hF (I.kap.symm g)
  rw [← hp.setIntegral_preimage_emb e.measurableEmbedding (fun n : NI V' C' => I.tr φ ((n : GA D V') * g)) 𝓕]
  refine Eq.trans ?_ key
  congr 1
  funext x
  show φ (I.kap.symm (I.kap (x : GA D V) * g)) = φ ((x : GA D V) * I.kap.symm g)
  rw [map_mul, MulEquiv.symm_apply_apply]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

namespace GroundFieldChange

theorem finsum_const_mul_int (c : ℤ) (f : ℕ → ℤ) : ∑ᶠ n, c * f n = c * ∑ᶠ n, f n :=
  (mul_finsum f c).symm

theorem hdim_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules)
    (n : ℕ) : hdim κ F n = Module.finrank κ κ' * hdim κ' F n := by
  rw [hdim_def, hdim_def, Module.finrank_mul_finrank]

theorem chi_fieldChange (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (F : Z.Modules) :
    chi κ F = (Module.finrank κ κ' : ℤ) * chi κ' F := by
  rw [chi_def, chi_def, ← finsum_const_mul_int]
  refine finsum_congr fun n ↦ ?_
  rw [hdim_fieldChange κ κ' Z F n, Nat.cast_mul]
  ring

theorem interNum_fieldChange : ∀ (κ κ' : Type) [Field κ] [Field κ'] [Algebra κ κ'] (Z : Scheme.{0})
    [Algebra κ' Γ(Z, ⊤)] [Algebra κ Γ(Z, ⊤)] [IsScalarTower κ κ' Γ(Z, ⊤)] (G : Z.Modules)
    {ι : Type} [Fintype ι] (L : ι → LB Z),
    interNum κ G L = (Module.finrank κ κ' : ℤ) * interNum κ' G L := by
  intro κ κ' _ _ _ Z _ _ _ G ι _ L
  rw [interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [chi_fieldChange κ κ' Z]
  ring

end GroundFieldChange

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsContinuousL2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_toL2_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w) := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act _ a A _ hs hA φ hφ
  let g := GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2
  have hg : ∀ w, gard ε σ φ w = g w := fun w => gard_eq hσ hφ w
  let L : H →ₗ[ℂ] Lp ℂ 2 ν := A.comp (g : H →ₗ[ℂ] H)
  have hL : ∀ w, L w = A (gard ε σ φ w) := fun w => rfl
  have hc : ∀ x, Continuous fun w => a (gard ε σ φ w) x := fun x => by
    obtain ⟨C, hC⟩ := (_root_.GlobalTheory.SobGarding.sobCont_gard n ε H σ P G hP hG hσ _ (hs x)).1 φ hφ
    exact (LinearMap.mkContinuous (((LinearMap.proj x).comp a).comp (g : H →ₗ[ℂ] H)) C hC).continuous
  have key : Continuous L := by
    refine L.continuous_of_seq_closed_graph fun u w f hu hf => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
    have h1 : ∀ᵐ x ∂ν, ∀ k, (L (u k) : X → ℂ) x = a (gard ε σ φ (u k)) x :=
      ae_all_iff.2 fun k => hA _ (gard_mem hP hG hσ hφ (u k))
    refine Lp.ext ?_
    filter_upwards [hae, h1, hA _ (gard_mem hP hG hσ hφ w)] with x hx h1x h2x
    have h3 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (a (gard ε σ φ w) x)) :=
      ((hc x).tendsto w).comp (hu.comp hns.tendsto_atTop)
    have h4 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (f x)) :=
      hx.congr fun k => h1x (ns k)
    exact (tendsto_nhds_unique h4 h3).trans h2x.symm
  exact key

end GlobalTheory.SmVec
end

