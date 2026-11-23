module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFramePowEqIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationNaturalSemilinear
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.rig_pull_natural_semi : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] ((G'.cocycles × G'.omega) ⧸ _root_.LinearMap.range (G'.cob.prod (_root_.LinearMap.codRestrict G'.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G'.A i))).domRestrict G'.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k') (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  intro p k k' _ _ σ d e G G' c c' s μ φ ρ ρ' hμ hφ hρ hρ' t w ht
  have hz : (fun n => c.ev₂ n t) ∈ G.cocycles := (_root_.GlobalTheory.Katz.isCoc_iff_mem_cocycles p k d G c μ hμ t).1 ht
  have hu : (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1 w
  rw [hρ t w ⟨_, hz⟩ ⟨_, hu⟩ (fun _ => rfl) (fun _ => rfl), SemiHom.rig_mk]
  have hev : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
    intro n
    exact GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ n t
  refine hρ' _ _ _ _ (fun n => ?_) (fun n => ?_)
  · rw [SemiHom.cocycles_val, hev n]
  · rw [SemiHom.omega_val]
    change (s.app n).cot (∑ i, w i • dUnit (R := k) (c.x n i)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ, SemiBialgHom.cot_d]
    have hd : ∀ i, dUnit (R := k') (s.app n (c.x n i)) = ∑ l, lin (φ i) l • dUnit (R := k') (c'.x n l) := fun i => by
      rw [← hφ n i]
      exact (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A n) (c'.x n) (c'.nil n) (c'.aug n) (φ i)).2
    simp only [hd, Finset.smul_sum, smul_smul, pullLin, Finset.sum_smul]
    exact Finset.sum_comm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPresentationOfSeriesPairs
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.isRigOf_rigMk : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), c.IsLawOf μ → (∀ s w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n s) → (∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i)) → ρ (s, w) = G.rigMk (z, u)) → IsRigOf μ ρ := by
  intro p k _ d G c μ ρ hμ hρ
  have hcoc := _root_.GlobalTheory.Katz.isCoc_iff_mem_cocycles p k d G c μ hμ
  have hdu := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d
  have hlaw := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).2
  have hom := GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c
  have hone := _root_.GlobalTheory.Katz.Chart.functions_are_series p k d G c
  have hpres := (_root_.GlobalTheory.chart_square_presents p k d G c).2
  constructor
  · intro v
    obtain ⟨⟨z, u⟩, rfl⟩ := Submodule.mkQ_surjective _ v
    obtain ⟨s, hs, -⟩ := hpres z.1 (fun n => (z.2 n).2)
    obtain ⟨w, hw, -⟩ := hom.2 u
    have hz : (fun n => c.ev₂ n s) = z.1 := funext hs
    refine ⟨s, w, (hcoc s).2 (hz ▸ z.2), ?_⟩
    exact hρ s w z u (fun n => (hs n).symm) hw
  · intro s w hs
    let z : G.cocycles := ⟨fun n => c.ev₂ n s, (hcoc s).1 hs⟩
    let u : G.omega := ⟨fun n => ∑ i, w i • dUnit (R := k) (c.x n i), hom.1 w⟩
    rw [hρ s w z u (fun _ => rfl) (fun _ => rfl)]
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨B, hB⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq] at hB
      obtain ⟨b, hb, -⟩ := hone.2.2 B.1 B.2
      refine ⟨b, ?_, ?_⟩
      · have hz2 : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s := fun n => hone.2.1 n s
        obtain ⟨t, -, ht⟩ := hpres (fun n => c.ev₂ n s) hz2
        have h1 := ht s (fun _ => rfl)
        have h2 := ht (cob1 μ b) (fun n => by
          rw [(hlaw n b).2, hb n]
          exact (congrArg (fun y : G.cocycles => y.1 n) hB.1))
        exact h1.trans h2.symm
      · obtain ⟨w', -, hw'⟩ := hom.2 u
        have e1 := hw' w (fun _ => rfl)
        have e2 := hw' (lin b) (fun n => by
          rw [← (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2]
          change _ = dUnit (R := k) (c.ev n b)
          rw [hb n]
          exact (congrArg (fun y : G.omega => y.1 n) hB.2).symm)
        exact e1.trans e2.symm
    · rintro ⟨b, rfl, rfl⟩
      refine ⟨⟨fun n => c.ev n b, fun n => hone.1 n b⟩, ?_⟩
      rw [LinearMap.prod_apply, Prod.mk.injEq]
      constructor
      · apply Subtype.ext; funext n
        exact ((hlaw n b).2).symm
      · apply Subtype.ext; funext n
        exact (hdu (G.A n) (c.x n) (c.nil n) (c.aug n) b).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.RigTorsTriv

theorem triv_of_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  intro S A _ _ hA M hM hrig k hk hpow hfib
  have key : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (∃ t : (M.pull f).Gen, t.IsGen) ↔ pull f (cls M hM) = 0 :=
    fun f => (cls_eq_zero_iff (pull_isLB hM f)).symm.trans (by rw [cls_pull hM f])
  have hsurj : ∀ V : S.Opens, Function.Surjective (A.hom ∣_ V).appTop.hom := fun V => by
    have hG : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
    have h1 := hG _ _ (Out.TLinPf.isAb_pullback V.ι A hA)
    let e := IsPullback.isoIsPullback _ _ (isPullback_morphismRestrict A.hom V)
      (IsPullback.of_hasPullback A.hom V.ι).flip
    have he : e.hom ≫ pullback.snd A.hom V.ι = A.hom ∣_ V := IsPullback.isoIsPullback_hom_fst _ _ _ _
    have hi : Function.Surjective e.hom.appTop.hom := by
      have : IsIso (e.hom.app ⊤) := inferInstance
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
    rw [← he, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    exact hi.comp h1.2
  have hc0 : pull (1 : 𝟙_ (Over S) ⟶ A).left (cls M hM) = 0 := (key _).1 hrig
  have hkM : k • cls M hM = 0 := by
    have h := (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).2 hpow
    rw [cls_linComb hM] at h
    simpa [pull_id] using h
  refine GlobalTheory.CubeGlue.triv_of_locally_triv hM A.hom (1 : 𝟙_ (Over S) ⟶ A).left
    (by simpa using Over.w (1 : 𝟙_ (Over S) ⟶ A)) hsurj hrig ?_
  intro s
  obtain ⟨R, j, hj, ⟨p, hp⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := s) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := hj
  let A' := (Over.pullback j').obj A
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback j' A hA
  let φ := pullback.fst A.hom j'
  have hM' : (M.pull φ).IsLB := pull_isLB hM φ
  have key' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A'.left),
      (∃ t : ((M.pull φ).pull f).Gen, t.IsGen) ↔ pull (f ≫ φ) (cls M hM) = 0 := fun f =>
    (cls_eq_zero_iff (pull_isLB hM' f)).symm.trans (by rw [cls_pull hM' f, cls_pull hM φ, pull_comp])
  have hone : (1 : 𝟙_ (Over (Sp R)) ⟶ A').left ≫ φ = j' ≫ (1 : 𝟙_ (Over S) ⟶ A).left := by
    rw [Hom.one_def, Hom.one_def]
    simp [φ]
  have hrig' := (key' _).2 (by rw [hone, pull_comp, hc0, map_zero])
  have hk' : IsUnit (k : R) := by
    have h := hk.map ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp j'.appTop.hom)
    simpa using h
  have hpow' : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM' _ _)).1 ?_
    rw [cls_linComb hM']
    simp [pull_id, cls_pull hM φ, ← map_nsmul, hkM]
  let P : PrimeSpectrum R := p
  haveI : P.asIdeal.IsPrime := P.isPrime
  let F := AlgebraicClosure P.asIdeal.ResidueField
  let ψ : R →+* F := (algebraMap P.asIdeal.ResidueField F).comp (algebraMap R P.asIdeal.ResidueField)
  have hfib' : ∃ t : ((M.pull φ).pull (pullback.fst A'.hom (spMap ψ))).Gen, t.IsGen := by
    rw [key']
    have h0 := (key _).1 (hfib F (spMap ψ ≫ j'))
    have e : pullback.fst A'.hom (spMap ψ) ≫ φ =
        pullback.lift (pullback.fst A'.hom (spMap ψ) ≫ φ) (pullback.snd A'.hom (spMap ψ))
          (by
            have hc : pullback.fst A'.hom (spMap ψ) ≫ A'.hom = pullback.snd A'.hom (spMap ψ) ≫ spMap ψ :=
              pullback.condition
            rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact (congrArg (· ≫ j') hc).trans (Category.assoc _ _ _))
          ≫ pullback.fst A.hom (spMap ψ ≫ j') := (pullback.lift_fst _ _ _).symm
    rw [e, pull_comp, h0, map_zero]
  obtain ⟨r, hr, ht⟩ := GlobalTheory.T.localTriviality_of_noetherian_descent (GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre GlobalTheory.T.exists_generator_torsion_bundle_abelianScheme_sqZero) R A' hA' (M.pull φ) hM' hrig' k hk' hpow' F ψ hfib'
  have hrp : P ∈ PrimeSpectrum.basicOpen r := by
    intro hm
    apply hr
    show algebraMap _ F (algebraMap R P.asIdeal.ResidueField r) = 0
    rw [(Ideal.algebraMap_residueField_eq_zero).2 hm, map_zero]
  refine ⟨j' ''ᵁ PrimeSpectrum.basicOpen r, ⟨p, hrp, hp⟩, ?_⟩
  refine (key _).2 ?_
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen r
  let W := A.hom ⁻¹ᵁ (j' ''ᵁ D)
  have h1 : Set.range (W.ι ≫ A.hom) ⊆ Set.range j' := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨q, -, hq⟩ := y.2
    exact ⟨q, hq⟩
  let m : W.toScheme ⟶ A'.left :=
    pullback.lift W.ι (IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1) (IsOpenImmersion.lift_fac _ _ _).symm
  have h2 : Set.range m ⊆ Set.range (A'.hom ⁻¹ᵁ D).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : m ≫ A'.hom = IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 := pullback.lift_snd _ _ _
    show (m ≫ A'.hom) y ∈ D
    rw [e]
    obtain ⟨q, hqD, hq⟩ := y.2
    have : IsOpenImmersion.lift j' (W.ι ≫ A.hom) h1 y = q := j'.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]; exact hq.symm)
    rw [this]; exact hqD
  have hfac : W.ι = IsOpenImmersion.lift (A'.hom ⁻¹ᵁ D).ι m h2 ≫ (A'.hom ⁻¹ᵁ D).ι ≫ φ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (pullback.lift_fst _ _ _).symm
  rw [hfac, pull_comp, (key' _).1 ht, map_zero]

end GlobalTheory.RigTorsTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecBasisTransfer

def chartPullUnLinComb {X X' Y Y' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (g : Y ⟶ Y') (hc : ∀ k, g ≫ ψ' k ≫ F = ψ k) :
    ChartPull (LB.LinComb L ψ ε) (LB.LinComb (L.pull F) ψ' ε) g :=
  have pt : ∀ k (y : Y), F (ψ' k (g y)) = ψ k y := fun k y => by
    rw [← hc k]; rfl
  have le : ∀ j : K → L.ι, LB.wchart L ψ j ≤ g ⁻¹ᵁ LB.wchart (L.pull F) ψ' (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (by
      show F (ψ' k (g y)) ∈ L.U (j k)
      rw [pt k y]; exact Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      have m : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j k) := le j hj
      have m' : g y ∈ LB.wchart (L.pull F) ψ' (fun k _ => j' k) := le j' hj'
      refine (gm_linComb L ψ ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) ψ' ε g y _ _ m m').symm)
      refine Eq.trans ?_ (gm_pull_g L F (g ≫ ψ' k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 m k) (Set.mem_iInter.1 m' k)).symm
      rw [Category.assoc, hc k, Category.id_comp] }

theorem sec_eq_of_f {Y : Scheme.{0}} {N : LB Y} {s t : LB.Sec N} (e : s.f = t.f) : s = t := by
  obtain ⟨a, ha⟩ := s
  obtain ⟨b, hb⟩ := t
  cases e
  rfl

theorem pullSec_pullSec {Y Y' : Scheme.{0}} {M : LB Y} {M' : LB Y'} {g : Y ⟶ Y'} {h : Y' ⟶ Y}
    (c' : ChartPull M M' g) (c : ChartPull M' M h) (hh : g ≫ h = 𝟙 Y) (hidx : ∀ j, c.idx (c'.idx j) = j)
    (s : LB.Sec M) : GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s := by
  refine sec_eq_of_f (funext fun j => fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y ≫ g) y ∈ M'.U (c'.idx j) := c'.le j hy
  rw [GlobalTheory.SecTwist.gs_pullSec c' _ (𝟙 Y) y j hy, GlobalTheory.SecTwist.gs_pullSec c s (𝟙 Y ≫ g) y _ hy',
    Category.id_comp, hh, hidx j]

theorem gs_liftHom {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} {Z : Scheme.{0}}
    (f : Z ⟶ (T ⊗ A).left) (z : Z) (W : (T ⊗ A).left.Opens) (hz : f z ∈ W) (r : Γ(T.left, ⊤)) :
    gs f z W (liftHom A W r) = gs (f ≫ (fst T A).left) z ⊤ r :=
  (gs_res f z le_top hz _).trans (gs_pull f (fst T A).left z ⊤ trivial _)

def pullLin {S S' Z : Scheme.{0}} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A'] (L : LB A.left)
    (L' : LB A'.left) (k k' : ℤ) (y : Z ⟶ S) (x : Z ⟶ S') {h : (Over.mk x ⊗ A').left ⟶ (Over.mk y ⊗ A).left}
    (c : ChartPull (LPow A' L' k' (Over.mk x)) (LPow A L k (Over.mk y)) h)
    (hfst : h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) A').left) :
    SecM A L k (Over.mk y) →ₗ[Γ(Z, ⊤)] SecM A' L' k' (Over.mk x) where
  toFun m := SecM.ofSec A' (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m))
  map_add' m₁ m₂ := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (m₁ + m₂))).f i) =
      gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₁)).f i +
        (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m₂)).f i)
    rw [gs_add _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz,
      GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    exact gs_add _ z _ hz' _ _)
  map_smul' r m := Subtype.ext (funext fun i => fn_ext fun z hz => by
    have hz' : (𝟙 _ ≫ h) z ∈ (LPow A L k (Over.mk y)).U (c.idx i) := c.le i hz
    show gs (𝟙 _) z _ ((GlobalTheory.SecTwist.pullSec c (SecM.toSec A (r • m))).f i) =
      gs (𝟙 _) z _ (liftHom A' _ r * (GlobalTheory.SecTwist.pullSec c (SecM.toSec A m)).f i)
    rw [gs_mul _ z _ hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz, GlobalTheory.SecTwist.gs_pullSec c _ _ z i hz]
    refine (gs_mul _ z _ hz' (liftHom A _ r) _).trans (congrArg (· * _) ?_)
    rw [gs_liftHom A _ z _ hz' r, gs_liftHom A' (𝟙 _) z _ hz r, Category.assoc, hfst])

theorem li_span_map {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] {I : Type*} (E : M ≃ₗ[R] M') (v : I → M) (hli : LinearIndependent R v)
    (hsp : Submodule.span R (Set.range v) = ⊤) :
    LinearIndependent R (E ∘ v) ∧ Submodule.span R (Set.range (E ∘ v)) = ⊤ := by
  refine ⟨hli.map' E.toLinearMap E.ker, ?_⟩
  rw [Set.range_comp, ← E.coe_toLinearMap, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]

theorem bases_transfer : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  intro S S' A _ Ag _ φ L _ k R _ x y h hc _ hfst m b b' hb' hli hsp
  let c := chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc
  have hc' : ∀ _ : Fin 1, inv h ≫ (snd (Over.mk x) Ag).left ≫ φ = (snd (Over.mk y) A).left := fun _ => by
    rw [hc 0, IsIso.inv_hom_id_assoc]
  let c' := chartPullUnLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left)
    (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) (inv h) hc'
  have hfst' : inv h ≫ (fst (Over.mk x) Ag).left = (fst (Over.mk y) A).left := by
    rw [← hfst, IsIso.inv_hom_id_assoc]
  let F := pullLin A Ag L (L.pull φ) k k y x c hfst
  let G := pullLin Ag A (L.pull φ) L k k x y c' hfst'
  have GF : ∀ s : LB.Sec (LPow A L k (Over.mk y)),
      GlobalTheory.SecTwist.pullSec c' (GlobalTheory.SecTwist.pullSec c s) = s :=
    pullSec_pullSec c' c (IsIso.inv_hom_id h) (fun _ => rfl)
  have FG : ∀ s : LB.Sec (LPow Ag (L.pull φ) k (Over.mk x)),
      GlobalTheory.SecTwist.pullSec c (GlobalTheory.SecTwist.pullSec c' s) = s :=
    pullSec_pullSec c c' (IsIso.hom_inv_id h) (fun _ => rfl)
  let E : SecM A L k (Over.mk y) ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)] SecM Ag (L.pull φ) k (Over.mk x) :=
    { F with
      invFun := G
      left_inv := fun n => congrArg (SecM.ofSec A) (GF (SecM.toSec A n))
      right_inv := fun n => congrArg (SecM.ofSec Ag) (FG (SecM.toSec Ag n)) }
  have hv : (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) =
      E ∘ fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y)) :=
    funext fun i => by rw [hb' i]; rfl
  have key := li_span_map E _ hli hsp
  rw [← hv] at key
  exact key

end GlobalTheory.SecBasisTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureRigidifications
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqTower.StageExists

theorem hasSignature_map_conj {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

def withIdx {D : D7} (V : HSp D) (p : ℕ) : HSp D := { V with sig := fun _ => (V.rank - p, p) }

theorem withIdx_sigOK {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) : (withIdx V p).SigOK := by
  intro σ
  show Formalism.UG.HasSignature (V.gram.map σ) (V.rank - p) p
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_conj (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1


open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem rig_exists {D : D7} {V : HSp D} {p : ℕ} (h : NegIdx V p) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  obtain ⟨r, e, hr⟩ := _root_.GlobalTheory.RigExists.exists_rig D (withIdx V p) Λ (withIdx_sigOK h) hΛ
  exact ⟨⟨r.Λ, r.β, r.s, r.B⟩, e, hr⟩


open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in
theorem vac_exists {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S WW : HSp D} {p q : ℕ} (hS : NegIdx S p) (hW : NegIdx WW q) {r : Rig S} {rW : Rig WW} (h : r.Is) (h' : rW.Is) :
    (∃ f, IsVacO ψ θ (neg S) WW (fun τ => -r.s τ) rW.s r.Λ rW.Λ f) ∧ ∃ f, IsVacO ψ θ S WW r.s rW.s r.Λ rW.Λ f := by
  have hneg : IsSelfDualC (neg S) r.Λ := by
    refine ⟨h.1.1, fun y => (h.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  constructor
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (neg (withIdx S p)) (withIdx WW q) (fun τ => -r.s τ) rW.s
      (sigOK_sgn true (withIdx_sigOK hS)) (withIdx_sigOK hW) (fun τ => isCartanInv_sgn true S τ (h.2.2 τ).1)
      (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ hneg h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩
  · obtain ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hψ hθ (withIdx S p) (withIdx WW q) r.s rW.s
      (withIdx_sigOK hS) (withIdx_sigOK hW) (fun τ => (h.2.2 τ).1) (fun τ => (h'.2.2 τ).1) r.Λ rW.Λ h.1 h'.1
    exact ⟨f, h0, h1, ⟨a, b, c, d⟩, h2, h3, h4⟩


end GlobalTheory.SqTower.StageExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsLowerBoundAmpleMinusTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSLowerTwist

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  intro hC hHS k _ X _ p D hX P b s t hG c hgen hreg hnef hsemi a ha ε hε
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX P.L P.A a ha
  have hε3 : 0 < ε / 3 := by positivity
  have h1 := _root_.GlobalTheory.HSNef.lc_add_div_sub_le k X p D hX P b s t hG c hgen hreg (ε / 3) hε3
  have h2 : ∀ᶠ n : ℕ in atTop, a / ((D + 1).factorial : ℝ) - ε / 3 <
      α n / (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
    (hlim.div_const ((D + 1).factorial : ℝ)).eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, ⟨hn1, hn2⟩, hn0⟩ := ((h1.and h2).and (eventually_gt_atTop 0)).exists
  have h3 := GlobalTheory.HSNef.lowerBound_along_div hC hHS k X p D hX P c n (α n) hn0 hnef hsemi hG.ample hG.nef.semiPos (hα n) (ε / 3) hε3
  filter_upwards [hn1, h3] with M hM1 hM3
  have hM : (0 : ℝ) ≤ (M : ℝ) ^ (D + 1) := by positivity
  rw [div_right_comm] at hM3
  have h4 := mul_le_mul_of_nonneg_right hn2.le hM
  nlinarith

end GlobalTheory.HSLowerTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_boundary_local_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  first | exact @GlobalTheory.BdEquation.exists_reduced_equation | exact GlobalTheory.BdEquation.exists_reduced_equation | (intros; apply GlobalTheory.BdEquation.exists_reduced_equation <;> assumption)
end

