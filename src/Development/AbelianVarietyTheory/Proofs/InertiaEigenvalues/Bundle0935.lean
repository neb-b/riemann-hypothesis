module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0932
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleFormsSmoothAdmissibleUnitaryModule
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefRowMod

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace


set_option maxHeartbeats 1000000 in
theorem main : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G]
    (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0),
    GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt →
    ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx j
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hmod := hcore.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame Y.hF (Y.PW j) := Y.stdPsi.2 j
  have hcc := _root_.GlobalTheory.CongConjugate.congConj D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MW j (sg0 D A3.A)) (θ := R.θ) (R.νW j) (R.fdW j)
    (Y.PW j) hSA hSig hθ hHaar hFD
  have hT := Y.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (Y.PW j) hStd (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) ρ) : ℚ) : ℝ)) * (RealDat.nP F.lv2 false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D A3.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (R.MW j (sg0 D A3.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∀ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)),
      ∃ b, Mult.IsMultIP (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (Y.PW j) hx hy
    exact hSA _ hSig _ R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (R.MW j (sg0 D A3.A)) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW j (sg0 D A3.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc j)) ∘ₗ (Y.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (Y.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart R.θ (R.MW j (sg0 D A3.A)) (levS _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf j (sg0 D A3.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (Y.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (R.MW j (sg0 D A3.A))
            ρ := principalLevelFrame.actM (Y.PW j) (R.MW j (sg0 D A3.A))
            C := principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A))
            B := fun x y => (c : ℂ) * Mult.ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (Y.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [_root_.GlobalTheory.SchurPairingInvariant.ipM_actM D (Wc D j) _ R.θ (R.MW j (sg0 D A3.A)) D.R.r (Y.PW j) (R.νW j) (R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (Y.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (Y.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (Y.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (R.MW j (sg0 D A3.A)) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.νW j) (R.fdW j) (φ x) (φ y) = _
              rw [GlobalTheory.RowModCanon.ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _
                (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, Y.prtWE j σ]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc,
    Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl, fun y => hφ y⟩

end GlobalTheory.RefRowMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SGoodOfLevelShape
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RecT.Thread

section Level

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def LevelShape (π : NG.AutRep L n) : Prop :=
  ∃ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ NG.HypOutside J χ B ∧
    (∃ f ∈ NG.isoTyp π.ρ π.S, f ∈ NG.TypeSp π.ρ J χ ∧ f ≠ 0) ∧
    ∀ s : SplitPlace L, s.v ∈ B → ∃ s₀ : SplitPlace L, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield L)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelUni J χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield L))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 → ξ u = 1))

theorem good_of_levelShape (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing)
    (π : NG.AutRep L n) (h : LevelShape π) :
    ∀ (s : SplitPlace L) (σ : IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS π.S s σ →
      GlobalTheory.RecT.Good (GlobalTheory.LocLanglands.cls σ) := by
  obtain ⟨J, χ, B, hc, hH, ⟨f, hf, hfT, hf0⟩, hB⟩ := h
  intro s σ hσ
  by_cases hs : s.v ∈ B
  · obtain ⟨s₀, hv, hB'⟩ := hB s hs
    rcases hB' with ⟨r, ξ, hP⟩ | ⟨hk, r, ψ₀, ξ, hU, hψ, ht⟩
    · exact GlobalTheory.AVGood.good_of_toral (GlobalTheory.ParaToral.toral_of_levelPara hBZ hZ L n π.toAlgWt π.S π.irrS J χ hc s₀ r ξ hP
        f hf hfT hf0 s hv.symm σ hσ)
    · exact GlobalTheory.AVGood.good_of_fixed_KOne hZ hk _ (GlobalTheory.UniDepthZero.main L n π.toAlgWt π.S π.irrS J χ hc s₀ r ψ₀ ξ hU hψ ht
        f hf hfT hf0 s hv.symm σ hσ)
  · exact GlobalTheory.AVGood.good_of_isSpherical hBZ _ (GlobalTheory.SphHyp.isSpherical_of_hypOutside L n π.toAlgWt π.S π.irrS J χ hc B hH
      f hf hfT hf0 s hs σ hσ)

end Level

end GlobalTheory.RecT.Thread

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.SphInertRef

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : Formalism.IndefR.Links.RealDat3 D A3 Ks}
  {F : Formalism.IndefR.Links.Face3 D A3} {X0 : BaseLevelRowSide D} {Y : Read R.toRealDat F.lv2 X0} {M : MtFam D}

theorem rt_real_eq_of_lev (hMA : MtAd Y M) (i : Fin D.R.m) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1))
    (κ : GAf D.host.E D.R.nV)
    (hJ : (hMA.PV i).ψ κ ∈ Formalism.IndefR.Links.levS _ (R.toRealDat.βV i)
      (Formalism.IndefR.RecTie.datVP R.toRealDat i (Y.tupT D.what₂.mu0) (R.toRealDat.levR F.lv2 false)))
    (hχ : Formalism.IndefR.Lev.levChi _ (R.toRealDat.βV i)
      (Formalism.IndefR.RecTie.datVP R.toRealDat i (Y.tupT D.what₂.mu0) (R.toRealDat.levR F.lv2 false)) ((hMA.PV i).ψ κ) = 1) :
    NG.rt D.host.E D.R.nV κ ((M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x) =
      (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x := by
  have h0 : Formalism.IndefR.RecTie.Used0 D D.what₂.mu0 := Or.inl rfl
  funext g
  apply (hMA.eW _ h0 i).injective
  have e1 := hMA.read _ h0 i x (g * κ)
  have e2 := hMA.read _ h0 i x g
  have e3 := (Y.IL.jMt _ h0 i x).2.2 _ hJ ((hMA.PV i).ψ g)
  rw [hχ, ← map_mul] at e3
  exact e1.trans (e3.trans ((one_smul ℂ _).trans e2.symm))

end Read

end GlobalTheory.SphInertRef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SymplecticPairingHalfLatticesEqProdPrimitive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatPairing


set_option synthInstance.maxHeartbeats 400000 in
theorem trace_mul_int {D : D7} {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin b) (Fin a) (EAf D))
    (hA : IsIntM A) (hB : IsIntM B) :
    Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hB j i)


set_option synthInstance.maxHeartbeats 400000 in
theorem resS_trace_mul {D : D7} (PP : Pl D.host.E) {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D))
    (B : Matrix (Fin b) (Fin a) (EAf D)) (hA : IsIntM A) (hB : IsIntM B)
    (h : Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP ⟨Matrix.trace (A * B), h⟩ = Matrix.trace (redM PP A * redM PP B) := by
  have h1 : (⟨Matrix.trace (A * B), h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ∑ i, ∑ j, (⟨A i j, hA i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨B j i, hB j i⟩ := by
    apply Subtype.ext
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul]
  rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [redM, dif_pos (hA i j), dif_pos (hB j i)]

theorem inv_isPrimitive {R : Type} [CommRing R] (χ : AddChar R ℂ) (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  intro a ha h1
  apply h (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h1 x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply] using this

theorem exists_primitive {E : Type} [Field E] [NumberField E] (PP : Pl E) :
    ∃ χ : AddChar (kP PP) ℂ, χ.IsPrimitive := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  letI : Field (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 E ⧸ PP.asIdeal) := Fintype.ofFinite _
  exact ⟨_, AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 E ⧸ PP.asIdeal)⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem pairing_eq_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) → ∀ u : WO S T, IsHalf e u → IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → ψ (symplO S T x u) = ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj S T βS βT x))) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT Q e he hQ ϖ hϖ hϖQ
  by_cases h0 : S.rank = 0 ∨ T.rank = 0
  · refine ⟨fun PP => (exists_primitive PP).choose, fun PP _ => (exists_primitive PP).choose_spec, ?_⟩
    intro x _ _ u _ _
    have hz : hO S T x u = 0 := by
      unfold hO
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
    rw [symplO, hz, mul_zero, map_zero, AddChar.map_zero_eq_one]
    symm
    refine Finset.prod_eq_one fun PP _ => ?_
    have : ∀ (A : Matrix (Fin T.rank) (Fin S.rank) (kP PP.1)) (B : Matrix (Fin S.rank) (Fin T.rank) (kP PP.1)),
        Matrix.trace (A * B) = 0 := by
      intro A B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
    rw [this, AddChar.map_zero_eq_one]
  · rw [not_or] at h0
    obtain ⟨χ, hχ, hform⟩ := _root_.GlobalTheory.IdemCharLift.factor_prim D ψ Q e he ϖ hϖ hϖQ
      (_root_.GlobalTheory.ScalarSelfDual.int_iff_dual D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT (Nat.pos_of_ne_zero h0.1) (Nat.pos_of_ne_zero h0.2) Q e he hQ)
    refine ⟨fun PP => (χ PP)⁻¹, fun PP hPP => inv_isPrimitive _ (hχ PP hPP), ?_⟩
    intro x _ hx u hu hux
    have heu : e • u = u := by
      funext i j
      exact hu i j
    have hsm : (u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) = incA D (ϖ : D.host.E) • u := rfl
    have hZ : e * (-hO S T u x) = -hO S T u x := by
      rw [mul_neg, ← GlobalTheory.PlaceModel.hO_smul_left, heu]
    have htr : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) =
        -Matrix.trace (frMapAdj S T βS βT x * frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [mul_neg, map_neg, ← GlobalTheory.PlaceModel.hO_smul_left, ← hsm, GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT]
    have hint := trace_mul_int _ _ hx hux
    have hint' : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [htr]; exact Subring.neg_mem _ hint
    have hs : symplO S T x u =
        Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (-hO S T u x)) := by
      rw [GlobalTheory.PlaceModel.symplO_skew S T u x, symplO, mul_neg, map_neg]
    rw [hs, hform _ hZ hint']
    refine Finset.prod_congr rfl fun PP _ => ?_
    have h2 : (⟨_, hint'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -⟨_, hint⟩ := Subtype.ext htr
    rw [h2, map_neg, resS_trace_mul PP.1 _ _ hx hux, AddChar.inv_apply, Matrix.trace_mul_comm]

end GlobalTheory.FlatPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProduct
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.RSEulerId

theorem thetaZ_eq_mul_eulD : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a π ha hu T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hℓ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, hcore⟩ :=
    GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums E a π ha hu T hT
  have hF : φ.1 ∈ GlobalTheory.JSW.mspanR π₀ := hφ.elim (fun h => Submodule.mem_sInf.2 fun _ hS => hS.1 φ h) id
  have hπu : π₀.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  have hFc : Continuous φ.1 := by
    obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπu φ.1 hF
    have h0 := (hw []).2
    rw [GlobalTheory.JSW.word_nil, hψ] at h0
    exact h0.cont
  refine ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, fun μ _ 𝓕 h𝓕 => ?_⟩
  obtain ⟨𝓕₀, h𝓕₀⟩ := _root_.GlobalTheory.CellDec.exists_isFundamentalDomain_NE E a μ
  obtain ⟨H, hHc, hH1, hH⟩ := hcore μ 𝓕₀ h𝓕₀
  refine ⟨H, hHc, hH1, fun x hx => ?_⟩
  obtain ⟨hHx, heq⟩ := hH x hx
  have hU := GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding E a ℓ hℓ π₀ hπu φ.1 hF Φ hΦs.continuous hΦc hΦr J η μ 𝓕 𝓕₀ h𝓕 h𝓕₀ x
  have hfin := _root_.GlobalTheory.RSThetaSelf.lintegral_ne_top E a ℓ π₀ ω hω hc φ.1 hF Φ hΦs hΦc hΦr hΦp J η μ 𝓕 h𝓕 x hx
  have hZ := _root_.GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral E a ℓ π₀ φ.1 hF hFc Φ hΦs.continuous hΦr hΦp J η μ 𝓕 h𝓕 x hfin
  rw [hU, heq] at hfin hZ
  refine ⟨hHx, fun h => hfin (by rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hHx).ne']), ?_⟩
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hHx.le]

end GlobalTheory.RSEulerId
end

