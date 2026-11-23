module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CrysTwistBack

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {a : ℕ}

theorem isCrysAt_of_tw {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
    [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ)
    (r : ↥Gw →* GL (Fin a) (Om l)) (h : IsCrysAt P Bw (UpperTheory.V.Af.tw r c))
    (hc : IsCrysAt P Bw (GlobalTheory.TripleGal.rk1 c)) : IsCrysAt P Bw r := by
  obtain ⟨L₁, r₁, m₁, hr₁⟩ := h
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  have hp := (local_ext P Bw l₁ r₁).1.2 hr₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    simp [GlobalTheory.TripleGal.rk1]
  have hM : IsModel Bw r L (UpperTheory.V.Af.tw r₁' d⁻¹) := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        ((UpperTheory.V.Af.tw r c g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((UpperTheory.V.Af.tw r₁' d⁻¹ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul, map_mul, e, UpperTheory.V.Af.tw_val, Matrix.smul_apply, smul_eq_mul,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀,
      show algebraMap ↥L.1 (Om l) (d g : ↥L.1) = (c g : Om l) from hcd g, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  refine ⟨L, _, hM, ?_⟩
  let θ : ↥(GK Bw.Kw) →* (↥L.1)ˣ := d.comp Bw.e.symm.toMonoidHom
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T Bw.Kw L (Bw.repE L (UpperTheory.V.Af.tw r₁' d⁻¹)) (Bw.repE L r₁') θ
    (fun g x => ?_) ?_).2 hp
  · rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul]
    change _ = ((d (Bw.e.symm g) : ↥L.1) * ((d⁻¹ (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)) • _
    rw [MonoidHom.inv_apply, Units.mul_inv, one_smul]
  · refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD Bw.Kw) (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) hq
    change (Bw.repE L c₂' g x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm g))

end GlobalTheory.CrysTwistBack

namespace GlobalTheory.CrysTwistBack

theorem isSpherical_twist_of_unr {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (κ : HChar E) (hκ : κ.UnrAt w)
    (h : GlobalTheory.SmGL.IsSpherical σ.ρ) :
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a κ w) (CuspSub.isOpen_ker_locDet κ w)).ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv0⟩
  have hg : g.1 ∈ GlobalTheory.LFun.KGL w (n := a) := hK ▸ g.2
  have h1 : CuspSub.locDet a κ w g.1 = 1 := hκ _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)
  have h3 := hv g
  show ((CuspSub.locDet a κ w g.1 : ℂˣ) : ℂ) • σ.ρ g.1 v = _
  rw [h1, Units.val_one, one_smul]
  exact h3

theorem holds_good_crys : AutomorphicFormsFiniteGL → HeckeLAdicCharacterAbove → Holds .csd .crys → Holds .good .crys := by
  intro hF hA hC E Ω _ _ _ _ _ _ l _ ι a ha π χ hs r hr w hw
  intro P AI hT A hAw O _ _ _ Bw hj σ hσ hsph
  obtain ⟨κ, m, hκ, hκu, hcs⟩ := _root_.GlobalTheory.GoodCsdTwist.exists_goodCsd_twist hF E l a ha π χ hs w hw
  obtain ⟨art, hart, hch⟩ := (GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt
    GlobalTheory.globalArtinReciprocity_holds).1 E Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hch l ι κ m (fun k _ => hκ k)
  have hw' : Weak (π.twist κ) ι (UpperTheory.V.Af.tw r μ) :=
    ⟨UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ hr.1 hμc, UpperTheory.V.Af.Cq.attTwist E Ω l ι a r π hr.2 art κ m μ hart hμ⟩
  have h1 := hC E Ω l ι a ha (π.twist κ) (quadChar E ^ a) hcs (UpperTheory.V.Af.tw r μ) hw' w hw P AI hT A hAw O Bw hj _
    (hσ.twist κ) (isSpherical_twist_of_unr a w σ κ hκu hsph)
  have h2 := (hA E Ω l P AI hT ι art hart κ m μ (fun k _ => hκ k) hμc hμ w A hAw O Bw hj).2.2.1 hκu
  obtain ⟨T⟩ := hT
  exact isCrysAt_of_tw T Bw (μ.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype) h1 h2

end GlobalTheory.CrysTwistBack

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeDetIdealCharacterEqConstMulDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.DetIdChi

open Matrix

theorem heq_transport (D : D7) {n N : ℕ} (h : n = N) (K : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (K' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (hK : HEq K K') :
    (IsSDLat D.host.E n K → IsSDLat D.host.E N K') ∧ TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) K = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) K' := by
  subst h
  cases eq_of_heq hK
  exact ⟨id, rfl⟩

def coGL {E : Type} [Field E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : GL (Fin N) E :=
  ⟨LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)), LinearMap.toMatrix' ((f.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)),
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩

theorem toLE_coGL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : toLE (coGL f) = f := by
  refine LinearEquiv.ext fun x => ?_
  rw [toLE_apply]
  show LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)) *ᵥ x = f x
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem inv_mul_mem_UJ {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (G : Matrix (Fin N) (Fin N) E)
    (crd co : GL (Fin N) E) (h1 : cT σ crd.1 * crd.1 = G) (h2 : star co.1 * co.1 = G) : crd⁻¹ * co ∈ UJ σ G := by
  show cT σ ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * G * ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = G
  rw [← Emat.star_eq_cT σ hσ] at h1 ⊢
  rw [Units.val_mul, star_mul, ← h1]
  have e : star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have e' : (crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := Units.mul_inv crd
  calc star (co : Matrix (Fin N) (Fin N) E) * star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (star (crd : Matrix (Fin N) (Fin N) E) * crd) *
        (((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * co)
      = star (co : Matrix (Fin N) (Fin N) E) * (star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E)) *
        ((crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) * co := by
          simp only [Matrix.mul_assoc]
    _ = star (co : Matrix (Fin N) (Fin N) E) * co := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
    _ = star (crd : Matrix (Fin N) (Fin N) E) * crd := by rw [h2, h1]

end GlobalTheory.TwV.Xc.DetIdChi

open GlobalTheory.TwV.Xc.DetIdChi in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.chi_detId_kerN_eq : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl j hj
  have hσ : ∀ x : D.host.E, (sigD D : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  set G := gramN D j hj with hG
  set crd := J.A.crd j hj with hcrd
  have hco := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (sigD D : D.host.E →+* D.host.E) hσ (D.R.N j) (D.R.N j) rfl G crd
    (J.pins.crd_orth j hj)).1
  set co : GL (Fin (D.R.N j)) D.host.E := coGL (stdCo (sigD D : D.host.E →+* D.host.E) G) with hcoDef
  have hco2 : star co.1 * co.1 = G := Emat.gram_of_orth _ hσ G _ hco
  set γ₀ := crd⁻¹ * co with hγ₀
  have hγ : γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) G := inv_mul_mem_UJ _ hσ G crd co (J.pins.crd_orth j hj) hco2
  have hr : GlobalTheory.TwU.ratA D.host.F γ₀ ∈ UPts (sigD D) G (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ₀, hγ, rfl⟩
  have hch := _root_.GlobalTheory.TwV.Xc.chiI_hom S hDict hSpl
  refine ⟨chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)), ?_⟩

  have key : ∀ (β : (J.St j hj).Ch) (x : UA D j hj), IsSDLat D.host.E _ (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb) →
      t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb)) =
        chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)) * chiI J (Matrix.GeneralLinearGroup.det x.1) := by
    intro β x hsd
    let y : UA D j hj := ⟨GlobalTheory.TwU.ratA D.host.F γ₀ * x.1, mul_mem hr x.2⟩
    have hlat : latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb = GlobalTheory.TwU.latCo D.sp G crd J.a y.1 ((J.St j hj).K β).lev.Lb := by
      rw [← GlobalTheory.TwU.latCo_eq_latK G co (toLE_coGL _), show co = crd * γ₀ by rw [hγ₀, mul_inv_cancel_left]]
      exact GlobalTheory.TwU.latCo_mul G crd γ₀ hγ J.a x.1 _
    obtain ⟨hg, hcar, d, hdd, hdet⟩ := _root_.GlobalTheory.TwV.conj_crd_unitary_carries J.A J.dtU J.a J.pins J.tie j hj β y
    rw [J.base j hj β] at hcar
    have hstd : IsSDLat D.host.E (D.R.N j) (StandardLatticesGL3.stdL D (D.R.N j)) := by
      have := ((t.O u μ).L0 j).2
      rwa [Formalism.L2.Ker.initial_lattice_eq_standard] at this
    rw [hlat] at hsd ⊢
    have hrel := J.rel (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩ _ hg hcar d hdet
    have hid := t.idl_ok.2.2.2.2 (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩
    rw [hrel] at hid
    have hx1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj x
    have hy1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj y
    have hr1 : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) ∈ U1 (sigD D) := by
      have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) =
          Matrix.GeneralLinearGroup.det y.1 * (Matrix.GeneralLinearGroup.det x.1)⁻¹ := by
        show _ = Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀ * x.1) * _
        rw [MonoidHom.map_mul Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) x.1, mul_inv_cancel_right]
      rw [e]
      exact mul_mem hy1 (inv_mem hx1)
    rw [← hch.1 _ hr1 _ hx1, show Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) * Matrix.GeneralLinearGroup.det x.1 =
      Matrix.GeneralLinearGroup.det d.1 by rw [hdd]; exact (map_mul _ _ _).symm, hch.2.2.1 d]
    show t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (D.R.N j)) (⟨_, hsd⟩ : SDLat D.host.E (D.R.N j)).1) = _
    rw [← hid, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl
  intro La hLa hsd
  obtain ⟨⟨hr', -⟩, -, hheq, hdt⟩ := hDict j hj La hLa
  obtain ⟨h1, h2⟩ := heq_transport D hr' _ _ hheq
  rw [h2, hdt]
  exact key _ _ (h1 hsd)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProduct
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieChiH_of_parts : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d ι j hj cB sc cK hsc La hLa c' L' hL'
  have hLat := S.Y.Rep_lat j La hLa
  have hsC := _root_.GlobalTheory.TwV.DelB.scalAt_all S hD d j hj La (c', L') hLat hL'
  have he := _root_.GlobalTheory.TwV.DelB.eFac_mul_pPow _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)) j La (c', L')
  have h2 := hsc La (c', L') hLat hL'
  show cK * S.E.iK (S.Y.eS j La * (S.Y.eT j (c', L'))⁻¹) * cB j La * (pPow (sysS H X std) j La (c', L') * ι (d.sC S j La (c', L'))) = _
  rw [hsC]
  have hι : ∀ x y : ℂ, ι (x * y) = ι x * ι y := map_mul ι
  simp only [hι]
  linear_combination (cK * cB j La * ι (d.uS S j La) * ι (d.uT S j (c', L')) *
      ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ)) * he +
    ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ) * h2

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameScalarOddPositionsDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem zpow_toNat_div' {K : Type} [Field K] (x : K) (hx : x ≠ 0) (e : ℤ) :
    x ^ e.toNat * (x ^ (-e).toNat)⁻¹ = x ^ e := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx]
  congr 1
  omega

theorem blk_scal_odd {K : Type} [Field K] (c δ : K) (hc : c ≠ 0) (hδ : δ ≠ 0) (N : ℕ) (hN : 1 ≤ N) (cM sz : ℤ)
    (h0 : 0 ≤ (N : ℤ) * cM - sz) :
    ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat *
      ((δ⁻¹) ^ (cM - sz).toNat * ((c * δ⁻¹) ^ N) ^ (cM - (N : ℤ) * cM + sz).toNat) *
      ((δ⁻¹) ^ (-(cM - sz)).toNat * ((c * δ⁻¹) ^ N) ^ (-(cM - (N : ℤ) * cM + sz)).toNat)⁻¹ =
    c ^ sz * δ ^ (-cM) := by
  have hκ : c * δ⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hδ)
  have hd : δ⁻¹ ≠ 0 := inv_ne_zero hδ
  have hκN : (c * δ⁻¹) ^ N ≠ 0 := pow_ne_zero _ hκ
  have e1 : ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat = (c * δ⁻¹) ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) := by
    rw [← pow_mul, ← zpow_natCast]
    congr 1
    push_cast [Int.toNat_of_nonneg h0, Nat.cast_sub hN]
    ring
  calc _ = ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat *
        ((δ⁻¹) ^ (cM - sz).toNat * ((δ⁻¹) ^ (-(cM - sz)).toNat)⁻¹) *
        (((c * δ⁻¹) ^ N) ^ (cM - (N : ℤ) * cM + sz).toNat * (((c * δ⁻¹) ^ N) ^ (-(cM - (N : ℤ) * cM + sz)).toNat)⁻¹) := by
          ring
    _ = (c * δ⁻¹) ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) * (δ⁻¹) ^ (cM - sz) *
        (c * δ⁻¹) ^ ((N : ℤ) * (cM - (N : ℤ) * cM + sz)) := by
          rw [zpow_toNat_div' _ hd, zpow_toNat_div' _ hκN, e1, ← zpow_natCast (c * δ⁻¹) N, ← zpow_mul]
    _ = c ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz) + (N : ℤ) * (cM - (N : ℤ) * cM + sz)) *
        δ ^ (-(((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) + -(cM - sz) + -((N : ℤ) * (cM - (N : ℤ) * cM + sz))) := by
          rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', inv_zpow', zpow_add₀ hc, zpow_add₀ hδ, zpow_add₀ hδ]
          ring
    _ = _ := by
          congr 2 <;> ring


set_option maxHeartbeats 1000000 in
theorem scal_tauV : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → GlobalTheory.FrameB.sS X Kc j (GlobalTheory.FrameB.kV Kc fd c j La') * GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') * (GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La'))⁻¹ = ∏ τ, if IsOddPos (pos.symm τ).2 then c ^ szT X D pos j τ * ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ^ cT1 X D pos j τ else 1 := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd c hc j hN La' M hU hFr ν hν
  obtain ⟨-, hsz, -, hle, -⟩ := _root_.GlobalTheory.TwV.DelA.size_first_last_rows X D pos j hN ν hν
  have hN1 : 1 ≤ NN X.G.P.m X.t j := by unfold NN; omega

  have hdet : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (GlobalTheory.FrameB.mk Kc fd j La' v s).det =
      Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) := by
    intro v s
    unfold GlobalTheory.FrameB.mk
    rw [det_mAt, hFr v, Matrix.det_submatrix_equiv_self, RingHom.map_det (ρ v)]
    rfl
  have hdet0 : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (GlobalTheory.FrameB.mk Kc fd j La' v s).det ≠ 0 := by
    intro v s
    rw [hdet]
    exact (((M.isUnit.map (Matrix.detMonoidHom))).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) |>.ne_zero

  have hbd : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)),
      0 ≤ (NN X.G.P.m X.t j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2 := by
    intro b
    have h1 : szMu X j b.1 b.2 = szT X D pos j (pos b) := by
      show _ = szMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h2 : cMu X j b.1 b.2 = cT1 X D pos j (pos b) := by
      show _ = cMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    rw [h1, h2, hsz, ← hN.1]
    have : ∑ r : Fin (D.R.N j), (ν (pos b) r : ℤ) ≤ ∑ _r : Fin (D.R.N j), cT1 X D pos j (pos b) := by
      refine Finset.sum_le_sum fun r _ => ?_
      have := hle (pos b) (Fin.castLE (rk_le X D hN) r)
      simpa [extNu] using this
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hkN : GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') =
      ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), if IsOddPos b.2 then
        ((GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2).det⁻¹) ^ (exY X j b.1 b.2).toNat *
          (GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 ^ NN X.G.P.m X.t j) ^ (exT X j b.1 b.2).toNat else 1 := by
    unfold GlobalTheory.FrameB.kN
    rw [Fintype.prod_sigma]
  have hkD : GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') =
      ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), if IsOddPos b.2 then
        ((GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2).det⁻¹) ^ (-exY X j b.1 b.2).toNat *
          (GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 ^ NN X.G.P.m X.t j) ^ (-exT X j b.1 b.2).toNat else 1 := by
    unfold GlobalTheory.FrameB.kD
    rw [Fintype.prod_sigma]
  rw [← Fintype.prod_equiv pos _ _ (fun _ => rfl), hkN, hkD, GlobalTheory.FrameB.sS, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  beta_reduce
  rw [Equiv.symm_apply_apply]
  by_cases ho : IsOddPos b.2
  · simp only [if_pos ho]
    have hw : GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2 = GlobalTheory.FrameB.mk Kc fd j La' b.1 b.2 := by
      unfold GlobalTheory.FrameB.wV; rw [if_pos ho]
    have hk : GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 = c * (GlobalTheory.FrameB.mk Kc fd j La' b.1 b.2).det⁻¹ := by
      unfold GlobalTheory.FrameB.kV; rw [if_pos ho]
    rw [hw, hk, exY, exT, blk_scal_odd c _ hc (hdet0 b.1 b.2) _ hN1 _ _ (hbd b)]
    have h1 : szMu X j b.1 b.2 = szT X D pos j (pos b) := by
      show _ = szMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h2 : cMu X j b.1 b.2 = cT1 X D pos j (pos b) := by
      show _ = cMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h3 := (_root_.GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU b.1 b.2).2
    rw [if_pos ho] at h3
    rw [h1, h2, hdet, h3, ← zpow_mul]
    congr 2
    ring
  · simp only [if_neg ho]
    simp

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleJointDictionary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.joint_dict : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  intro j hj La hLa
  cases j with
  | zero =>
    have hp := (_root_.GlobalTheory.TwV.Joint.isPt_pt_zero t std J La).1
    exact ⟨hp, _root_.GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul t std J La hLa, _root_.GlobalTheory.kerN_zero_eq_latK_pt t std J La, _root_.GlobalTheory.joint_dt_eq_det_of_isPt t std J 0 hj La _ hp⟩
  | succ j =>
    have hp := (_root_.GlobalTheory.TwV.Joint.pt_succ_isPt t std J j hj La).1
    exact ⟨hp, _root_.GlobalTheory.TwV.Joint.pt_succ_coset t std J j hj La hLa, _root_.GlobalTheory.TwV.Joint.kerN_succ_heq t std J j hj La hLa, _root_.GlobalTheory.joint_dt_eq_det_of_isPt t std J (j + 1) hj La _ hp⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumEqOfLatticeTuplesAgreeAway
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.xiM_eq_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb La' Lb' hab hab'
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hj1 : j + 1 ≤ D.R.m := hj
  funext z
  rw [_root_.GlobalTheory.TwV.Xc.xiM_eq_adelic S hD hS j hj1 (hN j) (hN (j + 1)) La La' z, _root_.GlobalTheory.TwV.Xc.xiM_eq_adelic S hD hS j hj1 (hN j) (hN (j + 1)) Lb Lb' z]
  have hc : J.chart std j (Nat.le_of_succ_le hj1) La = J.chart std j (Nat.le_of_succ_le hj1) Lb := by
    obtain ⟨h1, h2, h3, -⟩ := hab
    rcases La with ⟨c, a⟩
    rcases Lb with ⟨c', b⟩
    simp only at h3
    subst h3
    exact _root_.GlobalTheory.TwV.Xc.chart_eq_of_comp S hD hS j _ c a b h1 h2
  have hc' : J.chart std (j + 1) hj1 La' = J.chart std (j + 1) hj1 Lb' := by
    obtain ⟨h1, h2, h3, -⟩ := hab'
    rcases La' with ⟨c, a⟩
    rcases Lb' with ⟨c', b⟩
    simp only at h3
    subst h3
    exact _root_.GlobalTheory.TwV.Xc.chart_eq_of_comp S hD hS (j + 1) _ c a b h1 h2
  rw [hc, hc']
  refine congrFun (S.law.away j hj1 _ _ (J.pt std j _ Lb) (J.pt std (j + 1) hj1 Lb') (J.pt std j _ La) (J.pt std (j + 1) hj1 La') ?_) _
  intro v' hv'
  have hne : v' ≠ ((A0 J).pl v).1 := fun h => (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hS).2.2.1 v' hv' (h ▸ ((A0 J).pl v).2)
  exact ⟨(GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j _ La Lb hab).1 v' hne, (GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v (j + 1) hj1 La' Lb' hab').1 v' hne⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeries
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelB.serAt_all : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos d ι hι j hj La La' hLa hLa'
  have hr := _root_.GlobalTheory.TwV.DelB.sysS_ranks S
  have hu := _root_.GlobalTheory.TwV.DelB.Dec.eM_mul_star S d
  have hp := _root_.GlobalTheory.TwV.DelB.pullAt_of_dict S hDict d j hj La La' hLa hLa'
  have hs := _root_.GlobalTheory.TwV.DelB.pullbackScalar_ne_zero S d j hj La La' hLa hLa'
  exact _root_.GlobalTheory.TwV.DelB.frecG_pull D _ (sysS H X std) S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) S.lam ι hι (J.rho std) hPos d.eM
    (ltC S.g S.hLT) j La La' (hu j La) (hu (j + 1) La') t.B t.χ (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT hPair
    (hr.1 ▸ hj) hLa hLa' (d.sP S j La La') (thCl (X := sysS H X std) t u μ (clsAt X H) j La La') hs hp
end

