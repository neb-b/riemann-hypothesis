module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertible
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem det_map_ringHom {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem frInv_fdOfCharts {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) : FrInv (fdOfCharts cp a bad) := by
  intro j La v
  simp only [fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self, det_map_ringHom]
  apply IsUnit.map
  rw [Matrix.det_mul, LinearMap.det_toMatrix']
  exact IsUnit.mul (LinearEquiv.isUnit_det' _) (Matrix.isUnits_det_units _)

theorem frames_invertible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    FrInv (J.fd std) ∧ ∀ d : Dec J std, FrInv d.fd2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have h1 : FrInv (J.fd std) := frInv_fdOfCharts _ _ _
  refine ⟨h1, fun d j La v => ?_⟩
  show IsUnit (((star (d.eM j La)).map (J.rho std v)) * (J.fd std).frM j La v).det
  rw [Matrix.det_mul, det_map_ringHom]
  exact IsUnit.mul (IsUnit.map _ (Matrix.isUnit_det_of_left_inverse (_root_.GlobalTheory.TwV.DelB.Dec.eM_mul_star S d j La))) (h1 j La v)

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometry
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.muT_det_ratA : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) ∧ ∀ k (hk : k ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) = ∏ τ, TaylorLogMetric.embT D τ γ.1.det ^ e τ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj
  obtain ⟨e, he, hz⟩ := S.law.mu_rat j hj
  refine ⟨e, he, fun k hk γ hγ => ?_⟩
  have hu := ((_root_.GlobalTheory.TwV.DelB.gMat_det S) k hk).2 γ hγ
  have key : Matrix.GeneralLinearGroup.det (ratA D.host.F γ) =
      Formalism.L2.DIV.ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det γ) := by
    ext
    simp [ratA, Formalism.UG.bc, Formalism.L2.DIV.ratId, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [key]
  have h2 := hz (Matrix.GeneralLinearGroup.det γ) (by simpa using hu.2)
  simpa using h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCoordsConjUnitaryAndCarriesCompanion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCarry

theorem mem_hatL_latAd_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ Formalism.L2.Herm.hatL (F := F) (latAd x Lb) ↔
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ u ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x u
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  exact hrec

theorem carries_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (C y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (M : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) M) (hspan : Submodule.span E (M : Set (Fin N → E)) = ⊤) :
    Formalism.L2.Herm.Carries (F := F) (C * y * C⁻¹) (latAd C M) (latAd (C * y) M) := by
  intro x
  rw [mem_hatL_latAd_iff (C * y) M hfin hspan, mem_hatL_latAd_iff C M hfin hspan, Matrix.mulVec_mulVec, ← Units.val_mul]
  have e : C⁻¹ * (C * y * C⁻¹)⁻¹ = (C * y)⁻¹ := by group
  rw [e]

theorem cT_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {N : ℕ}
    (σ : E →ₐ[F] E) (M : Matrix (Fin N) (Fin N) E) :
    cT (sigR σ R) (M.map (inclE (F := F) R)) = (cT (σ : E →+* E) M).map (inclE (F := F) R) := by
  ext a b
  simp [cT, sigR, inclE]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem conj_mem_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ratA F co * y * (ratA F co)⁻¹ ∈ UPts σ (1 : Matrix (Fin N) (Fin N) E) (FiniteAdeleRing (𝓞 F) F) := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] R) := ((ratA F co : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCm
  set Ci : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (((ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCi
  set Y : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hY
  have hCm' : Cm = co.1.map (inclE (F := F) R) := rfl
  have hJ : cT s Cm * Cm = J.map (inclE (F := F) R) := by
    rw [hCm', cT_map_incl, ← Matrix.map_mul, hco]
  have hy' : cT s Y * J.map (inclE (F := F) R) * Y = J.map (inclE (F := F) R) := hy
  have hCC : Cm * Ci = 1 := by
    rw [hCm, hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  show cT s ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) *
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) * ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R)
  rw [h1, Units.val_mul, Units.val_mul, ← hCm, ← hCi, ← hY, Matrix.mul_one, cT_mul, cT_mul]
  calc cT s Ci * (cT s Y * cT s Cm) * (Cm * Y * Ci)
      = cT s Ci * (cT s Y * (cT s Cm * Cm) * Y) * Ci := by simp only [Matrix.mul_assoc]
    _ = cT s Ci * (cT s Cm * Cm) * Ci := by rw [hJ, hy']
    _ = cT s (Cm * Ci) * (Cm * Ci) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hCC, cT_one, Matrix.one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem exists_stdUnitaryPoint_det_eq_unitaryPoint_det {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), d ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det d = Matrix.GeneralLinearGroup.det y := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set u := Matrix.GeneralLinearGroup.det y with hu
  refine ⟨Units.map (Matrix.scalar (Fin 1) : E ⊗[F] R →+* Matrix (Fin 1) (Fin 1) (E ⊗[F] R)).toMonoidHom u, ?_, ?_⟩
  ·
    have hy' : cT s (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) * J.map (inclE (F := F) R) * (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
        J.map (inclE (F := F) R) := hy
    have hdet := congrArg Matrix.det hy'
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hcT : ∀ M : Matrix (Fin N) (Fin N) (E ⊗[F] R), (cT s M).det = s M.det := by
      intro M
      unfold cT
      rw [Matrix.det_transpose, RingHom.map_det]
      rfl
    have hJu : IsUnit (J.map (inclE (F := F) R)).det := by
      show IsUnit ((inclE (F := F) R).mapMatrix J).det
      rw [← RingHom.map_det]
      refine IsUnit.map _ ?_
      have hco' : IsUnit (co : Matrix (Fin N) (Fin N) E).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
      rw [← hco, Matrix.det_mul]
      refine IsUnit.mul ?_ hco'
      unfold cT
      rw [Matrix.det_transpose]
      show IsUnit (((σ : E →+* E)).mapMatrix (co : Matrix (Fin N) (Fin N) E)).det
      rw [← RingHom.map_det]
      exact hco'.map _
    rw [hcT] at hdet
    have hn : s (u : E ⊗[F] R) * (u : E ⊗[F] R) = 1 := by
      have h2 : (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det = 1 * (J.map (inclE (F := F) R)).det := by
        calc (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det
            = s (u : E ⊗[F] R) * (J.map (inclE (F := F) R)).det * (u : E ⊗[F] R) := by ring
          _ = (J.map (inclE (F := F) R)).det := by rw [hu, Matrix.GeneralLinearGroup.val_det_apply]; exact hdet
          _ = 1 * (J.map (inclE (F := F) R)).det := (one_mul _).symm
      exact hJu.mul_right_cancel h2
    have h1 : (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    show cT s _ * (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) * _ = (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R)
    rw [h1, Matrix.mul_one]
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, hn]
  · ext
    simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_one]

theorem det_conj {R : Type} [CommRing R] {N : ℕ} (C y : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (C * y * C⁻¹) = Matrix.GeneralLinearGroup.det y := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.TwV


open GlobalTheory.ConjCarry in
theorem conj_crd_unitary_carries : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β y
  have hco := hPins.crd_orth i hi
  have hLbf := ((St i hi).K β).lev.Lb_fin
  have hLbs := ((St i hi).K β).lev.Lb_span
  obtain ⟨e1, hCf, hCs⟩ := GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a 1 _ hLbf hLbs
  have e2 := (GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a y _ hLbf hLbs).1
  have e1' : latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb =
      latAd (ratA D.host.F (A.crd i hi)) (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb) := by
    have := e1
    simp only [OneMemClass.coe_one, mul_one] at this
    exact this
  refine ⟨conj_mem_std (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2, ?_, ?_⟩
  · rw [e1', e2]
    exact carries_conj _ _ _ hCf hCs
  · obtain ⟨d, hd, hdd⟩ := exists_stdUnitaryPoint_det_eq_unitaryPoint_det (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2
    refine ⟨⟨d, hd⟩, hdd, ?_⟩
    exact hdd.trans (GlobalTheory.ConjCarry.det_conj (ratA D.host.F (A.crd i hi)) y.1).symm

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepTwistAtClassRepEqCharPowDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem castSt_y_castCls {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) : (castSt h S).y (castCls h i c) = S.y c := by
  subst h; rfl

theorem exists_isDetOf_uPts (D : D7) (i : ℕ) (hi : i ≤ D.R.m)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 := by
  have hd := det_unitary_adelic_point_gram_step_norm_one D i hi x
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1)).toMonoidHom (Matrix.GeneralLinearGroup.det x.1), ?_⟩, ?_⟩
  · simp only [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply, Formalism.L2.DIV.conjId] at hd
    have hd' := congrArg Units.val hd
    simp only [Units.val_mul, Units.coe_map, Units.val_one, MonoidHom.coe_coe] at hd'
    show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, Matrix.scalar_apply, inclE]
    rw [← Algebra.TensorProduct.one_def, mul_one, mul_comm]
    exact hd'
  · ext
    simp [Formalism.L2.Herm.IsDetOf, Matrix.GeneralLinearGroup.det]

theorem tw_at_rep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β c
  obtain ⟨y, hy⟩ := exists_isDetOf_uPts D (j + 1) hj (((I.at' j hj).st.K β).y c)
  rw [J.tw j hj β _ y hy]
  have hrep : (J.St (j + 1) hj).y (castCls (X.onCh j hj) (j + 1) c.1) = ((I.at' j hj).st.K β).y c := by
    have e := J.st j hj
    revert e
    generalize J.St (j + 1) hj = St'
    intro e
    subst e
    rw [castSt_y_castCls]
    exact (GlobalTheory.TwU.StepCharts.y_eq (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) c).symm
  rw [J.tie.dt (j + 1) hj _ y (by rw [hy, hrep])]

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepKernelLatticeEqPointKernelLattice
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.KerSucc

theorem latK_of_renamed {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N n : ℕ} (h : N = n) (hr : n = N) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb Lb₁ : Submodule (𝓞 E) (Fin N → E))
    (J' : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb' : Submodule (𝓞 E) (Fin n → E))
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hy : x = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) y)
    (hLb : Lb' = Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E))) (h₁ : Lb₁ = Lb) :
    HEq ((latK sp J' a y Lb').map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a x Lb₁) := by
  have h1 := (GlobalTheory.reindex_rename_point_det_latK sp hr J' a y Lb').1
  have h3 := (GlobalTheory.reindex_rename_point_det_latK sp h J a x Lb).2.2
  have hy' : y = Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) x := by rw [hy]; exact h1.symm
  rw [hJ, hLb, h₁, hy']
  exact h3

section Unfold

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem gram_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).J (i + 1) La =
      (Formalism.L2.Forms.gramN D (i + 1) hi).reindex (finCongr hr) (finCongr hr) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = _
  rw [chAt, dite_eq_left hi]

theorem base_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).Lb (i + 1) La =
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
        ((reE (E := D.host.E) hr).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = _
  rw [chAt, dite_eq_left hi]

end Unfold

end GlobalTheory.TwV.KerSucc

theorem GlobalTheory.TwV.Joint.kerN_succ_heq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  obtain ⟨hr, hx⟩ := (_root_.GlobalTheory.TwV.Joint.pt_succ_isPt t std J j hj La).1
  have hLb := (GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa).2.1
  have hJ : (J.cp std).J (j + 1) La = (gramN D (j + 1) hj).reindex (finCongr hr.symm) (finCongr hr.symm) :=
    GlobalTheory.TwV.KerSucc.gram_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  have hL : (J.cp std).Lb (j + 1) La = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb.map
      ((reE (E := D.host.E) hr.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) :=
    GlobalTheory.TwV.KerSucc.base_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  exact GlobalTheory.TwV.KerSucc.latK_of_renamed D.sp hr.symm hr _ J.a _ _ _ _ _ _ hJ hx hL hLb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepPointMemDoubleCosetClassRep
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.Joint.pt_succ_coset : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hb := _root_.GlobalTheory.TwV.Joint.basesAt_span t std J (j + 1) La hLa
  obtain ⟨-, -, hU, -, hy⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  have hp := (_root_.GlobalTheory.TwV.Joint.pt_succ_isPt t std J j hj La).2
  obtain ⟨hc, κ, hγ, e⟩ := kaAt_pt H j hj ((I.at' j hj).st.eC.symm La.1).1 ((I.at' j hj).st.eC.symm La.1).2 La.2 _
    (fun v => hb v) (J.pt std (j + 1) hj La) hp
  have ea : (I.at' j hj).st.eC ⟨((I.at' j hj).st.eC.symm La.1).1, ((I.at' j hj).st.eC.symm La.1).2⟩ = La.1 :=
    Equiv.apply_symm_apply _ _
  have hc' : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1 := by
    rw [ea] at hc; exact hc
  refine ⟨_, hγ, ⟨κ.1, (SetLike.ext_iff.1 hU κ.1).2 κ.2⟩, ?_⟩
  rw [hy hc']
  have e2 : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc'⟩ :=
    congrArg _ (Subtype.ext (congrArg (fun a => clsOf (S := (I.at' j hj).st) (H.core j hj) a La.2) ea))
  rw [← e2]
  exact e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesPairOfPullbackKernelFunction
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelB

theorem linSub_smul' {σ R : Type} [Fintype σ] [CommRing R] (B : σ → σ → R) (a : R) (f : MvPowerSeries σ R) :
    linSub B (a • f) = a • linSub B f := by
  rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, GlobalTheory.TwU.LawAll.linSub_C_mul']

theorem map_linSub' {σ R S : Type} [Fintype σ] [CommRing R] [CommRing S] (h : R →+* S) (B : σ → σ → R)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map h (linSub B f) = linSub (fun x y => h (B x y)) (MvPowerSeries.map h f) := by
  unfold linSub
  exact GlobalTheory.PSerLin.map_subst_linear h B f

theorem frecG_pull : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  intro D p _ X E pos fd lam ι hι ρ hρ e c j La La' he he' cc δ B χ SS cl Ξ₀ muT hok hj hL hL' s Θ hs hK
  obtain ⟨-, -, hdiff, hcoef, hsc, hcf, hcf0, hfr⟩ := hok j hj La La' hL hL'
  have hΘ : Differentiable ℂ Θ :=
    _root_.GlobalTheory.TwU.XbEntire.entire_of_pull D cc δ (e j La) (e (j + 1) La') Θ _ s he he' hs hdiff hK
  have hsc' : scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hsc (TaylorLogMetric.Qbar.inv_mem hcf)
  have hser := _root_.GlobalTheory.TwV.SerMap.padicSeries_const_mul D p lam ι hι _ _ _ s hsc' hcoef hK
  have htay := _root_.GlobalTheory.TwV.DelB.tay_pull_linSub D cc δ (e j La) (e (j + 1) La') Θ hΘ
  have hsub := _root_.GlobalTheory.TwV.DelB.sum_pullMat_subBG_reframe D p X E pos fd lam ι hι ρ hρ e c j La La' he he' (fun v => ⟨(hfr v).1, (hfr v).2.1⟩)
  rw [frecG_eq, hser]
  change linSub _ (_ • _ • MvPowerSeries.map ι (tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (e j La) (e (j + 1) La') Θ))) = _
  rw [htay, map_linSub', ← linSub_smul', ← linSub_smul', GlobalTheory.TwU.LawAll.linSub_linSub', smul_smul]
  congr 1
  funext x y
  exact hsub x y

end GlobalTheory.TwV.DelB
end

