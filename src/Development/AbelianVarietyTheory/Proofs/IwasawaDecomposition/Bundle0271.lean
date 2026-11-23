module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProjFin

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem finrank_app_eq_residueDegree {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z']
    (f : Z' ⟶ Z) [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) {U : Z.Opens}
    (hU : IsAffineOpen U) (hxU : f (genericPoint Z') ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) = f.residueDegree (genericPoint Z') := by
  letI := (f.app U).hom.toAlgebra
  letI := (Z.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    (Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (f.app U ≫ Z'.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := isFractionRing_evaluation Z hU h hxU
  haveI := isFractionRing_evaluation Z' (hU.preimage f) rfl hxU
  exact (IsFractionRing.finrank_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
    Γ(Z', f ⁻¹ᵁ U) (Z'.residueField (genericPoint Z'))).symm

theorem genRank_eq_finrank_sections {X : Scheme.{0}} [IsIntegral X] (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    VB.genRank F = Module.finrank Γ(X, U) Γ(F, U) := by
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have key (y : U) : Module.finrank (X.presheaf.stalk (y : X)) (F.presheaf.stalk (y : X) :) =
      Module.finrank Γ(X, U) Γ(F, U) := by
    have := hU.isLocalization_stalk y
    have := QCoh.isLocalizedModule_germLinear F hU y
    have hp := (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors
    rw [IsLocalization.finrank_eq _ _ hp, IsLocalizedModule.finrank_eq _ (QCoh.germLinear F y) hp]
  exact key ⟨_, hx⟩

theorem isFiniteQC_pushforward_structureModule {Z Z' : Scheme.{0}} (f : Z' ⟶ Z) [IsFinite f] :
    QCoh.IsFiniteQC ((Scheme.Modules.pushforward f).obj (structureModule Z')) :=
  ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward f _ hV
    (hF := QCoh.finite_sections (structureModule Z') (hV.preimage f))⟩

theorem genRank_pushforward {Z Z' : Scheme.{0}} [IsIntegral Z] [IsIntegral Z'] (f : Z' ⟶ Z)
    [IsFinite f] (h : f (genericPoint Z') = genericPoint Z) :
    VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      f.residueDegree (genericPoint Z') := by
  obtain ⟨U, hU, hxU⟩ := QCoh.exists_affine_mem (genericPoint Z)
  have hx' : f (genericPoint Z') ∈ U := h ▸ hxU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have h1 : VB.genRank ((Scheme.Modules.pushforward f).obj (structureModule Z')) =
      Module.finrank Γ(Z, U) Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) :=
    genRank_eq_finrank_sections _ hU hxU
  letI := (f.app U).hom.toAlgebra
  let e : Γ((Scheme.Modules.pushforward f).obj (structureModule Z'), U) ≃ₗ[Γ(Z, U)]
      Γ(Z', f ⁻¹ᵁ U) :=
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [h1, e.finrank_eq, finrank_app_eq_residueDegree f h hU hx']

theorem interNumOn_eq_residueDegree_mul : ∀ (κ : Type) [Field κ] (Z Z' : Scheme.{0}) [IsIntegral Z]
    [IsIntegral Z'] [Algebra κ Γ(Z, ⊤)] (f : Z' ⟶ Z) [IsFinite f], IsProjOver (strHom κ (X := Z)) →
    topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → ∀ N : LB Z, N.IsLB →
    interNumOn κ f ![N] = (f.residueDegree (genericPoint Z') : ℤ) *
      interNum κ (structureModule Z) ![N] := by
  intro κ _ Z Z' _ _ _ f _ hP hd hg N hN
  haveI := isFiniteQC_pushforward_structureModule f
  rw [interNumOn_def, GlobalTheory.T.intersectionNumber_eq_genericRank_mul_projCurve κ Z hP hd _ N hN, genRank_pushforward f hg]

end GlobalTheory.ProjFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMSmulMeasureSelf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetSharp

open Formalism.IndefR.Mult

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_ne_zero_of_ne {M : DSModel V S} {u : MMap M} (hu : u ≠ 0) : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := by
  intro τ
  by_contra h
  push_neg at h
  exact hu (MultilinearMap.ext fun v => (u.map_coord_zero τ (h (v τ))).trans rfl)

theorem ipM_smul_measure_self (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {u : MMap M} {a : ℝ} (ha : 0 ≤ a)
    (hu : u ≠ 0) (h : ∃ c, IsMultIP M μ 𝓕 u u c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 u u = (a : ℂ) * ipM M μ 𝓕 u u := by
  choose w hw using sm_ne_zero_of_ne hu
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 u u ((a : ℂ) * ipM M μ 𝓕 u u) := by
    intro v v'
    obtain ⟨h1, h2⟩ := ipM_spec M μ 𝓕 u u h v v'
    refine ⟨?_, ?_⟩
    · unfold IntegrableOn at h1 ⊢
      rw [Measure.restrict_smul]
      exact h1.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  exact hasPeterssonInner_unique M _ 𝓕 u u w hv0 (ipM_spec M _ 𝓕 u u ⟨_, h1⟩) h1

end Schur

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem norm_sq_rows (hP : Pins R F cG) (Z : ReadL R F X0 Y) (y : Fin ((s1Of R F).D) → D.what₂.LL) :
    ‖D.jEE (Z.eRR y)‖ ^ 2 =
      (RealDat.nP F.lv2 true)⁻¹ * ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ ^ 2 := by
  set z : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
    ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)) with hz
  have hzn : ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ = ‖z‖ := rfl
  rw [hzn]
  obtain ⟨hinj, -, hip⟩ := hP.char.base.models.HE
  set w := D.jEE (Z.eRR y) with hw
  have hT := Y.tied.sharp.ee w w
  have hJ := Z.jEE y
  have hE : ⟪w, w⟫_ℂ = ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0 (R.HE.e z) (R.HE.e z) := by
    rw [hT]
    show ipMT _ _ _ _ _ = _
    rw [ipMT, hJ]
    show ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0
      (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hip' : ⟪z, z⟫_ℂ = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) := hip z z
  have ha : (0 : ℝ) ≤ (RealDat.nP F.lv2 true)⁻¹ := (inv_pos.2 (RealDat.nP_pos (F := F.lv2) true)).le
  by_cases hz0 : z = 0
  · have hu : R.HE.e z = 0 := by rw [hz0, map_zero]
    have hw0 : w = 0 := by
      apply Y.Ish.jE.injective
      rw [map_zero]
      apply Subtype.ext
      rw [hJ]
      show PiTensorProduct.lift (R.HE.e z) = 0
      rw [hu, map_zero]
    rw [hw0, hz0, norm_zero, norm_zero]
    ring
  · have hu : R.HE.e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
    have hex : ∃ c, IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) c := by
      by_contra hno
      have h0 : ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) = 0 := by
        unfold ipM
        rw [dite_eq_right hno]
      exact hz0 (inner_self_eq_zero.1 (hip'.trans h0))
    rw [ipM_smul_measure_self (R.MY 0) R.ν0 R.fd0 ha hu hex, ← hip'] at hE
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ _ _ _ _ z, hE]
    exact Complex.re_ofReal_mul _ _

theorem majAt_rows_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR x) (Z.eRR y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hR := (complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim).rowHyp true
  have hn := hR.h4pos.2.2 true
  have hv0 := (pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP).2.2.2.2
  refine fun x y => GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ _ Z.eRR.toLinearMap (fun y => ?_) x y
  have hL : Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) = ‖D.jEE (Z.eRR y)‖ := by
    rw [hv0]; exact D.jEE_norm _
  have hr : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y y =
      (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) *
        ⟪(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y), (R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)⟫_ℂ :=
    PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr true hR.h2 hn y y
  show Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) ^ 2 =
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y ^ 2
  rw [hL, norm_sq_rows hP Z y]
  refine Eq.trans ?_ (Formalism.BasicNotions.normAt_sq_eq_majAt _ _ _ _).symm
  rw [hr, inner_self_eq_norm_sq_to_K, Complex.re_ofReal_mul]
  norm_cast

end GlobalTheory.Mem.R3.MetSharp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralHalf
section
noncomputable section

namespace GlobalTheory.Mem.Col2.HostK

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.UnusedSlot33.HK
open scoped BigOperators

variable {R : Ranks} (H : Host R)

theorem emb_conj (f : H.E →+* ℂ) (y : H.E) : f (H.conj y) = starRingEnd ℂ (f y) := Formalism.HC.HostAx.conjE_apply _ _ _

theorem sqrt_mem : H.sqrtMinusD ∈ H.K := bE_mem H

theorem φ₀_sqrt : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem exists_coords {x : H.E} (hx : x ∈ H.K) : ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD :=
  by apply _root_.GlobalTheory.CoordsOfMemAdjoin.exists_rat_coords <;> assumption

theorem conj_coords (a b : ℚ) :
    H.conj ((a : H.E) + (b : H.E) * H.sqrtMinusD) = (a : H.E) - (b : H.E) * H.sqrtMinusD := by
  rw [map_add (f := _), map_mul, map_ratCast, map_ratCast, H.conj_sqrtMinusD]
  ring

theorem conj_mem {x : H.E} (hx : x ∈ H.K) : H.conj x ∈ H.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords H hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a) (mul_mem (SubfieldClass.ratCast_mem _ b) (sqrt_mem H))

def conjK : H.K →+* H.K :=
  RingHom.codRestrict ((H.conj : H.E →+* H.E).comp H.K.val.toRingHom) H.K (fun x => conj_mem H x.2)

theorem coe_conjK (x : H.K) : ((conjK H x : H.K) : H.E) = H.conj (x : H.E) := rfl

theorem conjK_conjK (x : H.K) : conjK H (conjK H x) = x := Subtype.ext (conj_conj H x)

theorem exists_norm_int (x : 𝓞 H.K) : ∃ m : ℤ, (x : H.K) * conjK H x = m :=
  ⟨Algebra.intNorm ℤ (𝓞 H.K) x, Subtype.ext (by
    have := norm_int H x
    simpa [coe_conjK] using this.symm)⟩

theorem isGalois_over : IsGalois H.K H.E := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : H.E) : ((Algebra.trace H.K H.E y : H.K) : H.E) = ∑ τ : H.E ≃ₐ[H.K] H.E, τ y := by
  have := isGalois_over H
  exact trace_eq_sum_automorphisms (K := H.K) y

theorem conj_comm (τ : H.E ≃ₐ[H.K] H.E) (y : H.E) : H.conj (τ y) = τ (H.conj y) :=
  H.φ₀.injective (by
    rw [emb_conj H H.φ₀ (τ y)]
    exact (emb_conj H (H.φ₀.comp (τ : H.E →+* H.E)) y).symm)

theorem trace_conj (y : H.E) : Algebra.trace H.K H.E (H.conj y) = conjK H (Algebra.trace H.K H.E y) := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm H τ y).symm

theorem trace_pos (y : H.E) (hy : y ≠ 0) : ∃ a : ℚ, 0 < a ∧ Algebra.trace H.K H.E (y * H.conj y) = (a : H.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords H (Algebra.trace H.K H.E (y * H.conj y)).2
  have hfix : H.conj ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E)
      = ((Algebra.trace H.K H.E (y * H.conj y) : H.K) : H.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : H.E) * H.sqrtMinusD = 0 := by linear_combination (-1 / 2 : H.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg H.φ₀ hab
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : H.E ≃ₐ[H.K] H.E, H.φ₀ (τ (y * H.conj y)) = ((Complex.normSq (H.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : H.E ≃ₐ[H.K] H.E, Complex.normSq (H.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem card_tau : Fintype.card (Tau R) = Module.finrank H.K H.E := by
  have := isGalois_over H
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective (GlobalTheory.InducedType.galK_bijective H)

theorem embT_K (τ : Tau R) (a : H.K) : embT H τ (a : H.E) = H.φ₀ (a : H.E) := by
  change H.φ₀ (H.sigmaOf _ _) = _
  rw [sigmaOf_fix_K H _ τ.2 _ a.2]

theorem sum_embT (y : H.E) : ∑ τ, embT H τ y = H.φ₀ ((Algebra.trace H.K H.E y : H.K) : H.E) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_trace, map_sum]
  exact Fintype.sum_bijective (GlobalTheory.InducedType.galK H) (GlobalTheory.InducedType.galK_bijective H) _ _ (fun τ => rfl)

theorem isIntegral_half : IsIntegral ℤ ((1 + (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K)) / 2) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := by
    have := H.hyp.2.2.2.1
    exact ⟨(H.d + 1) / 4, by omega⟩
  have hs : (⟨H.sqrtMinusD, sqrt_mem H⟩ : H.K) ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa using H.sqrtMinusD_sq)
  have hm' : (H.d : H.K) + 1 = 4 * m := by exact_mod_cast hm
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp only [eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : H.K) * hs - (1 / 4 : H.K) * hm'

end GlobalTheory.Mem.Col2.HostK

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeG
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign.DomCurv

section Sqrt

open scoped MatrixOrder

theorem exists_eq_conjTranspose_mul_self {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin k) (Fin k) ℂ, T = Bᴴ * B := by
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

end Sqrt

variable {m r : ℕ}

def domForm (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - Matrix.of x * (Matrix.of x)ᴴ

theorem domGram_eq (x : Fin m → Fin r → ℂ) : domGram m r x = ((domForm m r x)⁻¹)ᵀ := rfl

theorem mContDiffAt_of (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) y := fun a b => by
  show ContDiffAt ℝ k (fun x : Fin m → Fin r → ℂ => x a b) y
  exact ((contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin r → ℂ)) a)).contDiffAt

theorem mdel_of (y ξ : Fin m → Fin r → ℂ) :
    mdel (fun y : Fin m → Fin r → ℂ => Matrix.of y) y ξ = Matrix.of ξ := by
  ext a b
  show del (fun x : Fin m → Fin r → ℂ => x a b) y ξ = ξ a b
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, del_eq_fderiv (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_of (y η : Fin m → Fin r → ℂ) :
    mdbar (fun y : Fin m → Fin r → ℂ => Matrix.of y) y η = 0 := by
  ext a b
  show dbar (fun x : Fin m → Fin r → ℂ => x a b) y η = 0
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem mContDiffAt_domForm (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (domForm m r) y :=
  (mContDiffAt_const 1).sub ((mContDiffAt_of k y).mul (mContDiffAt_of k y).conjTranspose)

theorem domForm_eq_fun : domForm m r = fun y => 1 + -(Matrix.of y * (Matrix.of y)ᴴ) := by
  funext y; simp [domForm, sub_eq_add_neg]

theorem mdel_domForm (y ξ : Fin m → Fin r → ℂ) :
    mdel (domForm m r) y ξ = -(Matrix.of ξ * (Matrix.of y)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdel_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdel_const,
    mdel_neg, mdel_mul h1 h1.conjTranspose, mdel_conjTranspose, mdbar_of, mdel_of]
  simp

theorem mdbar_domForm (y η : Fin m → Fin r → ℂ) :
    mdbar (domForm m r) y η = -(Matrix.of y * (Matrix.of η)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdbar_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdbar_const,
    mdbar_neg, mdbar_mul h1 h1.conjTranspose, mdbar_conjTranspose, mdbar_of, mdel_of]
  simp

theorem conn_domGram {y : Fin m → Fin r → ℂ} (hu : IsUnit (domForm m r y).det)
    (ξ : Fin m → Fin r → ℂ) :
    conn (domGram m r) y ξ = Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) := by
  have e : (fun x => (domGram m r x)ᵀ) = fun x => (domForm m r x)⁻¹ := by
    funext x; rw [domGram_eq, transpose_transpose]
  have e2 : (domGram m r y)ᵀ = (domForm m r y)⁻¹ := congrFun e y
  rw [conn, e2, ← mdel_transpose, e, mdel_inv (mContDiffAt_domForm 1 y) hu, mdel_domForm,
    nonsing_inv_nonsing_inv _ hu]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]

theorem curv_domGram_eq {x : Fin m → Fin r → ℂ} (hx : IsUnit (domForm m r x).det)
    (ξ η : Fin m → Fin r → ℂ) :
    curv (domGram m r) x ξ η = -(Matrix.of ξ * ((1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ *
      Matrix.of x) * ((Matrix.of η)ᴴ * (domForm m r x)⁻¹))) := by
  have hev := (mContDiffAt_domForm (m := m) (r := r) 1 x).eventually_isUnit hx
  have he : (fun y => conn (domGram m r) y ξ) =ᶠ[𝓝 x]
      fun y => Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) :=
    hev.mono fun y hy => conn_domGram hy ξ
  have hZ := mContDiffAt_of (m := m) (r := r) 1 x
  have hM := (mContDiffAt_domForm (m := m) (r := r) 1 x).inv hx
  rw [curv, mdbar_congr he, mdbar_mul (mContDiffAt_const (Matrix.of ξ)) (hZ.conjTranspose.mul hM),
    mdbar_const, mdbar_mul hZ.conjTranspose hM, mdbar_inv (mContDiffAt_domForm 1 x) hx,
    mdbar_domForm, mdbar_conjTranspose, mdel_of]
  simp only [Matrix.zero_mul, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_add]
  rw [add_comm]

end GlobalTheory.PointFormSign.DomCurv

namespace GlobalTheory.PointFormSign


open DomCurv in
theorem curv_domGram_isNegSq (m r : ℕ) (x : Fin m → Fin r → ℂ)
    (hx : (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef) : IsNegSq (curv (domGram m r) x) r := by
  have hxA : (domForm m r x).PosDef := hx
  have hu : IsUnit (domForm m r x).det := (isUnit_iff_isUnit_det _).1 hxA.isUnit
  have hM := hxA.inv
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self hM.posSemidef
  have hQ : (1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ * Matrix.of x).PosSemidef :=
    (PosDef.one.add_posSemidef (hM.posSemidef.conjTranspose_mul_mul_same (Matrix.of x))).posSemidef
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hQ
  have hBu : IsUnit B.det := by
    have h1 : IsUnit (Bᴴ * B).det := by rw [← hB]; exact (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  let T : (Fin m → Fin r → ℂ) →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ :=
    { toFun := fun ξ => B * Matrix.of ξ * Cᴴ
      map_add' := fun ξ ξ' => by
        show B * Matrix.of (ξ + ξ') * Cᴴ = B * Matrix.of ξ * Cᴴ + B * Matrix.of ξ' * Cᴴ
        rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c ξ => by
        show B * (c • Matrix.of ξ) * Cᴴ = c • (B * Matrix.of ξ * Cᴴ)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨B, T, hBu, fun ξ η => ?_⟩
  rw [curv_domGram_eq hu, hC, hB]
  show -(Matrix.of ξ * ((Cᴴ * C) * ((Matrix.of η)ᴴ * (Bᴴ * B)))) =
    B⁻¹ * (-((B * Matrix.of ξ * Cᴴ) * (B * Matrix.of η * Cᴴ)ᴴ)) * B
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hBu]

end GlobalTheory.PointFormSign
end
end

