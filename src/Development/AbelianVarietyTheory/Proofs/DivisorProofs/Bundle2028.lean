module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyQuasiFiniteBigCellToBaseProdAffineSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole.CellQF

open GlobalTheory.FlagMod (initSpan initSpan_le_of_tri)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {m : ℕ}

theorem initSpan_eq_of_lower {v v' : Fin m → M} (L : Matrix (Fin m) (Fin m) R)
    (hL : ∀ i j, i < j → L i j = 0) (hd : ∀ i, IsUnit (L i i))
    (h : ∀ i, v' i = ∑ j, L i j • v j) (i : ℕ) : initSpan R v' i = initSpan R v i := by
  have ht : L.IsLowerTriangular := fun a b hab => hL a b hab
  have hdet : IsUnit L.det := by
    rw [Matrix.det_of_lowerTriangular L ht]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun a _ => hd a)
  haveI : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
  have hti : L⁻¹.BlockTriangular OrderDual.toDual := Matrix.blockTriangular_inv_of_blockTriangular ht
  have hinv : ∀ a, v a = ∑ j, L⁻¹ a j • v' j := fun a => by
    simp only [h, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul L hdet, Matrix.one_apply]
    simp
  refine le_antisymm (initSpan_le_of_tri (B := L.transpose) (fun a b hab => hL b a hab) h i)
    (initSpan_le_of_tri (B := (L⁻¹).transpose) (fun a b hab => hti hab) hinv i)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def baseVec (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) {K : Type} [CommRing K] (x : Sp K ⟶ TF.Y.X)
    (hU : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) : TanM x TF.Y.t.G :=
  LieMet.tanOf (v := spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (by
    have := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev x U.1 hU) (hv (e ⟨σ, j⟩))
    unfold LogKS.chart at this
    rwa [GlobalTheory.FlagMod.spMap_ev x U.2 hU] at this)

theorem vecAt_eq_sum (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) {K : Type} [CommRing K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W)
    {x : Sp K ⟶ TF.Y.X} (ex : z ≫ toBase TF Z = x) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i =
      ∑ j, ev z W hz ((L σ * N σ) i j) • baseVec TF U e v hv x hU σ j := by
  subst ex
  have hc := h.2.2.2.2.2.2.2 K z hz hU hk hx σ i
  exact (LieMet.isComb_iff (fun j => baseVec TF U e v hv _ hU σ j)
    (fun j => ev z W hz ((L σ * N σ) i j)) _).1 hc

theorem step_eq_cell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (hv : ∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) {K : Type} [CommRing K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W)
    {x : Sp K ⟶ TF.Y.X} (ex : z ≫ toBase TF Z = x) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = x) (σ : E →+* ℂ) (i : ℕ) :
    TF.X.F.step (z ≫ inc₀ TF.X Z) hx σ i =
      initSpan K (fun a => ∑ j, ev z W hz (N σ a j) • baseVec TF U e v hv x hU σ j) i := by
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 hz
  rw [TF.X.F.step_eq k _ hk hx]
  refine initSpan_eq_of_lower (fun a b => ev z W hz (L σ a b))
    (fun a b hab => by rw [h.2.2.2.1 σ a b hab, map_zero]) (fun a => (h.2.2.2.2.1 σ a).map _) (fun a => ?_) i
  rw [vecAt_eq_sum TF Z U e v hv W k L N h z hz ex hU hk hx σ a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

end GlobalTheory.LogPole.CellQF

namespace GlobalTheory.LogPole.CellQF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem locallyOfFiniteType_cell (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W))
    (h : IsCell TF Z U e v W k L N) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  have hπ : LocallyOfFiniteType (toBase TF Z) := by
    have : IsProper TF.X.π := TF.X.proper
    infer_instance
  have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (toBase TF Z) hπ U ⟨W, h.1⟩ h.2.1
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  refine RingHom.FiniteType.of_comp_finiteType
    (f := (MvPolynomial.C : Γ(TF.Y.X, U.1) →+* MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ?_
  rw [CommRingCat.hom_ofHom, MvPolynomial.eval₂Hom_comp_C]
  exact h1

end GlobalTheory.LogPole.CellQF


set_option maxHeartbeats 1000000 in
open GlobalTheory.LogPole.CellQF in
theorem GlobalTheory.LogPole.locallyQuasiFinite_cellMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)))) := by
  intro E _ _ _ H Dw l Xo c TF Z _ U n e v hv W k L N h
  haveI := locallyOfFiniteType_cell TF Z U e v W k L N h
  refine GlobalTheory.locallyQuasiFinite_of_finite_geometric_points _ fun Ω _ _ y => ?_
  have hfs : IsOpenImmersion h.1.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec h.1
  have hzW : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W), ⊤ ≤ (x ≫ h.1.fromSpec) ⁻¹ᵁ W :=
    fun x => GlobalTheory.FlagMod.le_preimage_comp x (GlobalTheory.FlagMod.tau_le h.1 le_rfl)
  have hsp : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      spMap (ev (x ≫ h.1.fromSpec) W (hzW x)) = x := fun x => by
    rw [← cancel_mono h.1.fromSpec]
    exact GlobalTheory.FlagMod.spMap_ev _ h.1 _
  have hy : ∀ x : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      spMap ((ev (x.1 ≫ h.1.fromSpec) W (hzW x.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y := fun x => by
    rw [← spMap_comp', hsp]
    exact x.2
  have hρ : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      (ev (x.1 ≫ h.1.fromSpec) W (hzW x.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)) =
      (ev (x'.1 ≫ h.1.fromSpec) W (hzW x'.1)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)) := fun x x' =>
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((hy x).trans (hy x').symm))
  have hN : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}, ∀ σ a b,
      ev (x.1 ≫ h.1.fromSpec) W (hzW x.1) (N σ a b) = ev (x'.1 ≫ h.1.fromSpec) W (hzW x'.1) (N σ a b) := by
    intro x x' σ a b
    rcases lt_trichotomy a b with hab | rfl | hab
    · have e1 : N σ a b = MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)
          (MvPolynomial.X ⟨σ, ⟨(a, b), hab⟩⟩) := by
        rw [MvPolynomial.eval₂Hom_X']; rfl
      rw [e1]
      exact congrArg (fun f => f (MvPolynomial.X ⟨σ, ⟨(a, b), hab⟩⟩)) (hρ x x')
    · rw [h.2.2.2.2.2.2.1 σ a, map_one, map_one]
    · rw [h.2.2.2.2.2.1 σ a b hab]
      exact (RingHom.map_zero _).trans (RingHom.map_zero _).symm
  have hUx : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      ⊤ ≤ ((x ≫ h.1.fromSpec) ≫ toBase TF Z) ⁻¹ᵁ U.1 :=
    fun x => GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzW x)
  have hev : ∀ x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W),
      ev ((x ≫ h.1.fromSpec) ≫ toBase TF Z) U.1 (hUx x) = ((ev (x ≫ h.1.fromSpec) W (hzW x)).comp
        (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))).comp MvPolynomial.C :=
    fun x => by
    ext r
    rw [← GlobalTheory.FlagMod.ev_appLE _ _ h.2.1 (hzW x)]
    simp
  have hB : ∀ x x' : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      (x.1 ≫ h.1.fromSpec) ≫ toBase TF Z = (x'.1 ≫ h.1.fromSpec) ≫ toBase TF Z := fun x x' => by
    refine (GlobalTheory.FlagMod.spMap_ev _ U.2 (hUx x.1)).symm.trans (Eq.trans ?_ (GlobalTheory.FlagMod.spMap_ev _ U.2 (hUx x'.1)))
    rw [hev x.1, hev x'.1, hρ x x']
  rcases isEmpty_or_nonempty {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}
    with h0 | hne
  · exact @Finite.of_subsingleton _ ⟨fun a => (h0.false a).elim⟩
  obtain ⟨x₀⟩ := hne
  have ex₀ : (x₀.1 ≫ h.1.fromSpec) ≫ toBase TF Z = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
    (Category.assoc _ _ _).symm
  have hU0 : ⊤ ≤ (((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π) ⁻¹ᵁ U.1 := by
    rw [← ex₀]; exact hUx x₀.1
  have hfin := TF.flag.fin Ω ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z)
  have key : ∀ x : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) // x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y},
      ∃ hx : ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π,
      ∀ (σ : E →+* ℂ) (i : ℕ), TF.X.F.step ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) hx σ i =
        TF.X.F.step ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) rfl σ i := fun x => by
    have ex : (x.1 ≫ h.1.fromSpec) ≫ toBase TF Z = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
      (hB x x₀).trans ex₀
    have hx : ((x.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = ((x₀.1 ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π :=
      (Category.assoc _ _ _).trans ex
    refine ⟨hx, fun σ i => ?_⟩
    refine (step_eq_cell TF Z U e v hv.1 W k L N h _ (hzW x.1) ex hU0 hx σ i).trans ?_
    refine Eq.trans ?_ (step_eq_cell TF Z U e v hv.1 W k L N h _ (hzW x₀.1) ex₀ hU0 rfl σ i).symm
    simp only [hN x x₀]
  have hinj : Function.Injective
      (fun x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) => (x ≫ h.1.fromSpec) ≫ inc₀ TF.X Z) :=
    fun a b hab => (cancel_mono h.1.fromSpec).1 ((cancel_mono (inc₀ TF.X Z)).1 hab)
  have hS : {x : Spec (CommRingCat.of Ω) ⟶ Spec Γ(Y₀ TF.X Z, W) | x ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N))) = y}.Finite :=
    (hfin.preimage hinj.injOn).subset fun x hx => key ⟨x, hx⟩
  exact hS.to_subtype
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusOfIsTwistPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TranslateSection

theorem translT_inv_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A) :
    translT A z⁻¹ ≫ translT A z = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, translPt, Category.assoc, lift_snd, lift_fst, Category.id_comp, comp_lift_assoc, lift_fst_assoc]
    change (fst T A ≫ z) * ((fst T A ≫ z⁻¹) * snd T A) = snd T A
    have e : fst T A ≫ z⁻¹ = (fst T A ≫ z)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one])
    rw [e, mul_inv_cancel_left]

theorem translT_surjective : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (z : T ⟶ A), Function.Surjective (translT A z).left.base := by
  intro S A _ T z y
  refine ⟨(translT A z⁻¹).left.base y, ?_⟩
  have h := congrArg (fun f : T ⊗ A ⟶ T ⊗ A => f.left y) (translT_inv_comp A z)
  simpa [Scheme.Hom.comp_apply] using h

theorem mulT_eq {S : Scheme.{0}} (A : Over S) [GrpObj A] (m : ℕ) :
    mulT A (baseOver S) m = (λ_ A).hom ≫ mulA A m ≫ (λ_ A).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, CartesianMonoidalCategory.leftUnitor_hom, mulT]
  refine (lift_snd _ _).trans ?_
  rw [mulA, MonObj.comp_pow, Category.comp_id]
  rfl

theorem mulT_surjective : ∀ {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (m : ℕ), 1 ≤ m → Function.Surjective (mulT P.A (baseOver S) m).left.base := by
  intro S _ P m hm y
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨-, -, hs, -⟩ := hLaw.mulN S P m hm
  obtain ⟨b, hb⟩ := hs.surj ((λ_ P.A).hom.left y)
  refine ⟨(λ_ P.A).inv.left b, ?_⟩
  have h1 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left ((λ_ P.A).inv.left b)) (mulT_eq P.A m)
  have h2 := congrArg (fun f : baseOver S ⊗ P.A ⟶ baseOver S ⊗ P.A => f.left y) (λ_ P.A).hom_inv_id
  have h3 := congrArg (fun f : P.A ⟶ P.A => f.left b) (λ_ P.A).inv_hom_id
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.id_left] at h1 h2 h3
  have h2' : (λ_ P.A).inv.left ((λ_ P.A).hom.left y) = y := h2
  have h3' : (λ_ P.A).hom.left ((λ_ P.A).inv.left b) = b := h3
  rw [h1, h3', hb, h2']

theorem mem_nonzeroLocus_of_isTwistPull : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection

end GlobalTheory.MBLow.TranslateSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CodimOne

theorem mem_preimage_sup_of_ringKrullDim_stalk_le_one :
    ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  intro X S _ f _ _ V U hV hU z hz
  by_contra hzm
  have hzU : f z ∉ U := fun h => hzm (Or.inl h)
  have hzV : z ∉ V := fun h => hzm (Or.inr h)
  set s := f z with hs

  let ξ : X := f.fiberι s (genericPoint (f.fiber s))
  have hfξ : f ξ = s := (f.range_fiberι s).le ⟨_, rfl⟩
  have hrange : ∀ y : X, f y = s → ξ ⤳ y := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ Set.range (f.fiberι s) := (f.range_fiberι s).ge hy
    exact (genericPoint_specializes w).map (f.fiberι s).continuous
  obtain ⟨x, hxV, hxs⟩ := hV s
  have hξV : ξ ∈ V := (hrange x hxs).mem_open V.isOpen hxV
  have hξz : ξ ⤳ z := hrange z rfl
  have hξnez : ξ ≠ z := fun h => hzV (h ▸ hξV)

  obtain ⟨u, huU⟩ := hU
  have hηU : genericPoint S ∈ U := (genericPoint_specializes u).mem_open U.isOpen huU
  have hηs : genericPoint S ⤳ f ξ := hfξ ▸ genericPoint_specializes s
  obtain ⟨ζ, hζξ, hfζ⟩ := (Flat.generalizingMap f) hηs
  have hζneξ : ζ ≠ ξ := by
    intro h
    apply hzU
    rw [← hfξ, ← h, hfζ]
    exact hηU
  have h1 : z < ξ := lt_of_le_not_ge hξz (fun h => hξnez (hξz.antisymm h).eq)
  have h2 : ξ < ζ := lt_of_le_not_ge hζξ (fun h => hζneξ (hζξ.antisymm h).eq)
  have hc : (2 : ℕ∞) ≤ Order.coheight z := by
    have a := Order.coheight_add_one_le h1
    have b := Order.coheight_add_one_le h2
    have : (1 : ℕ∞) + 1 ≤ Order.coheight ζ + 1 + 1 := by gcongr; exact le_add_self
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight ζ + 1 + 1 := this
      _ ≤ Order.coheight ξ + 1 := by gcongr
      _ ≤ Order.coheight z := a
  rw [ringKrullDim_stalk_eq_coheight] at hz
  have : Order.coheight z ≤ 1 := by exact_mod_cast hz
  exact absurd (hc.trans this) (by norm_num)

end GlobalTheory.CodimOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissible
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTrUnit

theorem exists_const : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE _hbij μ hμ
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl (F := F), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hfin : ∀ v : Pl (F := F), ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
    intro v
    have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ := GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA
  have hinf : ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F (Fin n × Fin d),
        @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
          (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
    letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact _root_.GlobalTheory.ArchInvForm.const_of_intertwines hP F (Fin n × Fin d) ψ hψ ei A hA
  exact GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure hinf hfin μ hμ

end GlobalTheory.ModelTrUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport
section
namespace MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.MaTransport

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def carryPartition (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A) :
    ChartPartition (tAtlas A h) where
  χ j := P.χ j ∘ h.symm
  smooth j k := by
    have e₁ : (P.χ j ∘ h.symm) ∘ ((tAtlas A h).chart k).symm = P.χ j ∘ (A.chart k).symm :=
      funext fun y => by simp [tAtlas_symm]
    rw [e₁]
    exact P.smooth j k
  nonneg j x := P.nonneg j _
  tsupport_subset j := fun x hx =>
    P.tsupport_subset j (tsupport_comp_subset_preimage (P.χ j) h.symm.continuous hx)
  sum_eq_one x := P.sum_eq_one (h.symm x)

theorem isPotential_pullback (A : FinHolAtlas e X) (h : X ≃ₜ X') {Q : LocPot X'}
    (hQ : IsPotential (tAtlas A h) Q) : IsPotential A (Q.pullback h h.continuous) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · exact hQ.1 (h x) j
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hQ.2 (h x) (h x') (h y) hy
    refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, fun j => ?_, fun z hz => ?_⟩
    · exact hG j
    · exact hd (h z) hz

theorem integralWith_carry (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : ChartPartition A)
    (Φ : Fin e → LocPot X') (g : X' → ℝ) :
    integralWith (tAtlas A h) (carryPartition A h P) Φ g =
      integralWith A P (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change P.χ j (h.symm (h ((A.chart j).symm y))) * g (h ((A.chart j).symm y)) * _ =
    P.χ j ((A.chart j).symm y) * g (h ((A.chart j).symm y)) * _
  rw [h.symm_apply_apply]
  rfl

theorem mInt_tAtlas (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X]
    [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X')
    (Φ : Fin e → LocPot X') (g : X' → ℝ) (hΦ : ∀ i, IsPotential (tAtlas A h) (Φ i))
    (hg : Continuous g) :
    mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  obtain ⟨P⟩ := existsPartition A
  have hΨ : ∀ i, IsPotential A ((Φ i).pullback h h.continuous) :=
    fun i => isPotential_pullback A h (hΦ i)
  rw [mIntEq (tAtlas A h) (carryPartition A h P) Φ hΦ g (mIntegrableCont _ Φ hΦ g hg),
    mIntEq A P _ hΨ (g ∘ h) (mIntegrableCont A _ hΨ _ (hg.comp h.continuous)),
    integralWith_carry]

end GlobalTheory.CompanionTheory.MaTransport

end
end

end MongeAmpereTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] [CompactSpace X] [T2Space X] [CompactSpace X'] [T2Space X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (Φ : Fin e → LocPot X') (g : X' → ℝ), (∀ i, IsPotential (tAtlas A h) (Φ i)) → Continuous g → mInt (tAtlas A h) Φ g = mInt A (fun i => (Φ i).pullback h h.continuous) (g ∘ h) := by
  first | exact @MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | exact MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas | (intros; apply MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverTensorIsPullbackOfIsPullbackSquaresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares : ∀ {S S' : Scheme.{0}} (s : S' ⟶ S) (A B : Over S') (Y Z : Over S) (j : A.left ⟶ Y.left) (j' : B.left ⟶ Z.left), IsPullback j A.hom Y.hom s → IsPullback j' B.hom Z.hom s → ∃ k : (A ⊗ B).left ⟶ (Y ⊗ Z).left, k ≫ (fst Y Z).left = (fst A B).left ≫ j ∧ k ≫ (snd Y Z).left = (snd A B).left ≫ j' ∧ IsPullback k (A ⊗ B).hom (Y ⊗ Z).hom s := by
  first | exact @GlobalTheory.over_tensor_isPullback_of_isPullback | exact GlobalTheory.over_tensor_isPullback_of_isPullback | (intros; apply GlobalTheory.over_tensor_isPullback_of_isPullback <;> assumption)
end

