module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.ThetaBaseMove

open Formalism.IndefR.Fin.LevelGroupLemmas

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem heisO_smul' (u : WO S T) (c : ℂ) (g : WO S T → ℂ) : heisO ψ S T u (c • g) = c • heisO ψ S T u g := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_smul (c : ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (c • g) := by
  refine ⟨fun γ w => ?_, ?_, hg.cont.const_smul c, fun k L hL h0 w => (hg.smooth k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg.quasi]; ring
  · obtain ⟨U, hU, h⟩ := hg.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', h u hu h0]⟩

theorem isPlaceModel_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (g : GA D S) (h : GA D T) (c : ℂ)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) f₀) (c • (om (g, h)).comp Tm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply,
      hW.om_heis g h x (Tm Φ) (hth Φ hΦ), hfx x (Or.inl hx), heisO_smul']
  · intro Φ hΦ y hy
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply,
      hW.om_heis g h y (Tm Φ) (hth Φ hΦ), hfx y (Or.inr hy), heisO_smul']
  · rw [LinearMap.smul_apply, LinearMap.comp_apply, hTm.vac]

theorem isThetaAt_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hth : ∀ f₀, IsThetaFunO ψ S T f₀ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm →
      ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    {b Φ f : WO S T → ℂ} (hb : IsThetaFunO ψ S T b) (g : GA D S) (h : GA D T) {c : ℂ} (hc : c ≠ 0)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 b Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) b) Φ (c • om (g, h) f) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  refine ⟨⟨_, isPlaceModel_move hW hTm (hth b hb Tm hTm) g h c hfx⟩, fun T' hT' => ?_⟩
  have hfx' : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g⁻¹ h⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hfx x hx]
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have k1 : ∀ v, om (g⁻¹, h⁻¹) (om (g, h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k2 : ∀ v, om (g, h) (om (g⁻¹, h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hm := isPlaceModel_move hW hT' (hth _ (theta_smul c (hW.om_pres _ _ hb)) T' hT') g⁻¹ h⁻¹ c⁻¹ hfx'
  rw [map_smul, k1, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  have e1 : f = _ := hall _ hm
  rw [e1, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, k2, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem actO_fix_of_orth {a e : AE D} {z : GA D S} (hz : SuppAt a S z) (h0 : e * (a + cA D a) = 0) {x : WO S T}
    (hx : IsHalf e x) : actO S T z⁻¹ 1 x = x := by
  rw [actO_eq, inv_inv, mt_one', Matrix.one_mul]
  have : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z - 1) = 0 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hx k j, ← hz j l]
    linear_combination (x k j * (mt S z - 1) j l) * h0
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this

end General

theorem thAt_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t _hV Sa St hSa hSt hd eg ea et fg b Φ f z c hg ha ht hfg hb hz hc hf
  obtain ⟨⟨hψ, hvac⟩, e, he, -⟩ := hC.thP.vP i t
  have hW := (GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t).weil
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hsp : SplitSet (R.Q t) := SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)
  have hth : ∀ {a : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum a P → ∀ f₀, IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀ → ∀ Tm,
      IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D a)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀ Tm →
      ∀ Ψ, IsSBHalf (cA D a) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ →
        IsThetaFunO R.ψ (Vc D i) (Wc D i) (Tm Ψ) := by
    intro a P h f₀ hf₀ Tm hTm Ψ hΨ
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSV
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSW
    exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self h])
      (by rw [← map_mul, h.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart h)) hf₀ Tm hTm Ψ hΨ
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBa := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Sa (fun y => omegaQ Sa (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  have hfgθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) fg := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
    rw [hall Tm hTm]
    exact hth hg _ hvac.theta Tm hTm _ hSBg
  have hbθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) b := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hb
    rw [hall Tm hTm]
    exact hth ha _ hfgθ Tm hTm _ hSBa
  have o1 : et * ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
      hsp.mul_eq_zero (hSt hp) (hSa hq) fun e => Finset.disjoint_left.1 hd hq (e ▸ hp)
  have o2 : et * cA D ea = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← idem_eq ht, ← idem_eq ha, idem, idem, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hsp.mul_conj (hSt hp) (hSa hq)
  have o3 : et * (ea + cA D ea) = 0 := by rw [mul_add, o1, o2, add_zero]
  have o4 : cA D et * (ea + cA D ea) = 0 := by
    have := congrArg (cA D) o3
    rwa [map_mul, map_add, GlobalTheory.LatVac.cA_cA, map_zero, add_comm] at this
  refine isThetaAt_move hW (hth ht) hbθ z⁻¹ 1 hc (fun x hx => ?_) hf
  rcases hx with hx | hx
  · exact actO_fix_of_orth hz o4 hx
  · rw [GlobalTheory.LatVac.cA_cA] at hx
    exact actO_fix_of_orth hz o3 hx

end GlobalTheory.ThetaBaseMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BasisChange

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def cb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) : epsR R ⟶ G :=
  ∏ i, GrpTangent.epsScale (c i) ≫ v i

theorem comb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = cb c v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext (hu i)
  · rintro rfl
    exact ⟨fun i => GrpTangent.epsScale (c i) ≫ v i, fun i => rfl, by rw [List.prod_ofFn]; rfl⟩

theorem comp_prod' {T T' : Over (Sp R)} (s : T' ⟶ T) {J : Type} (S : Finset J) (u : J → (T ⟶ G)) :
    s ≫ ∏ i ∈ S, u i = ∏ i ∈ S, s ≫ u i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem cb_tan {n : ℕ} (c : Fin n → R) {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    IsTangent (cb c v) := by
  rw [GrpTangent.isTangent_iff, cb, comp_prod']
  exact Finset.prod_eq_one fun i _ => (GrpTangent.isTangent_iff _).1 (GrpTangent.isTangent_epsScale _ (hv i))

theorem scale_sum {w : epsR R ⟶ G} (hw : IsTangent w) {J : Type} (S : Finset J) (a : J → R) :
    GrpTangent.epsScale (∑ i ∈ S, a i) ≫ w = ∏ i ∈ S, GrpTangent.epsScale (a i) ≫ w := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using GrpTangent.epsScale_zero_comp hw
  | insert j S hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, GrpTangent.epsScale_add_comp _ _ hw, ih]

theorem cb_cb {m n : ℕ} (a : Fin m → R) (M : Matrix (Fin m) (Fin n) R) {v : Fin n → (epsR R ⟶ G)}
    (hv : ∀ i, IsTangent (v i)) : cb a (fun i => cb (M i) v) = cb (Matrix.vecMul a M) v := by
  simp only [cb, comp_prod', GrpTangent.epsScale_mul_assoc]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← scale_sum (hv j)]
  rfl

theorem cb_single {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin n) :
    cb (Pi.single j 1) v = v j := by
  rw [cb, Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, GrpTangent.epsScale_one, Category.id_comp]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, GrpTangent.epsScale_zero_comp (hv i)]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem exists_unit {n : ℕ} {y y' : Fin n → (epsR R ⟶ G)} (hy : IsLieBasis y) (hy' : IsLieBasis y') :
    ∃ M : Matrix (Fin n) (Fin n) R, IsUnit M ∧ ∀ i, IsLieComb (M i) y (y' i) := by
  choose M hM using fun i => (hy.2 _ (hy'.1 i)).exists
  choose N hN using fun i => (hy'.2 _ (hy.1 i)).exists
  refine ⟨Matrix.of M, ?_, hM⟩
  have e : y' = fun i => cb (Matrix.of M i) y := funext fun i => (comb_iff _ _ _).1 (hM i)
  have h : Matrix.of N * Matrix.of M = 1 := by
    ext i j
    have k : y i = cb (Matrix.vecMul (N i) (Matrix.of M)) y := by
      rw [← cb_cb _ _ hy.1, ← e]
      exact (comb_iff _ _ _).1 (hN i)
    have := (hy.2 _ (hy.1 i)).unique ((comb_iff _ _ _).2 k) ((comb_iff _ _ _).2 (cb_single hy.1 i).symm)
    have := congrFun this j
    rw [Matrix.one_apply, Matrix.mul_apply]
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply, eq_comm] using this
  exact IsUnit.of_mul_eq_one_right _ h

theorem basis_of_unit {n : ℕ} {v v' : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) {M : Matrix (Fin n) (Fin n) R}
    (hM : IsUnit M) (h : ∀ i, IsLieComb (M i) v (v' i)) : IsLieBasis v' := by
  have e : v' = fun i => cb (M i) v := funext fun i => (comb_iff _ _ _).1 (h i)
  subst e
  refine ⟨fun i => cb_tan _ hv.1, fun w hw => ?_⟩
  obtain ⟨c, hc, hu⟩ := hv.2 w hw
  obtain ⟨U, rfl⟩ := hM
  set M : Matrix (Fin n) (Fin n) R := U.val with hMU
  have hN : M * U.inv = 1 := U.val_inv
  have hN' : U.inv * M = 1 := U.inv_val
  have key : ∀ b, IsLieComb b (fun i => cb (M i) v) w ↔ Matrix.vecMul b M = c := fun b => by
    rw [comb_iff, cb_cb _ _ hv.1, ← comb_iff]
    exact ⟨fun q => hu _ q, fun q => by rw [q]; exact hc⟩
  refine ⟨Matrix.vecMul c U.inv, (key _).2 ?_, fun b hb => ?_⟩
  · rw [Matrix.vecMul_vecMul, hN', Matrix.vecMul_one]
  · rw [← (key b).1 hb, Matrix.vecMul_vecMul, hN, Matrix.vecMul_one]

end GlobalTheory.MBLow.BasisChange

theorem GlobalTheory.MBLow.key_basis_change : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  intro κ hκ R K _ _ _ f x G _ _ φ hφ y y' v' hy hy' hv hv'
  obtain ⟨M, hM, hMy⟩ := GlobalTheory.MBLow.BasisChange.exists_unit hy hy'
  have hc : ∀ i, IsLieComb ((M.map f) i) x.v (v' i) := fun i =>
    Chart.comb_baseChange f hφ (hMy i) hv (hv' i)
  let _ := x.P.isAb.comm
  have hb : IsLieBasis v' := GlobalTheory.MBLow.BasisChange.basis_of_unit x.basis (hM.map f.mapMatrix) hc
  have hd : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  refine ⟨hb, hd.unit ^ 4, ?_⟩
  have := hκ K x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis x.th x.th_ne v' hb 1 (M.map f)
    (fun i => by rw [show Geo.Tor.constFn x.P.A.hom _ (1 : K) = 1 by simp [Geo.Tor.constFn], _root_.one_mul]) hc
  have e : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  rw [e] at this
  simpa using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ScaleJet

variable {R : Type} [CommRing R]

theorem res_cst {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem appLE_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V h).hom (constFn q U a) = constFn q' V a := by
  subst hf
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U V (fun _ _ => trivial) h)

theorem app_cst {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X) (hf : f ≫ q = q')
    (U : X.Opens) (a : R) : (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE, appLE_cst q q' f hf]

def cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : LB.Sec L) : LB.Sec L where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_cst, res_cst, s.compat, mul_left_comm]

theorem nonzeroLocus_cMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : LB.Sec L) : Out.nonzeroLocus (cMul q a s) = Out.nonzeroLocus s := by
  unfold Out.nonzeroLocus
  refine iSup_congr fun k => ?_
  have hu : IsUnit (constFn q (L.U k) a) := (ha.map _).map _
  show X.basicOpen (constFn q _ a * s.f k) = _
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit hu]
  exact inf_eq_right.2 (X.basicOpen_le _)

theorem valR_cMul {A : Type} [CommRing A] {X : Scheme.{0}} (q : X ⟶ Sp R) (φ : R →+* A) (x : Sp A ⟶ X)
    (hx : x ≫ q = spMap φ) (U : X.Opens) (a : R) (f : Γ(X, U)) :
    valR x U (constFn q U a * f) = φ a * valR x U f := by
  unfold valR
  split_ifs with h
  · rw [map_mul, map_mul, appLE_cst q (spMap φ) x hx U ⊤ h]
    congr 1
    have h3 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
      (Scheme.Hom.app_eq_appLE (spMap φ) (U := ⊤)).symm
    have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
    have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (((spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) = φ a
    rw [h3]
    refine h2.trans ?_
    simp
  · simp

section Twist

variable {A : Over (Sp R)} [GrpObj A] (L : LB A.left)

theorem twist_cMul {T : Over (Sp R)} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b]))
    (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)) (c : R)
    (h : IsTwistPull A L ψ m hm a b α s s') :
    IsTwistPull A L ψ m hm a b α (cMul (T ⊗ A).hom c s) (cMul (T ⊗ A).hom c s') := by
  intro j
  have e := h j
  simp only [cMul]
  erw [RingHom.map_mul, res_cst, e, RingHom.map_mul, app_cst _ _ ψ.left (Over.w ψ), RingHom.map_mul, res_cst]
  exact mul_left_comm _ _ _

end Twist

end GlobalTheory.MBLow.ScaleJet

namespace GlobalTheory.MBLow.ScaleJet

theorem polAVSectionInverseImage_mulConstant {R : Type} [CommRing R] (P : PolAV (Sp R)) (T : Over (Sp R)) (s : P.L.Sec)
    (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (c : R) (h : IsPolAVSectionInverseImage P T s t) :
    IsPolAVSectionInverseImage P T (cMul P.A.hom c s) (cMul (T ⊗ P.A).hom c t) := by
  intro i hi
  have e := h i hi
  simp only [cMul]
  erw [e, RingHom.map_mul, appLE_cst P.A.hom (T ⊗ P.A).hom (snd T P.A).left (Over.w (snd T P.A))]

theorem scale_key : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 →
    ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧
      ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C),
        ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i)
          (fun i j => a * J i j) := by
  intro κ hκ C _ _ x a ha
  have hne : ∀ s : Sp C, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus (cMul x.P.A.hom a x.th) := by
    intro s
    rw [nonzeroLocus_cMul _ ha.isUnit]
    exact x.th_ne s
  have hl : ∀ i, IsLieComb ((1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i) x.v (x.v i) := by
    intro i
    have : (1 : Matrix (Fin x.P.g) (Fin x.P.g) C) i = Pi.single i 1 := by
      ext k; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this]
    have := x.P.isAb.comm
    exact (LieComb.lieComb_algebra _ _ _ x.v x.basis.1).2.2.2.1 i
  refine ⟨cMul x.P.A.hom a x.th, hne, ?_, ?_⟩
  · have e := hκ C x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis (cMul x.P.A.hom a x.th) hne x.v x.basis a 1
      (fun i => rfl) hl
    simpa [Matrix.det_one] using e
  · rintro g hg m I pt ϑ J ⟨th, hon, U, t, i₀, c, hU, hi₀, hv⟩
    refine ⟨cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a th, polAVSectionInverseImage_mulConstant x.P _ x.th th a hon, U,
      fun i => cMul (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom a (t i), i₀, c, fun i => ⟨(hU i).1, ?_⟩, hi₀, fun i j => ?_⟩
    · obtain ⟨α, s₁, h1, h2, h3, h4⟩ := (hU i).2
      exact ⟨α, cMul _ a s₁, h1, h2, twist_cMul _ _ _ _ _ _ _ _ _ _ h3, twist_cMul _ _ _ _ _ _ _ _ _ _ h4⟩
    · have hx : epsLift (x.v (j.cast hg.symm)) ≫ (Over.mk (𝟙 (Sp C)) ⊗ x.P.A).hom =
          spMap (algebraMap C (DualNumber C)) := Over.w _
      have e := valR_cMul _ _ _ hx _ a ((t i).f fun _ => i₀)
      refine e.trans ?_
      rw [hv i j]
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl] <;> ring

end GlobalTheory.MBLow.ScaleJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open TopForm

section Pair

variable {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}

def topPair (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) : Forms α n →ₗ[A] A :=
  letI := α.toAlgebra
  exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap
    (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)))

end Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev PairIx (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) : Type :=
  Σ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Fin (Dw.mult τ.1) × Fin (Dw.mult ((starRingEnd ℂ).comp τ.1))

def symPair {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (P : PairIx H Dw) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b =>
    (if a = e ⟨P.1.1, P.2.1⟩ ∧ b = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ then 1 else 0) +
      (if a = e ⟨(starRingEnd ℂ).comp P.1.1, P.2.2⟩ ∧ b = e ⟨P.1.1, P.2.1⟩ then 1 else 0)

abbrev genPt (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z :=
  (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))

abbrev GenDer (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] : Type :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField

def GenKS (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)]
    (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left))
    (D : Fin Dw.dim → GenDer TF Z) : Prop :=
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  ∃ (U : TF.Y.X.affineOpens) (_ : U.1 ≤ barComp TF.Y Z) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField)
    (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (ε : Fin Dw.dim ≃ PairIx H Dw)
    (Dl : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U),
    spMap ρ ≫ LogKS.chart U = genPt TF Z ≫ (barComp TF.Y Z).ι ∧
    (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) ∧
    (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') ∧
    (∀ τ i, w τ i = spMap (dualMap ρ) ≫ v (e ⟨τ, i⟩)) ∧
    (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (Dl j).1 (symPair e (ε j))) ∧
    ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r)

end GlobalTheory.LogKSDiv

namespace GlobalTheory.LogKSDiv

open TopForm

theorem topPair_dForm {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D : Fin n → (letI := α.toAlgebra; Derivation k A A)) (f : Fin n → A) :
    topPair α D (dForm α f) = (Matrix.of fun i j => (letI := α.toAlgebra; (D j : Derivation k A A)) (f i)).det := by
  letI := α.toAlgebra
  rw [dForm_eq, topPair, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of _) = _
  congr 1
  ext i j
  exact Derivation.liftKaehlerDifferential_comp_D (D j) (f i)

end GlobalTheory.LogKSDiv
end
end

