module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnCharts
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompEmbEqOfFrBor
section
open AlgebraicGeometry CategoryTheory Limits NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg.GenericFlagInj

theorem unitri_eq_of_lower {S : Type} [CommRing S] {n : ℕ} (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ i j, j < i → A i j = 0) (hAd : ∀ i, A i i = 1)
    (hA' : ∀ i j, j < i → A' i j = 0) (hAd' : ∀ i, A' i i = 1)
    (hL : ∀ i j, i < j → L i j = 0) (e : A' = L * A) : A' = A := by
  first
  | exact @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | (apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genPt_inj {Z Z' : Comp Xo c} (h : genPt Z = genPt Z') : Z = Z' := by
  have g : ∀ W : Comp Xo c, IsGenericPoint (genPt W) (W : Set (Xo.XF c)) := fun W =>
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  exact Subtype.ext (by rw [← (g Z).def, ← (g Z').def, h])

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := by
  symm
  show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem genSp_eq {T : Type} [CommRing T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') :
    spMap ψ.toRingHom ≫ genSp Z = spMap ψ'.toRingHom ≫ genSp Z' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h
  · have e := genSp_strK Z
    have e' := genSp_strK Z'
    rw [Category.assoc, Category.assoc]
    erw [e, e']
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext r
    exact (ψ.commutes r).trans (ψ'.commutes r).symm

theorem comp_eq {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') : Z = Z' := by
  obtain ⟨p⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  have e := congrArg (fun f : Sp T ⟶ Xo.XF c => f p) (genSp_eq ψ ψ' h)
  simp only [Scheme.Hom.comp_apply, genSp] at e
  apply genPt_inj
  exact (Scheme.fromSpecResidueField_apply _ _).symm.trans (e.trans (Scheme.fromSpecResidueField_apply _ _))

theorem emb_eq {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (ψ ψ' : kap Z →ₐ[c.F] T)
    (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z) : ψ = ψ' := by
  have e := genSp_eq ψ ψ' h
  haveI : Mono (genSp Z) := by unfold genSp; infer_instance
  have e2 : spMap ψ.toRingHom = spMap ψ'.toRingHom := (cancel_mono (genSp Z)).1 e
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
  exact AlgHom.coe_ringHom_injective e3

noncomputable def resKap {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T) : kap Z →ₐ[c.F] T :=
  { φ.toRingHom.comp (algebraMap (kap Z) (Om Z)) with
    commutes' := fun r => by
      have := φ.commutes r
      rw [gfp_tower] at this
      exact this }

theorem x_eq {T : Type} [CommRing T] [Algebra c.F T] (h : GenFrEx Xo c) {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T)
    {y : FrPt Xo c T} (hy : FrMap φ (genFr h Z) y) : y.x = spMap (resKap φ).toRingHom ≫ xGen Z := by
  rw [hy.1, (isGenFr_genFr h Z).1, ← Category.assoc, spMap_comp_ring]
  rfl

theorem eq_of_frBor {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] (h : GenFrEx Xo c) (Z Z' : Comp Xo c)
    (φ : Om Z →ₐ[c.F] T) (φ' : Om Z' →ₐ[c.F] T) (y y' : FrPt Xo c T) (t : Ix Dw → Tˣ)
    (hy : FrMap φ (genFr h Z) y) (hy' : FrMap φ' (genFr h Z') y') (hb : FrBor t y y') : Z = Z' ∧ HEq φ φ' := by
  have hx := x_eq h φ hy
  have hx' := x_eq h φ' hy'
  have hxx := hx.symm.trans (hb.1.symm.trans hx')
  obtain rfl : Z = Z' := comp_eq _ _ hxx
  refine ⟨rfl, heq_of_eq ?_⟩
  have hψ : resKap φ = resKap φ' := emb_eq _ _ hxx
  obtain ⟨y₀, hy₀, hc⟩ := (isGenFr_genFr h Z).2
  have pull : ∀ (χ : Om Z →ₐ[c.F] T) (w : FrPt Xo c T), FrMap χ (genFr h Z) w → ∀ τ i,
      IsCombAt w.x (fun j => spMap (dualMap (resKap χ).toRingHom) ≫ y₀.u τ j) (fun j => χ (genCoef Z τ i j))
        (w.u τ i) := by
    intro χ w hw τ i
    refine isCombAt_pull χ.toRingHom hw.1 (fun j => ?_) (hw.2.1 τ i) (hc τ i)
    rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp]
    rfl
  have hcoef : ∀ τ i j, φ' (genCoef Z τ i j) = φ (genCoef Z τ i j) := by
    intro τ
    choose cf hd hz hcf using hb.2.1 τ
    have hyx : y.x = spMap (resKap φ).toRingHom ≫ y₀.x := by rw [hx, hy₀]
    have key := unitri_eq_of_lower (Matrix.of fun i j => φ (genCoef Z τ i j))
      (Matrix.of fun i j => φ' (genCoef Z τ i j)) (Matrix.of cf)
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef])
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef]) (fun i j hij => hz i j hij) ?_
    · intro i j
      exact congrFun (congrFun key i) j
    · ext i j
      have h1 := pull φ' y' hy' τ i
      rw [← hψ, hb.1] at h1
      have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo T y.x
        (fun j => spMap (dualMap (resKap φ).toRingHom) ≫ y₀.u τ j)
        (fun j => hyx ▸ GlobalTheory.Frames.FramedBaseChange.tan_bc (resKap φ).toRingHom (y₀.tan τ j)) (y.u τ)
        (Matrix.of fun j i => φ (genCoef Z τ i j)) (cf i) (y'.u τ i) (pull φ y hy τ) (hcf i)
      have ht : IsTanAt y.x (y'.u τ i) := hb.1 ▸ y'.tan τ i
      rw [hyx] at h1 h2 ht
      have h3 := (GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c _ T (resKap φ) y₀ τ _ ht (y'.eig τ i)).unique h1 h2
      have h4 := congrFun h3 j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at h4
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [h4]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · exact AlgHom.congr_fun hψ r
  · obtain ⟨τ, ⟨i, j⟩, hij⟩ := v
    have := hcoef τ i j
    simp only [genCoef, dif_pos (show i < j from hij)] at this
    exact this.symm

end GlobalTheory.Reg.GenericFlagInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem MChart.Lift.exists_coordinates (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (M : MChart Y) (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
    (Λ : M.Lift f y.x) :
    ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L,
      Λ.LieTie g y.u ∧ ∀ τ, LinearIndependent L (g τ).transpose := by
  classical
  have hb := vec_bijective E H Dw l Xo c O β Y M L f y.x Λ
  have hc := _root_.GlobalTheory.Reg.VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M L f y.x Λ
  choose cv hcv using fun τ i => (hb.2.2 (y.u τ i) (y.4 τ i)).exists
  refine ⟨fun τ j i => cv τ i j, fun τ i => hcv τ i, fun τ => ?_⟩
  refine Fintype.linearIndependent_iff.2 fun a ha k => ?_
  have ha' : ∑ i, a i • cv τ i = 0 := ha
  have s1 : ∑ i, ((Pi.single k (1 : L) : Fin (Dw.mult τ) → L) + a) i • cv τ i = cv τ k := by
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib, ha']
  have s2 : ∑ i, (Pi.single k (1 : L) : Fin (Dw.mult τ) → L) i • cv τ i = cv τ k := by
    simp [Pi.single_apply]
  have e1 : IsCombAt y.x (y.u τ) (Pi.single k 1 + a) (y.u τ k) :=
    (hc _ (cv τ) (y.u τ) _ (y.u τ k) (hcv τ)).2 (by rw [s1]; exact hcv τ k)
  have e2 : IsCombAt y.x (y.u τ) (Pi.single k 1) (y.u τ k) :=
    (hc _ (cv τ) (y.u τ) _ (y.u τ k) (hcv τ)).2 (by rw [s2]; exact hcv τ k)
  have h := (y.6 τ (y.u τ k) (y.4 τ k) (y.5 τ k)).unique e1 e2
  simpa using congrFun h k

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_integral_lift (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    {J : Type} (M : J → MChart Y) (hM : ∀ x : Y.X, ∃ j, x ∈ (M j).U) (L : Type) [Field L] [Algebra c.F L]
    (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (y : FrPt Xo c L) :
    ∃ (j : J) (f : Γ(Y.X, (M j).U) →+* L), (∀ a, f a ∈ W) ∧ Nonempty ((M j).Lift f y.x) := by
  classical
  have hx : y.x ≫ Xo.s = spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.2]
    unfold sOf
    exact spMap_comp_moduli_spaces _ _
  obtain ⟨yt, ⟨-, hyt⟩, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).1 W L
    (((algebraMap c.F L).comp β).codRestrict W hW) (algebraMap c.F L)
    (pullback.lift y.x (spMap (algebraMap c.F L)) hx) (RingHom.ext fun _ => rfl) (pullback.lift_snd _ _ _)
  obtain ⟨j, hj⟩ := hM (yt (IsLocalRing.closedPoint W))
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom (M j).hU W yt hj
  refine ⟨j, (algebraMap W L).comp ψ, fun a => (ψ a).2, ?_⟩
  have key : pullback.lift y.x (spMap (algebraMap c.F L)) hx ≫ Y.j =
      spMap ((algebraMap W L).comp ψ) ≫ (M j).hU.fromSpec := by
    rw [spMap_comp_moduli_spaces, Category.assoc, hψ, hyt]
  have hn := MChart.nonempty_lift E H Dw l Xo c O β Y (M j) L ((algebraMap W L).comp ψ)
    (pullback.lift y.x (spMap (algebraMap c.F L)) hx) (pullback.lift_snd _ _ _) key
  rwa [pullback.lift_fst] at hn

theorem exists_finite_pchart_cover : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), Covers P := by
  intro hS E _ _ _ H Dw l Xo c hBC O _ _ _ _ _ Y hP
  classical
  obtain ⟨J₀, hJ₀, M, hM⟩ := exists_finite_mchart_cover E H Dw l Xo c O (algebraMap O c.F) Y hP
  have hT := fun (j : J₀) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin (M j).n) =>
    _root_.GlobalTheory.Reg.exists_pChart_of_cell hS E H Dw l Xo c hBC O Y hP (M j) ix
  choose K hK P hPc using hT
  refine ⟨(j : J₀) × (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin (M j).n) × K j ix, ?_,
    fun q => P q.1 q.2.1 q.2.2, ?_⟩
  · infer_instance
  · intro L _ _ W hW y
    obtain ⟨j, f, hf, ⟨Λ⟩⟩ := exists_integral_lift E H Dw l Xo c O (algebraMap O c.F) Y M hM L W hW y
    obtain ⟨g, hg, hind⟩ := MChart.Lift.exists_coordinates E H Dw l Xo c O (algebraMap O c.F) Y (M j) L f y Λ
    choose ixs u b hu hlow hone hbt hdiag hgu using
      fun τ => GlobalTheory.exists_integral_pivot_decomposition L W (M j).n (Dw.mult τ) (g τ) (hind τ)
    obtain ⟨k, hk⟩ := hPc j ixs L W f y Λ u b hf hu (fun τ => ⟨hlow τ, hone τ⟩) (fun τ => ⟨hbt τ, hdiag τ⟩)
      (by rw [← funext hgu]; exact hg)
    exact ⟨⟨j, ixs, k⟩, hk⟩

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponent
section
namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Reg.exists_idem_section : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c → ∀ h : _root_.Formalism.L2.Pj.GenFrEx Xo c,
      _root_.GlobalTheory.Reg.Atlas h → ∀ Z : _root_.Formalism.L2.Pj.Comp Xo c, ∃ χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0,
        χ * χ = χ ∧ _root_.Formalism.L2.Pj.evC h Z χ = 1 ∧ ∀ Z', Z' ≠ Z → _root_.Formalism.L2.Pj.evC h Z' χ = 0 := by
  intro E _ _ _ H Dw l Xo c hev h hcov Z
  classical
  have hexp : _root_.Formalism.L2.Pj.ex Dw 0 0 = 0 := by
    unfold _root_.Formalism.L2.Pj.ex
    funext x
    cases x <;> rfl
  have hreg : ∀ C : _root_.GlobalTheory.Reg.FChart h,
      _root_.Formalism.L2.Pj.wchar (_root_.Formalism.L2.Pj.ex Dw 0 0) C.t *
        (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) C.Z ∈ C.R := by
    intro C
    rw [hexp]
    unfold _root_.Formalism.L2.Pj.wchar
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, _root_.one_mul]
    split_ifs
    · exact C.R.one_mem
    · exact C.R.zero_mem
  obtain ⟨χ, hχ, hval⟩ := _root_.GlobalTheory.Reg.SecGlue.exists_sec_of_regular E H Dw l Xo c hev h
    hcov 0 0 (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) hreg
  refine ⟨χ, hχ, ?_, by simp [hval], fun Z' hZ' => by simp [hval, hZ']⟩
  have hsq : χ * χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := by simpa using _root_.Formalism.L2.Pj.sec_mul Xo c 0 0 0 0 hχ hχ
  have hmem : χ * χ - χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := Submodule.sub_mem _ hsq hχ
  refine sub_eq_zero.mp (_root_.GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hev h hcov
    0 0 _ hmem fun Z' => ?_)
  have hmul : _root_.Formalism.L2.Pj.evC h Z' (χ * χ) = _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_mul _ _ _ _ _
  have hadd : _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ + χ) =
      _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ) + _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_add _ _ _ _ _
  have hidem : _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ = _root_.Formalism.L2.Pj.evC h Z' χ := by
    rw [hval]
    split_ifs <;> simp
  rw [sub_add_cancel, hmul, hidem] at hadd
  exact add_eq_right.mp hadd.symm

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModularSectionOfIntegralGenericValue
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.IntSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wchar_ex_smul {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n d : ℕ) (t : Ix Dw → Sˣ) :
    wchar (ex Dw (d • a) (d * n)) t = wchar (ex Dw a n) t ^ d := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul]
  cases i <;> simp [ex, mul_comm]

theorem one_mem (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (1 : Rul Xo c) ∈ sec Xo c (0 • a) (0 * n) := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  rw [wchar_ex_smul]; simp

theorem mul_mem {a : (E →+* ℂ) × ℕ → ℕ} {n d e : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c (d • a) (d * n))
    (hg : g ∈ sec Xo c (e • a) (e * n)) : f * g ∈ sec Xo c ((d + e) • a) ((d + e) * n) := by
  rw [add_smul, add_mul]; exact sec_mul Xo c _ _ _ _ hf hg

theorem pow_mem {a : (E →+* ℂ) × ℕ → ℕ} {n d : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c (d • a) (d * n)) (j : ℕ) :
    f ^ j ∈ sec Xo c ((j * d) • a) ((j * d) * n) := by
  induction j with
  | zero => rw [pow_zero, zero_mul]; exact one_mem a n
  | succ j ih => rw [pow_succ, Nat.succ_mul]; exact mul_mem ih hf

theorem prod_mem {a : (E →+* ℂ) × ℕ → ℕ} {n N : ℕ} {w : Fin N → Rul Xo c} (hw : ∀ i, w i ∈ sec Xo c a n)
    (e : Fin N → ℕ) (s : Finset (Fin N)) :
    ∏ i ∈ s, w i ^ e i ∈ sec Xo c ((∑ i ∈ s, e i) • a) ((∑ i ∈ s, e i) * n) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact one_mem a n
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    refine mul_mem ?_ ih
    have := pow_mem (d := 1) (a := a) (n := n) (f := w i) (by simpa using hw i) (e i)
    rwa [Nat.mul_one] at this

theorem aeval_mem {a : (E →+* ℂ) × ℕ → ℕ} {n N d : ℕ} {w : Fin N → Rul Xo c} (hw : ∀ i, w i ∈ sec Xo c a n)
    {P : MvPolynomial (Fin N) c.F} (hP : P.IsHomogeneous d) :
    MvPolynomial.aeval w P ∈ sec Xo c (d • a) (d * n) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have h1 : ∑ i, s i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hs)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [← h1]
  exact prod_mem hw s Finset.univ

def evA (hL : EvLaws Xo c) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    Rul Xo c →ₐ[c.F] S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y (hL.test S y)
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    have h1 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) r 1 y
    rw [evalAt_one _ _ y (hL.test S y), _root_.mul_one] at h1
    exact h1

theorem evC_aeval (hL : EvLaws Xo c) (h : GenFrEx Xo c) (Z : Comp Xo c) {N : ℕ} (w : Fin N → Rul Xo c)
    (P : MvPolynomial (Fin N) c.F) :
    evC h Z (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun s => evC h Z (w s)) P := by
  have := MvPolynomial.comp_aeval_apply (evA hL (genFr h Z)) P (f := w)
  exact this

theorem chart_mem (hL : EvLaws Xo c) {h : GenFrEx Xo c} (C : FChart h) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : wchar (ex Dw a n) C.t * evC h C.Z f ∈ C.R := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 := hL.wt a n f hf (Om C.Z) C.t (genFr h C.Z) C.yg (hL.test _ _) (hL.test _ _) C.bor
  set_option synthInstance.maxHeartbeats 200000 in
  have h2 := _root_.GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf C.R (Om C.Z) C.R.val C.y C.yg C.gen
  unfold evC
  rw [← h1, h2]
  exact (evR Xo c f C.y).2

theorem mem_of_integral {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω)
    (sm : Algebra.Smooth K R) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) (m : ℕ) (r : ℕ → Ω)
    (hr : ∀ i < m, r i ∈ R) (x : Ω) (hx : x ^ m + ∑ i ∈ Finset.range m, r i * x ^ i = 0) : x ∈ R := by
  classical
  have hq : IsIntegrallyClosed (R ⧸ (⊥ : Ideal R)) :=
    GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth K R ⊥ (by simp [IsDomain.minimalPrimes_eq_singleton_bot])
  have hR : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot R)
  have hF : IsFractionRing R Ω := by
    refine IsFractionRing.of_field R Ω fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by rw [eq_div_iff]; exacts [e, hb0]⟩
  let r' : Fin m → R := fun i => ⟨r i, hr i i.2⟩
  have hi : IsIntegral R x := by
    refine ⟨Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (r' i) * Polynomial.X ^ (i : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt r'), ?_⟩
    rw [← hx, Finset.sum_range (fun i => r i * x ^ i)]
    simp [Polynomial.eval₂_finsetSum, r']
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  exact y.2

end GlobalTheory.Reg.IntSec


open GlobalTheory.Reg.IntSec in
theorem GlobalTheory.Reg.exists_sec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), (∀ i, w i ∈ sec Xo c a n) → ∀ (Z : Comp Xo c) (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F) (b : Om Z), (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → b ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval (fun s => evC h Z (w s)) (cf i) * b ^ i = 0 → ∃ g ∈ sec Xo c (k • a) (k * n), evC h Z g = b ∧ (∀ Z', Z' ≠ Z → evC h Z' g = 0) ∧ g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA a n N w hw Z k m cf b hcf hb
  classical
  obtain ⟨g, hg, hgv⟩ := _root_.GlobalTheory.Reg.SecGlue.exists_sec_of_regular E H Dw l Xo c hL h hA (k • a) (k * n)
    (Function.update (fun Z' => (0 : Om Z')) Z b) (by
      intro C
      by_cases hZ : C.Z = Z
      · subst hZ
        rw [Function.update_self, wchar_ex_smul]
        refine mem_of_integral C.R C.sm C.frac m
          (fun i => wchar (ex Dw a n) C.t ^ ((m - i) * k) * evC h C.Z (MvPolynomial.aeval w (cf i))) ?_ _ ?_
        · intro i hi
          rw [← wchar_ex_smul]
          exact chart_mem hL C (aeval_mem hw (hcf i hi))
        · have h0 := congrArg (fun x => wchar (ex Dw a n) C.t ^ (k * m) * x) hb
          simp only [mul_zero, mul_add, Finset.mul_sum] at h0
          rw [← h0, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : k * m = (m - i) * k + k * i := by
            rw [mul_comm (m - i), ← mul_add, Nat.sub_add_cancel (Finset.mem_range.1 hi).le]
          rw [evC_aeval hL, hi', pow_add, mul_pow, ← pow_mul]
          ring
      · rw [Function.update_of_ne hZ, mul_zero]
        exact C.R.zero_mem)
  have hZ : evC h Z g = b := by rw [hgv, Function.update_self]
  have hZ' : ∀ Z', Z' ≠ Z → evC h Z' g = 0 := fun Z' hne => by rw [hgv, Function.update_of_ne hne]
  refine ⟨g, hg, hZ, hZ', ?_⟩
  refine _root_.GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h hA ((k + m * k) • a) ((k + m * k) * n) _ ?_ ?_
  · refine Submodule.add_mem _ (IntSec.mul_mem hg (IntSec.pow_mem hg m)) (Submodule.sum_mem _ fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    have e : k + m * k = k + (m - i) * k + i * k := by
      rw [add_assoc, ← add_mul, Nat.sub_add_cancel hi'.le]
    rw [e]
    exact IntSec.mul_mem (IntSec.mul_mem hg (aeval_mem hw (hcf i hi'))) (IntSec.pow_mem hg i)
  · intro Z'
    have e : g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i =
        g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval w (cf i) * g ^ i) := by
      simp only [mul_add, Finset.mul_sum, _root_.mul_assoc]
    have ev : ∀ f, evC h Z' f = evA hL (genFr h Z') f := fun f => rfl
    rw [e, ev, map_mul]
    by_cases hne : Z' = Z
    · subst hne
      refine mul_eq_zero_of_right _ ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb, map_add (f := _), map_pow, map_sum, ← ev, hZ]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← ev, ← ev, hZ, evC_aeval hL]
    · rw [← ev, hZ' Z' hne, zero_mul]
end
end

