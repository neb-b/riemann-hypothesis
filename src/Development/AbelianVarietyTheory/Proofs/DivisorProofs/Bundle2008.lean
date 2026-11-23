module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadGenericEigenFrameAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBundleFramesChartsChangeBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic
open Formalism.L2.Pj
open GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg GlobalTheory.FlagMod
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.ChartLieFrame

theorem eq_of_loc {Z : Scheme.{0}} {W : Z.Opens} {a b : Γ(Z, W)}
    (h : ∀ p ∈ W, ∃ (N : Z.Opens) (e : N ≤ W), p ∈ N ∧ resG Z e a = resG Z e b) : a = b :=
  ext_ev_loc fun p hp => by
    obtain ⟨N, e, hpN, hab⟩ := h p hp
    exact ⟨N, hpN, fun S _ z hz hN => by rw [← ev_res z e hN hz a, ← ev_res z e hN hz b, hab]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

def Rep (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)) : Prop :=
  ∀ (W : Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W)),
    VB.dualApp s h w = tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (h.trans hU)) j)) (tau_le hW le_rfl) w

theorem tanLin_res (M : MChart Y) {W W₀ V : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (hV : W₀ ≤ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega Y.t.G, V)) (j : Fin M.n) :
    tanLin Y.t (tau_le hW (e.trans hV)) s (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j) =
      fun i => resG Y.X e (tanLin Y.t (tau_le hW₀ hV) s (lieBasis M (tau hW₀) (tau_le hW₀ hM) j) i) := by
  have φe : spMap (ev (tau hW) W₀ (tau_le hW e)) ≫ tau hW₀ = tau hW := spMap_ev (tau hW) hW₀ (tau_le hW e)
  rw [← tanPull_lieBasis M _ φe (tau_le hW₀ hM) (tau_le hW (e.trans hM)) j,
    tanLin_tanPull Y.t _ φe (tau_le hW₀ hV) (tau_le hW (e.trans hV))]
  funext i
  exact ev_tau hW e (tau_le hW e) _

theorem tanEv_res (M : MChart Y) {W W₀ : Y.X.Opens} (hW : IsAffineOpen W) (hW₀ : IsAffineOpen W₀) (e : W ≤ W₀)
    (hM : W₀ ≤ M.U) (w : Γ(GlobalTheory.LieVB.omega Y.t.G, W₀)) (j : Fin M.n) :
    tanEv Y.t (isTan_tv (lieBasis M (tau hW) (tau_le hW (e.trans hM)) j)) (tau_le hW le_rfl) (resM _ e w) =
      resG Y.X e (tanEv Y.t (isTan_tv (lieBasis M (tau hW₀) (tau_le hW₀ hM) j)) (tau_le hW₀ le_rfl) w) := by
  rw [tanEv_resM]
  exact congrFun (tanLin_res M hW hW₀ e hM le_rfl ![w] j) 0

theorem Rep.res {M : MChart Y} {j : Fin M.n} {U : Y.X.Opens} {hU : U ≤ M.U} {s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) {U' : Y.X.Opens} (e : U' ≤ U) : Rep M j (e.trans hU) (resM _ e s) := fun W hW h w => by
  rw [VB.dualApp_res]
  exact hs W hW (h.trans e) w

theorem rep_unique (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {s s' : Γ(GlobalTheory.LieVB.Lie Y.t.G, U)}
    (hs : Rep M j hU s) (hs' : Rep M j hU s') : s = s' :=
  VB.dual_ext fun W h w => eq_of_loc fun p hp => by
    obtain ⟨N, hN, hpN, hNW'⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W) hp
    have hNW : N ≤ W := hNW'
    refine ⟨N, hNW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← VB.dualApp_resM, hs N hN, hs' N hN]

theorem rep_of_cover (M : MChart Y) (j : Fin M.n) {U : Y.X.Opens} (hU : U ≤ M.U) {ι : Type} (V : ι → Y.X.Opens)
    (hV : ∀ k, V k ≤ U) (hc : U ≤ iSup V) (s : Γ(GlobalTheory.LieVB.Lie Y.t.G, U))
    (H : ∀ k, Rep M j ((hV k).trans hU) (resM _ (hV k) s)) : Rep M j hU s := fun W hW h w =>
  eq_of_loc fun p hp => by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (h hp))
    obtain ⟨N, hN, hpN, hNW⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := W ⊓ V k) ⟨hp, hk⟩
    have eW : N ≤ W := fun q hq => (hNW hq).1
    have eV : N ≤ V k := fun q hq => (hNW hq).2
    refine ⟨N, eW, hpN, ?_⟩
    rw [← VB.dualApp_resM, ← tanEv_res M hN hW eW (h.trans hU) w j]
    have := H k N hN eV (resM _ eW w)
    rw [VB.dualApp_res] at this
    exact this

def locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n) (hC : IsAffineOpen C.U)
    (hM : C.U ≤ M.U) : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U) :=
  ∑ i : Fin n, (tanLin Y.t (tau_le hC le_rfl) C.e (lieBasis M (tau hC) (tau_le hC hM) j) i : Γ(Y.X, C.U)) •
    (C.isFrame.coord i : Γ(GlobalTheory.LieVB.Lie Y.t.G, C.U))

theorem rep_locSec (M : MChart Y) (j : Fin M.n) {n : ℕ} (C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n)
    (hC : IsAffineOpen C.U) (hM : C.U ≤ M.U) : Rep M j hM (locSec M j C hC hM) := fun W hW h w => by
  rw [locSec, VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    VB.IsFrame.dualApp_coord, smul_eq_mul]
  conv_rhs => rw [← (C.isFrame.basis h).sum_repr w]
  rw [tanEv_sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [VB.IsFrame.basis_apply, tanEv_resM, ev_tau_self, RingHom.id_apply, _root_.mul_comm]
  exact congrArg (((C.isFrame.basis h).repr w i) * ·) (congrFun (tanLin_res M hW hC h hM le_rfl C.e j) i).symm

theorem exists_rep (M : MChart Y) (j : Fin M.n) : ∃ s : Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), Rep M j le_rfl s := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  let V : (Σ n : ℕ, {C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n // IsAffineOpen C.U ∧ C.U ≤ M.U}) → Y.X.Opens :=
    fun k => k.2.1.U
  have hV : ∀ k, V k ≤ M.U := fun k => k.2.2.2
  have hc : M.U ≤ iSup V := fun p hp => by
    obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
    obtain ⟨N, hN, hpN, hNU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := M.U ⊓ U₀) ⟨hp, hp₀⟩
    have e₁ : N ≤ M.U := fun q hq => (hNU hq).1
    have e₂ : N ≤ U₀ := fun q hq => (hNU hq).2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨n, ⟨⟨N, fun i => resM _ e₂ (e i), he.res e₂⟩, hN, e₁⟩⟩, hpN⟩
  have hrep : ∀ k, Rep M j (hV k) (locSec M j k.2.1 k.2.2.1 k.2.2.2) := fun k => rep_locSec M j _ _ _
  obtain ⟨t, ht⟩ := Twist.exists_sec_of_cover V hV hc (fun k => locSec M j k.2.1 k.2.2.1 k.2.2.2) fun k k' =>
    rep_unique M j (inf_le_left.trans (hV k)) ((hrep k).res inf_le_left) ((hrep k').res inf_le_right)
  exact ⟨t, rep_of_cover M j le_rfl V hV hc t fun k => by rw [ht k]; exact hrep k⟩

theorem isFrame_of_rep (M : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ j, Rep M j le_rfl (f j)) :
    VB.IsFrame f := by
  haveI := Y.t.semi
  haveI := Y.t.semi.smooth
  refine VB.isFrame_of_forall_exists fun V h p hp => ?_
  obtain ⟨U₀, n, e, hp₀, he⟩ := GlobalTheory.LieVB.exists_isFrame_omega Y.t.G p
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := V ⊓ U₀) ⟨hp, hp₀⟩
  have e₁ : W ≤ V := fun q hq => (hWU hq).1
  have e₂ : W ≤ U₀ := fun q hq => (hWU hq).2
  let C : VB.Chart (GlobalTheory.LieVB.omega Y.t.G) n := ⟨W, fun i => resM _ e₂ (e i), he.res e₂⟩
  refine ⟨W, e₁, hpW, ?_⟩
  let R := (C.isFrame.dual.basis (le_rfl : C.U ≤ C.U)).equivFun
  let T : (Fin M.n → Γ(Y.X, W)) → (Fin n → Γ(Y.X, W)) :=
    (tanLin Y.t (tau_le hW (le_rfl : W ≤ C.U)) C.e) ∘ (lieBasis M (tau hW) (tau_le hW (e₁.trans h))).equivFun.symm
  have hT : Function.Bijective T :=
    (HodgeCech.tanLin_bijective Y.t C (tau hW) (tau_le hW le_rfl)).comp (LinearEquiv.bijective _)
  have key : ∀ a, R (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j)) a) = T a := by
    intro a
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [R, T, Function.comp_apply, Module.Basis.equivFun_apply, VB.IsFrame.dual_basis_repr,
      Fintype.linearCombination_apply, VB.dualApp_sum, LinearMap.sum_apply, VB.dualApp_smul, LinearMap.smul_apply,
      VB.dualApp_res, Module.Basis.equivFun_symm_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, GlobalTheory.LB.resG_self]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf k W hW _ _, GlobalTheory.Twist.resM_self]
    rfl
  have hc : R ∘ (Fintype.linearCombination Γ(Y.X, W) (fun j => resM _ (e₁.trans h) (f j))) = T := funext key
  exact (Function.Bijective.of_comp_iff' R.bijective _).1 (hc ▸ hT)

theorem rep_chg (M M' : MChart Y) (f : Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U)) (hf : ∀ i, Rep M i le_rfl (f i))
    (j : Fin M'.n) :
    Rep M' j inf_le_right (∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f i)) := fun W hW h w => by
  have ev' : ∀ v, tanEv Y.t (isTan_tv v) (tau_le hW le_rfl) w = tanLin Y.t (tau_le hW le_rfl) ![w] v 0 := fun v => rfl
  rw [VB.dualApp_sum]
  simp only [VB.dualApp_smul, LinearMap.sum_apply, LinearMap.smul_apply, VB.dualApp_res, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ev', ← (lieBasis M (tau hW) (tau_le hW (h.trans inf_le_left))).sum_toMatrix_smul_self
    (lieBasis M' (tau hW) (tau_le hW (h.trans inf_le_right))) j, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hf i W hW (h.trans inf_le_left) w, ev']
  refine congrArg₂ (· * ·) ?_ rfl
  rw [← chg_map M M' (tau hW) (tau_le hW (h.trans inf_le_left)) (tau_le hW (h.trans inf_le_right)) (tau_le hW h),
    Matrix.map_apply, ev_tau hW h]

theorem exists_lieFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∃ f : ∀ M : GlobalTheory.Reg.MChart Y, Fin M.n → Γ(GlobalTheory.LieVB.Lie Y.t.G, M.U), (∀ M, GlobalTheory.VB.IsFrame (f M)) ∧ ∀ (M M' : GlobalTheory.Reg.MChart Y) (j : Fin M'.n), GlobalTheory.Twist.resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) = ∑ i, GlobalTheory.FlagMod.chg M M' i j • GlobalTheory.Twist.resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i) := by
  intro E _ _ _ H Dw l Xo c O _ β Y
  choose f hf using fun (M : MChart Y) (j : Fin M.n) => exists_rep M j
  exact ⟨f, fun M => isFrame_of_rep M (f M) (hf M), fun M M' j =>
    rep_unique M' j inf_le_right ((hf M' j).res inf_le_right) (rep_chg M M' (f M) (hf M) j)⟩

end GlobalTheory.ChartLieFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenBasisNearBoundaryFlagSpacePoint
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
open scoped Matrix
attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LogPole.EigNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}


set_option maxHeartbeats 1000000 in
open GlobalTheory.LogKSDiv.Spread GlobalTheory.ShFam.EigSpread GlobalTheory.ShFam.EigLoc GlobalTheory.LieLocBasis in
theorem exists_eigBasis_at (TF : TorFlag Xo c) (p : TF.Y.X) :
    ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
      (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), p ∈ U.1 ∧ IsEigBasis TF U e v := by
  classical
  obtain ⟨U₁, hU₁, hp₁, x₁, hx₁, C, n, xc, hx⟩ := exists_affine_chart TF.Y.t (𝟙 TF.Y.X) p
  let L : Type := TF.Y.X.presheaf.stalk p
  letI : Algebra Γ(TF.Y.X, U₁) L := TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨p, hp₁⟩
  have hloc := hU₁.isLocalization_stalk ⟨p, hp₁⟩
  let ρ₁ : Γ(TF.Y.X, U₁) →+* L := algebraMap _ _
  have hK : spMap ρ₁ ≫ hU₁.fromSpec = TF.Y.X.fromSpecStalk p := by
    rw [← hU₁.fromSpecStalk_eq_fromSpecStalk hp₁]
    rfl
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [hid]; infer_instance
  haveI : IsIso (GlobalTheory.Toroidal.genι TF.Y) := inferInstanceAs (IsIso (pullback.fst TF.Y.s (spMap (RingHom.id c.F))))
  have hs : inv (GlobalTheory.Toroidal.genι TF.Y) ≫ GlobalTheory.Toroidal.genStr TF.Y = TF.Y.s := by
    rw [IsIso.inv_comp_eq]
    calc GlobalTheory.Toroidal.genStr TF.Y = GlobalTheory.Toroidal.genStr TF.Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = GlobalTheory.Toroidal.genι TF.Y ≫ TF.Y.s := pullback.condition.symm
  let φ₀ : c.F →+* L := (Spec.preimage (TF.Y.X.fromSpecStalk p ≫ TF.Y.s)).hom
  have hφ₀ : spMap φ₀ = TF.Y.X.fromSpecStalk p ≫ TF.Y.s := Spec.map_preimage _
  obtain ⟨f₀'⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c c.F (RingHom.id c.F) TF.Y L φ₀
    (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) (by rw [Category.assoc, hs, hφ₀])
  have e0 : (TF.Y.X.fromSpecStalk p ≫ inv (GlobalTheory.Toroidal.genι TF.Y)) ≫ GlobalTheory.Toroidal.genι TF.Y =
      TF.Y.X.fromSpecStalk p := by simp
  obtain ⟨f₀⟩ : Nonempty (GlobalTheory.ShFam.EigFrame TF.Y φ₀ (TF.Y.X.fromSpecStalk p)) := e0 ▸ ⟨f₀'⟩
  let φ₁ := cst TF.Y.s U₁
  have hφ₁ : spMap φ₁ = hU₁.fromSpec ≫ TF.Y.s := spMap_cst _ hU₁
  have hρφ : ρ₁.comp φ₁ = φ₀ := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hK, hφ₀])
  have vec_bc_of_chart {S : Type} [CommRing S] {x : Sp S ⟶ TF.Y.X} {n : ℕ}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj TF.Y.t.G}
      (C : ReciprocityTheory.ChartRestriction.G.Chart.Chart ((Over.pullback x).obj TF.Y.t.G))
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc)
      {S' : Type} [CommRing S'] (ψ : S →+* S') {x' : Sp S' ⟶ TF.Y.X} (h : x' = spMap ψ ≫ x) :
      ∃ (xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶ (Over.pullback x').obj TF.Y.t.G),
        ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc' ∧
        ∀ cc : Fin n → S, vec TF.Y.t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec TF.Y.t x xc cc := by
    subst h
    letI : Algebra S S' := ψ.toAlgebra
    obtain ⟨x₁, hx₁, hcomp⟩ := LieChart.univChart_baseChange_of_chart (R := S) (R' := S') _ C n xc hx
    have h₁ := IsGrpPullback.comp
      (isGrpPullback_pullback ((Over.pullback x).obj TF.Y.t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
      (isGrpPullback_pullback TF.Y.t.G x)
    obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
      (isGrpPullback_pullback TF.Y.t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
    refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
    have key : (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
        (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
      show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
      rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
    show (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
    rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
    rfl
  obtain ⟨xcK, hxK, hcK⟩ := vec_bc_of_chart C hx ρ₁ (x' := TF.Y.X.fromSpecStalk p)
    (by rw [hx₁, Category.comp_id, hK])
  have exists_projectors (c : Coeff l) {L : Type} [CommRing L] (φ : c.F →+* L) {x : Sp L ⟶ TF.Y.X} {n : ℕ}
      {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (ReciprocityTheory.ChartRestriction.G.Chart.JetR L (Fin n) m) ⟶ (Over.pullback x).obj TF.Y.t.G}
      (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc) :
      ∃ P : (E →+* ℂ) → Matrix (Fin n) (Fin n) L, ∀ {k : Type} [CommRing k] (ψ : L →+* k) {x' : Sp k ⟶ TF.Y.X}
        {xc' : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := k) (ReciprocityTheory.ChartRestriction.G.Chart.JetR k (Fin n) m) ⟶ (Over.pullback x').obj TF.Y.t.G}
        (hx' : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart _ n xc'), (∀ cc : Fin n → L, vec TF.Y.t x' xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec TF.Y.t x xc cc) → ∀ τ v, (P τ).map ψ *ᵥ v ∈ eig c (ψ.comp φ) hx' τ ∧
          (v ∈ eig c (ψ.comp φ) hx' τ → (P τ).map ψ *ᵥ v = v) := by
    classical
    have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
      ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    letI : Algebra c.F L := φ.toAlgebra
    refine ⟨fun τ => LinearMap.toMatrix' (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx) (embK c) α τ), fun {k} _ ψ {x' xc'} hx' hv τ => ?_⟩
    letI : Algebra c.F k := (ψ.comp φ).toAlgebra
    have e₁ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx') (embK c) α τ m) := fun m =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m)
    have e₂ : ∀ m, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hx') (embK c τ) m → ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx') (embK c) α τ m = m := fun m hm => by
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig (rho hx') (embK c) α hinj (Pi.single τ m) (fun τ' => by
        by_cases h : τ' = τ
        · subst h; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h]; intro a; simp) τ
      rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_same] at this
    have htm : ∀ (a : 𝓞 E) (cc : Fin n → L), rho hx' a (ψ ∘ cc) = ψ ∘ rho hx a cc :=
      fun a cc => vec_inj hx' (by
        show vec TF.Y.t _ xc' (ReciprocityTheory.ChartRestriction.G.Chart.tmap hx' _ _) = vec TF.Y.t _ xc' (_ ∘ ReciprocityTheory.ChartRestriction.G.Chart.tmap hx _ _)
        rw [vec_tmap hx', hv, hv, vec_tmap hx, Category.assoc])
    have pw : ∀ (j : ℕ) cc, (rho hx' α ^ j) (ψ ∘ cc) = ψ ∘ (rho hx α ^ j) cc := fun j => by
      induction j with
      | zero => exact fun _ => rfl
      | succ j ih => intro cc; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]; exact htm α _
    have pr : ∀ (Q : Polynomial c.F) cc, Polynomial.aeval (rho hx' α) (Q.map (algebraMap c.F k)) (ψ ∘ cc) =
        ψ ∘ Polynomial.aeval (rho hx α) (Q.map (algebraMap c.F L)) cc := fun Q cc => by
      induction Q using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [Polynomial.map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
        funext j; simp
      | monomial j a =>
        rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
          Module.End.mul_apply, Module.End.mul_apply, pw, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
        funext i
        exact (map_mul ψ _ _).symm
    have hP : (LinearMap.toMatrix' (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx) (embK c) α τ)).map ψ =
        LinearMap.toMatrix' (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj (rho hx') (embK c) α τ) := by
      ext i j
      have s : (Pi.single j 1 : Fin n → k) = ψ ∘ Pi.single j 1 := funext fun r => by
        by_cases hj : r = j <;> simp [hj, Pi.single_apply]
      rw [Matrix.map_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, s]
      exact (congrFun (pr _ _) i).symm
    intro v
    rw [hP, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff,
      ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    exact ⟨e₁ v, e₂ v⟩

  obtain ⟨Pr, hPr⟩ := exists_projectors c φ₁ hx
  choose Bv hBv using fun τ i => vec_exists hxK _ (f₀.tan τ i)
  have hBe : ∀ τ i, Bv τ i ∈ eig c φ₀ hxK τ := fun τ i => (vec_eig_iff hxK _ _).1 (by rw [← hBv]; exact f₀.eig τ i)
  have hPK : ∀ τ i, (Pr τ).map ρ₁ *ᵥ Bv τ i = Bv τ i := fun τ i =>
    (hPr ρ₁ hxK hcK τ (Bv τ i)).2 (by rw [hρφ]; exact hBe τ i)
  letI : Algebra c.F L := φ₀.toAlgebra
  have hEig : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c z.1) (Bv z.1 z.2) :=
    fun z => (ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).1 (hBe z.1 z.2)
  have hblk : ∀ τ w, ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (rho hxK) (embK c τ) w →
      ∃! a : Fin (Dw.mult τ) → L, ∑ i, a i • Bv τ i = w := fun τ w hw => by
    have := f₀.basis τ _ (vec_tan hxK w) ((vec_eig_iff hxK _ w).2 ((ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff _ _ _ _).2 hw))
    rw [show f₀.v τ = fun i => vec TF.Y.t _ xcK (Bv τ i) from funext (hBv τ)] at this
    simpa only [comb_iff hxK, eq_comm] using this
  have hglob := GlobalTheory.FlagEmb.EigSpread.global_basis (GlobalTheory.FlagEmb.EigSpread.splits c) (fun z => Bv z.1 z.2) hEig hblk
  obtain ⟨hli, hsp⟩ := (GlobalTheory.FlagEmb.EigSpread.existsUnique_iff _).1 hglob
  let bK := Module.Basis.mk hli hsp.ge
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hdet : IsUnit (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i).det := by
    have h1 : (Matrix.of fun i j => Bv (e.symm j).1 (e.symm j).2 i) =
        (Pi.basisFun L (Fin n)).toMatrix (bK.reindex e) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, bK]
    rw [h1]
    exact Matrix.isUnit_det_of_right_inverse (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  obtain ⟨g, hg, s0, B₀, -, hψB⟩ := spread_exact (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal
    (fun j => Bv (e.symm j).1 (e.symm j).2) hdet (fun j => Pr (e.symm j).1) (fun j => hPK _ _)
  have hU : IsAffineOpen (TF.Y.X.basicOpen g) := hU₁.basicOpen g
  have hU' : TF.Y.X.basicOpen g ∈ TF.Y.X.affineOpens := hU
  have hpU : p ∈ TF.Y.X.basicOpen g := by
    rw [Scheme.mem_basicOpen _ _ _ hp₁]
    exact IsLocalization.map_units L (⟨g, hg⟩ : (hU₁.primeIdealOf ⟨p, hp₁⟩).asIdeal.primeCompl)
  let ψ : Γ(TF.Y.X, U₁) →+* Γ(TF.Y.X, TF.Y.X.basicOpen g) :=
    (TF.Y.X.presheaf.map (homOfLE (TF.Y.X.basicOpen_le g)).op).hom
  have hψg : IsUnit (ψ g) := TF.Y.X.toRingedSpace.isUnit_res_basicOpen g
  obtain ⟨hs0, hdet0, hQ0⟩ := hψB _ ψ hψg
  have hmap : spMap ψ ≫ hU₁.fromSpec = hU.fromSpec := hU₁.map_fromSpec hU _
  obtain ⟨xcU, hxU, hcU⟩ := vec_bc_of_chart C hx ψ (x' := LogKS.chart ⟨_, hU'⟩)
    (by rw [hx₁, Category.comp_id]; exact hmap.symm)
  have hψφ : ψ.comp φ₁ = cst TF.Y.s (TF.Y.X.basicOpen g) := spMap_inj (by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, hφ₁, ← Category.assoc, hmap, spMap_cst _ hU])
  let u := hs0.unit
  let cU : Fin n → Fin n → Γ(TF.Y.X, TF.Y.X.basicOpen g) := fun j => (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j)
  have hdetU : IsUnit (Matrix.of fun i j => cU j i).det := by
    have : (Matrix.of fun i j => cU j i) = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • Matrix.of fun i j => ψ (B₀ j i) := by
      ext i j; rfl
    rw [this, Matrix.det_smul]
    exact (u⁻¹.isUnit.pow _).mul hdet0
  have hcUd : ∀ j, cU j = (↑u⁻¹ : Γ(TF.Y.X, TF.Y.X.basicOpen g)) • (ψ ∘ B₀ j) := fun j => rfl
  clear_value cU
  refine ⟨⟨_, hU'⟩, n, e, fun j => vec TF.Y.t _ xcU (cU j), hpU, fun j => vec_tan hxU _, fun w' hw' => ?_,
    fun a τ i => ?_⟩
  · obtain ⟨cc, rfl⟩ := vec_exists hxU w' hw'
    simp only [comb_iff hxU]
    exact basis_of_det cU hdetU cc
  · have hq := hQ0 (e ⟨τ, i⟩)
    simp only [Equiv.symm_apply_apply] at hq
    have hfix : (Pr τ).map ψ *ᵥ cU (e ⟨τ, i⟩) = cU (e ⟨τ, i⟩) := by
      rw [hcUd, Matrix.mulVec_smul, hq]
    have hmem := (hPr ψ hxU hcU τ (cU (e ⟨τ, i⟩))).1
    rw [hfix, hψφ] at hmem
    have heig : vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) ≫ (TF.Y.t.act.act a).left =
        spMap (epsMul (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a))) ≫
          vec TF.Y.t (LogKS.chart ⟨_, hU'⟩) xcU (cU (e ⟨τ, i⟩)) :=
      (vec_eig_iff hxU (fun a => cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)) (cU (e ⟨τ, i⟩))).2 hmem a
    have hc : IsCombAtG TF.Y.t (LogKS.chart ⟨_, hU'⟩) (fun j => vec TF.Y.t _ xcU (cU j))
        (Pi.single (e ⟨τ, i⟩) (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a)))
        (vec TF.Y.t _ xcU (cst TF.Y.s (TF.Y.X.basicOpen g) (embK c τ a) • cU (e ⟨τ, i⟩))) := by
      rw [comb_iff hxU, Finset.sum_eq_single (e ⟨τ, i⟩) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
        (fun hk => absurd (Finset.mem_univ _) hk), Pi.single_eq_same]
    rw [vec_smul hxU, ← heig] at hc
    exact hc

end GlobalTheory.LogPole.EigNear

theorem GlobalTheory.LogPole.exists_eigBasis_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ y : Y₀ TF.X Z, ∃ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), toBase TF Z y ∈ U.1 ∧ IsEigBasis TF U e v := by
  intro E _ _ _ H Dw l Xo c TF Z _ y
  exact GlobalTheory.LogPole.EigNear.exists_eigBasis_at TF (toBase TF Z y)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftMonoOfFpqcCoverLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem exists_lift_of_fpqc_cover : ∀ (G T T' Y : Scheme.{0}) (π : G ⟶ Y) [Mono π] (y : T ⟶ Y) (t : T' ⟶ T)
    [Flat t] [Surjective t] [QuasiCompact t] (z : T' ⟶ G), z ≫ π = t ≫ y → ∃ w : T ⟶ G, w ≫ π = y := by
  intro G T T' Y π _ y t _ _ _ z hz
  let s := pullback.snd π y
  let σ : T' ⟶ pullback s t :=
    pullback.lift (pullback.lift z t hz) (𝟙 T') (by rw [Category.id_comp]; exact pullback.lift_snd _ _ _)
  have hσ : σ ≫ pullback.snd s t = 𝟙 T' := pullback.lift_snd _ _ _
  haveI : IsSplitEpi (pullback.snd s t) := ⟨⟨⟨σ, hσ⟩⟩⟩
  haveI : IsIso (pullback.snd s t) := isIso_of_mono_of_isSplitEpi _
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  have hs : IsIso s :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq (MorphismProperty.isomorphisms.infer_property _)
  refine ⟨inv s ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionValueAbelianPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.SecValLin
open GlobalTheory.SecJet.Orders

theorem valR_add' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valR x U (f + g) = valR x U f + valR x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, valR_eq x U h, map_add (f := _)]
  · simp only [valR, dif_neg h, add_zero]

theorem valR_scal_mul {R A : Type} [CommRing R] [CommRing A] {X : Scheme.{0}} (ψ : R →+* A) (p : X ⟶ Sp R)
    (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ) (U : X.Opens) (c : R) (f : Γ(X, U)) :
    valR x U (resTop U (scal p c) * f) = ψ c * valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valR_eq x U h, valR_eq x U h, map_mul]
    have e : resTop U (scal p c) = Geo.Tor.constFn p U c := rfl
    rw [e, vh_const ψ p x hx U h c]
  · simp only [valR, dif_neg h, mul_zero]

theorem exists_linear_valR_sec : ∀ (K : Type) [Field K] (x : KeyIn K) (N : ℕ) (i : Fin 1 → x.P.L.ι) (B : Type) [CommRing B] [Algebra K B]
    (y : Sp B ⟶ (baseOver (Sp K) ⊗ x.P.A).left),
    y ≫ (fst (baseOver (Sp K)) x.P.A).left = spMap (algebraMap K B) →
    ∃ f : EA x.P (𝟙 (Sp K)) N →ₗ[K] B, ∀ s : EA x.P (𝟙 (Sp K)) N,
      f s = valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i) := by
  intro K _ x N i B _ _ y hy
  refine ⟨⟨⟨fun s => valR y ((LPow x.P.A x.P.L ((N : ℕ) : ℤ) (baseOver (Sp K))).U i) (s.sec.f i),
    fun s t => valR_add' y _ _ _⟩, fun c s => ?_⟩, fun s => rfl⟩
  show valR y _ (resTop _ (scal _ c) * s.sec.f i) = _
  rw [valR_scal_mul (algebraMap K B) _ y hy, RingHom.id_apply, Algebra.smul_def]

end GlobalTheory.SecValLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogVectorFieldExtendFunctionFieldDerivatioStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logVectorField_extend_functionFieldDerivation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ {N : ℕ} (Dl : Fin N → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), ∃ D : Fin N → GlobalTheory.LogKSDiv.GenDer TF Z, letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((Dl j).1 r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_genDer_extend | exact GlobalTheory.LogKSDiv.exists_genDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_genDer_extend <;> assumption)
end

