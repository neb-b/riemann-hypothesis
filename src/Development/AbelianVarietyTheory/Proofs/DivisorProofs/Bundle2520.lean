module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCoeffAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVInterior
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.KS
open TrivSqZeroExt (inl inr)

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K]

theorem exists_isTransl_snd {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {u : epsR K ⟶ A} (hu : IsTangent u)
    {dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hd : IsInvDer u dd) {S : Type} [CommRing S]
    (ψ : K →+* S) (x : Sp S ⟶ A.left) (hx : x ≫ A.hom = spMap ψ) :
    ∃ w, GlobalTheory.CechKS.IsTransl ψ x u w ∧ ∀ (O : A.left.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O) (f : Γ(A.left, O)),
      (valR w O f).snd = GlobalTheory.TangentOrigin.evalPt x O h (dd O f) := by
  letI : Algebra K (DualNumber S) := ((algebraMap S (DualNumber S)).comp ψ).toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) (DualNumber S) ⟶ A :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ x) (by
      rw [Category.assoc, hx]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl)
  let v' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) (DualNumber S) ⟶ A :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (DualNumber.eps : DualNumber S) (by simp)) ≫ u
  have hv' : v'.left = spMap (dualMap ψ) ≫ u.left := by
    show Spec.map _ ≫ u.left = _
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    ext <;> simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, dualMap, Algebra.ofId_apply,
      RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨(v' * z).left, ⟨z, v', rfl, hv', by rw [mul_comm]⟩, fun O h f => ?_⟩
  have hz : ⊤ ≤ z.left ⁻¹ᵁ O := fun p _ => h (Set.mem_univ _)
  obtain ⟨h', H⟩ := GlobalTheory.InvFieldBasis.evalPt_translate hu hd (DualNumber.eps : DualNumber S) (by simp) z O hz
  have e1 : valR (v' * z).left O f = GlobalTheory.TangentOrigin.evalPt (v' * z).left O h' f := by
    rw [valR, dite_eq_left h']; rfl
  have e2 : ∀ s, GlobalTheory.TangentOrigin.evalPt z.left O hz s = inl (GlobalTheory.TangentOrigin.evalPt x O h s) := fun s =>
    GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap S (DualNumber S)) x O h hz s
  rw [e1, H, e2, e2]
  simp

theorem exists_polAV_interior {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (x0 : Sp K ⟶ Y.X)
    (hx : ⊤ ≤ x0 ⁻¹ᵁ GlobalTheory.LogKS.interior Y) :
    ∃ (P₀ : Out.PolAV (Sp K)) (θ : P₀.A.left ⟶ Y.t.G.left), IsGrpPullback P₀.A Y.t.G x0 θ ∧
      LBIso P₀.L (Y.t.PP.L.pull θ) := by
  have hr : Set.range x0 ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    exact hx (Set.mem_univ p)
  let y' := IsOpenImmersion.lift Y.j x0 hr
  have hy' : y' ≫ Y.j = x0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨P, φ, -, hφ, hL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Y.oF.t Y.oF.proper Y.oF.ample
    Y.oF.ktriv K y'
  have g1 : IsGrpPullback P.A Y.t.G (y' ≫ Y.j) (φ ≫ Y.m.φ) := hφ.comp Y.m.cart
  rw [hy'] at g1
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have i1 : LBIso (Y.oF.t.PP.L.pull φ) (Y.t.PP.L.pull (φ ≫ Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ φ φ rfl)
      (chartPullSame _ (fun _ => φ ≫ Y.m.φ) (fun _ => Y.m.φ) (fun _ => 1) φ (fun _ => rfl)) ⟨w, hw⟩
  exact ⟨P, φ ≫ Y.m.φ, g1, LBIso.trans P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL i1⟩

theorem valR_eq_evalPt {S : Type} [CommRing S] {Z : Scheme.{0}} (x : Sp S ⟶ Z) (O : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (s : Γ(Z, O)) : valR x O s = GlobalTheory.TangentOrigin.evalPt x O h s := by
  rw [valR, dite_eq_left h]; rfl

theorem eq_of_evalPt_eq {Z : Scheme.{0}} {O : Z.Opens} (s s' : Γ(Z, O))
    (h : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ O),
      GlobalTheory.TangentOrigin.evalPt x O hx s = GlobalTheory.TangentOrigin.evalPt x O hx s') : s = s' := by
  let J : Type := {V : Z.Opens // IsAffineOpen V ∧ V ≤ O}
  refine eq_of_rsT_eq (fun V : J => V.1) (fun V => V.2.2) (fun p hp => ?_) s s' fun V => ?_
  · obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp O.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hpV⟩
  obtain ⟨t, ht, et⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq V.2.1 (RingHom.id _)
  have ht' : ⊤ ≤ t ⁻¹ᵁ O := fun p hp => V.2.2 (ht hp)
  have e : ∀ a : Γ(Z, O), rsT a V.1 = GlobalTheory.TangentOrigin.evalPt t O ht' a := fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_res t V.2.2 ht' ht, et, rsT_of_le V.2.2]; rfl
  rw [e, e, h _ t ht']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

theorem pull_diff (t : SAB H X) (V : X.Opens) (U : X.affineOpens) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a))
    (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) {J : Type} (W : J → t.G.left.Opens) (j : J → t.PP.L.ι)
    (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hWj : ∀ i, W i ≤ t.PP.L.U (j i))
    (hdiff : ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O))
      (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left)
      (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)),
      g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, GlobalTheory.LogKS.IsTranslate t φ g₀ (v a) (w a)) →
      valR g₀ O (d i O f - d i' O f) =
        ∑ a, ∑ b, φ (Θ a b) *
          ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) *
          (valR (w a) O f).snd)
    (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ t.G.left)
    (hm : IsGrpPullback A t.G x0 m) (u : Fin n → (epsR K ⟶ A))
    (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (GlobalTheory.FlagMod.ev x0 U.1 hU)) ≫ v a)
    (dd : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => m ⁻¹ᵁ t.PP.L.U i)) (hφ : IsDlog m t.PP.L dd φ)
    (i i' : J) (O : t.G.left.Opens) (hO : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)) :
    (m.app O).hom (d i O f - d i' O f) =
      ∑ a, (∑ b, constFn A.hom _ (GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b)) * rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) *
        dd a _ ((m.app O).hom f) := by
  have hut : ∀ a, IsTangent (u a) := GlobalTheory.CechKS.isTangent_of_fibre t U v hv x0 hU A m u hm hu
  have hOg : O ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := fun p hp => ⟨hWj i (hO hp).1, hWj i' (hO hp).2⟩
  have hOg' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i') := m.preimage_mono hOg
  refine eq_of_evalPt_eq _ _ fun S _ x hx => ?_
  let ψ : K →+* S := (Spec.preimage (x ≫ A.hom)).hom
  have hxA : x ≫ A.hom = spMap ψ := (Spec.map_preimage (x ≫ A.hom)).symm
  choose w hw hw' using fun a => exists_isTransl_snd (hut a) (hdd a) ψ x hxA
  have hbase : (x ≫ m) ≫ t.G.hom = spMap (ψ.comp (GlobalTheory.FlagMod.ev x0 U.1 hU)) ≫ GlobalTheory.LogKS.chart U := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hxA, GlobalTheory.Cris.spMap_comp (GlobalTheory.FlagMod.ev x0 U.1 hU), Category.assoc]
    exact congrArg _ (GlobalTheory.FlagMod.spMap_ev x0 U.2 hU).symm
  have key := hdiff i i' O hO f S (ψ.comp (GlobalTheory.FlagMod.ev x0 U.1 hU)) (x ≫ m) (fun a => w a ≫ m) hbase hx
    (fun a => GlobalTheory.CechKS.IsTransl.isTranslate_comp t x0 A m hm _ (v a) (u a) (hu a) ψ x hxA (w a) (hw a))
  have hxg : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i')) := fun p hp => hOg' (hx hp)
  have ev_g : ∀ b, (valR (w b ≫ m) _ (t.PP.L.g (j i) (j i')).val).snd *
      valR (x ≫ m) _ (t.PP.L.g (j i) (j i'))⁻¹.val =
      GlobalTheory.TangentOrigin.evalPt x (m ⁻¹ᵁ O) hx (rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) := fun b => by
    have hp : ∀ (s : Γ(t.G.left, t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))),
        pbT m s (m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i')) = (m.app _).hom s := fun s => by
      show pbT m s (m ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))) = _
      rw [pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
    have hxg' : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))) := hxg
    have e1 : GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val) *
        GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i')) =
        GlobalTheory.TangentOrigin.evalPt x _ hxg (dd b _ ((m.app _).hom (t.PP.L.g (j i) (j i')).val)) := by
      have := congrArg (GlobalTheory.TangentOrigin.evalPt x _ hxg) (hφ b (j i) (j i'))
      rw [map_mul, hp] at this
      exact this
    have h0 : (m.app _).hom (t.PP.L.g (j i) (j i')).val * (m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val) *
        GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) = 1 :=
      calc _ = GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val *
              (m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) := (map_mul _ _ _).symm
        _ = 1 := by rw [h0]; exact map_one _
    have e3 : GlobalTheory.TangentOrigin.evalPt x (m ⁻¹ᵁ O) hx (rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) =
        GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i')) := by
      rw [rsT_of_le hOg', GlobalTheory.TangentOrigin.evalPt_res x hOg' hxg hx]
    rw [GlobalTheory.CechKS.valR_comp_app, GlobalTheory.CechKS.valR_comp_app, hw' b _ hxg', valR_eq_evalPt _ _ hxg', e3]
    show GlobalTheory.TangentOrigin.evalPt x _ hxg (dd b _ ((m.app _).hom (t.PP.L.g (j i) (j i')).val)) *
      GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) = _
    rw [← e1]
    linear_combination (GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i'))) * e2
  rw [GlobalTheory.CechKS.valR_comp_app, valR_eq_evalPt _ _ hx] at key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ev_g, GlobalTheory.CechKS.valR_comp_app (w a) m O f, hw' a _ hx, map_mul, GlobalTheory.TangentOrigin.evalPt_constFn,
    GlobalTheory.InvFieldBasis.evalPt_congr hxA ⊤ le_rfl le_rfl, GlobalTheory.TangentOrigin.evalPt_spMap]
  rfl

theorem coeff_id {A₀ : Over (Sp K)} [GrpObj A₀] {g : ℕ} {v : Fin g → (epsR K ⟶ A₀)}
    {dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)} (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) {S : Scheme.{0}} (x₀ : Sp K ⟶ S) {X : Scheme.{0}} (p : X ⟶ S)
    (m : A₀.left ⟶ X) (H : IsPullback m A₀.hom p x₀) {U : S.Opens} (hU : IsAffineOpen U)
    (W₀ : X.Opens) (hW₀ : W₀ ≤ p ⁻¹ᵁ U) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W))
    (hadd : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f')
    (hmul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f)
    (hrs : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W'))
    (hbase : ∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X), y ≫ m = m' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)),
      (∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f') →
      (∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m'.app W).hom f * d W f' + (m'.app W).hom f' * d W f) →
      (∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m' ⁻¹ᵁ W')) →
      (∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' e d h1 h2 h3 h4
    subst e
    exact existsUnique_coeff hs hv hd x₀ p m H hU y W₀ hW₀ d h1 h2 h3 h4
  have := key (𝟙 _) m (Category.id_comp _) d hadd hmul hrs hbase
  simpa only [GlobalTheory.KS.LinDir.pbT_id] using this

theorem app_resG {Y Z : Scheme.{0}} (m : Y ⟶ Z) {W W' : Z.Opens} (h : W' ≤ W) (s : Γ(Z, W)) :
    (m.app W').hom (resG Z h s) = rsT ((m.app W).hom s) (m ⁻¹ᵁ W') := by
  have e : ∀ {O : Z.Opens} (s : Γ(Z, O)), (m.app O).hom s = pbT m s (m ⁻¹ᵁ O) := fun s => by
    rw [pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
  rw [e, e, ← rsT_of_le h, pbT_rsT m h le_rfl, rsT_pbT m le_rfl (m.preimage_mono h)]

theorem field_base {X Z : Scheme.{0}} (π : Z ⟶ X) {U : X.Opens} (W₀ : Z.Opens) (hW₀ : W₀ ≤ π ⁻¹ᵁ U)
    (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hf : GlobalTheory.LogKS.IsField W₀ d) (D : Γ(X, U) → Γ(X, U))
    (hl : ∀ (h : W₀ ≤ π ⁻¹ᵁ U) (r : Γ(X, U)), d W₀ ((π.appLE U W₀ h).hom r) = (π.appLE U W₀ h).hom (D r)) :
    ∀ W, W ≤ W₀ → ∀ r, d W (pbT π r W) = pbT π (D r) W := by
  intro W hW r
  have e : ∀ s : Γ(X, U), pbT π s W = resG Z hW (pbT π s W₀) := fun s => by
    rw [← rsT_of_le hW, rsT_pbT π hW₀ hW]
  rw [e, e, hf.2.2 W₀ W hW le_rfl, pbT_of_le π hW₀, pbT_of_le π hW₀, hl hW₀]

theorem isCoc_lc {Y : Scheme.{0}} {I : Type} {Uc : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ} (c : Fin g → K)
    (φ : Fin g → C1 Uc) (h : ∀ a, IsCoc Uc (φ a)) : IsCoc Uc (lc q c φ) := by
  intro i j k
  simp only [lc, rsT_sum, rsT_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_constFn q (O₀ := Uc i ⊓ Uc j) inf_le_left,
    rsT_constFn q (O₀ := Uc j ⊓ Uc k) (O := Uc i ⊓ Uc j ⊓ Uc k) (fun _ h => ⟨h.1.2, h.2⟩),
    rsT_constFn q (O₀ := Uc i ⊓ Uc k) (O := Uc i ⊓ Uc j ⊓ Uc k) (fun _ h => ⟨h.1.1, h.2⟩), ← mul_add, h a i j k]

theorem constFn_sub {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (x y : K) :
    constFn q O (x - y) = constFn q O x - constFn q O y := by
  simp [constFn]

end GlobalTheory.KSUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinGlue
open GlobalTheory.SiegelDescent GlobalTheory.SiegDesc GlobalTheory.CechPic

theorem lem_ab : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := _root_.GlobalTheory.GlueAb.main

theorem lem_lb : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := _root_.GlobalTheory.ArtinPatch.exists_lb_glue

theorem lem_triv : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := _root_.GlobalTheory.ArtinPicGlue.pic_eq_zero_of_pull_eq_zero

theorem lem_pt : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := GlobalTheory.T.fibreProduct_spec_fieldPoint_factors

theorem lem_princ : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := _root_.GlobalTheory.ArtinPrinc.principal_of_pull

theorem geom_transfer {S S' : Scheme.{0}} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B} {h M : ℕ}
    (c : SiegPre h M ζ s') (A₀ : Over S) [GrpObj A₀] [IsCommMonObj A₀] (f : S' ⟶ S) (φ : c.A.left ⟶ A₀.left)
    (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A₀)) (hs : s' = f ≫ s)
    (hp : IsGrpPullback c.A A₀ f φ) (hP₀ : P₀.IsLB)
    (diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ))
    (hlev : ∀ a, (c.lev a).left ≫ φ = f ≫ (lev₀ a).left) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (y : Sp k ⟶ S') (hy : y ≫ f = x) (β : B →+* k) (z : kˣ) (hx : x ≫ s = spMap β)
    (hz : (z : k) = β ζ) :
    (∀ a, (toUnit (Over.mk x) ≫ lev₀ a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A₀, g ^ M = 1 → ∃ a, toUnit _ ≫ lev₀ a = g) ∧
    ∀ a b, Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) M (toUnit (Over.mk x) ≫ lev₀ a) (toUnit _ ≫ lev₀ b)
      (unitOn (z ^ (2 * omegaStd a b))) := by
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ f := hp.1.w
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ c.A f φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

theorem spec_isPushout (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (hP : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P) (s₁ : Function.Surjective g₁)
    (s₂ : Function.Surjective g₂) : IsPushout (Spec.map g₁) (Spec.map g₂) (Spec.map f₁) (Spec.map f₂) := by
  have w : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hP.w]
  exact _root_.GlobalTheory.FlatPinch.main P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hl ha s₁ s₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
    (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂) (show Flat (𝟙 (Spec P)) from inferInstance) (IsPullback.id_vert _)
    (IsPullback.id_vert _) (IsPullback.id_vert _) w (by simp)

theorem nontrivial_of_pt (R : CommRingCat.{0}) (k : Type) [Field k] (y : Spec (CommRingCat.of k) ⟶ Spec R) :
    Nontrivial R := by
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y.base pt⟩

theorem exists_principal_glue : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ β c₁ c₂ hp₁ hp₂ hc₀
  obtain ⟨c₀, ⟨ψ₁, ψ₁₂, hψ₁, sψ₁, iψ₁, lψ₁⟩, ⟨ψ₂, ψ₂₂, hψ₂, sψ₂, iψ₂, lψ₂⟩⟩ := hc₀
  obtain ⟨A, instA, φ₁, φ₂, hA, hφ₁, hφ₂, hcomm⟩ :=
    lem_ab P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ c₁.A c₂.A c₀.A ψ₁ ψ₂ c₁.ab c₂.ab hψ₁ hψ₂
  haveI := hA.comm
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨φ₁₂, sφ₁⟩ := exists_isSquare hφ₁.1.w
  obtain ⟨φ₂₂, sφ₂⟩ := exists_isSquare hφ₂.1.w
  obtain ⟨χ₂, sχ⟩ := exists_isSquare (f := Spec.map g₁ ≫ Spec.map f₁) (φ := ψ₁ ≫ φ₁)
    (by rw [Category.assoc, hφ₁.1.w]; exact (reassoc_of% hψ₁.1.w) _)
  have e₁₂ : ψ₁₂ ≫ φ₁₂ = χ₂ := isSquare_comp rfl sψ₁ sφ₁ sχ
  have e₂₂ : ψ₂₂ ≫ φ₂₂ = χ₂ := isSquare_comp hcomm.symm sψ₂ sφ₂ sχ
  have flat : Flat (G2 A).hom := by
    haveI := hAA.smooth
    infer_instance
  have hiso₀ : LBIso (c₁.P.pull ψ₁₂) (c₂.P.pull ψ₂₂) :=
    LBIso.trans (pull_isLB c₁.isLB _) c₀.isLB (pull_isLB c₂.isLB _) iψ₁.symm iψ₂
  obtain ⟨L, hL, w₁, w₂⟩ := lem_lb P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (G2 A) (G2 c₁.A) (G2 c₂.A)
    (G2 c₀.A) φ₁₂ φ₂₂ ψ₁₂ ψ₂₂ flat (isPullback_of_isSquare hφ₁.1 sφ₁) (isPullback_of_isSquare hφ₂.1 sφ₂)
    (isPullback_of_isSquare hψ₁.1 sψ₁) (e₁₂.trans e₂₂.symm) (isSquare_w hψ₂.1.w sψ₂) c₁.P c₂.P c₁.isLB c₂.isLB
    hiso₀
  have clsP₁ : cls c₁.P c₁.isLB = pull φ₁₂ (cls L hL) := by
    rw [← cls_pull hL φ₁₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₁
  have clsP₂ : cls c₂.P c₂.isLB = pull φ₂₂ (cls L hL) := by
    rw [← cls_pull hL φ₂₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₂
  have rig : ∀ (a₁ : c₁.A ⟶ c₁.A ⊗ c₁.A) (a₂ : c₂.A ⟶ c₂.A ⊗ c₂.A) (a : A ⟶ A ⊗ A),
      a₁.left ≫ φ₁₂ = φ₁ ≫ a.left → a₂.left ≫ φ₂₂ = φ₂ ≫ a.left →
      (∃ t : (c₁.P.pull a₁.left).Gen, t.IsGen) → (∃ t : (c₂.P.pull a₂.left).Gen, t.IsGen) →
      ∃ t : (L.pull a.left).Gen, t.IsGen := by
    intro a₁ a₂ a e₁ e₂ t₁ t₂
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL _ (pull_isLB hL _)]
    refine lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A c₁.A c₂.A φ₁ φ₂ hA hφ₁.1 hφ₂.1 _ ?_ ?_
    · rw [← pull_comp, ← e₁, pull_comp, ← clsP₁, ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _)]
      exact (cls_eq_zero_iff _).2 t₁
    · rw [← pull_comp, ← e₂, pull_comp, ← clsP₂, ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _)]
      exact (cls_eq_zero_iff _).2 t₂
  have one₁ := one_comp hφ₁ c₁.A A φ₁ hφ₁.1.w
  have one₂ := one_comp hφ₂ c₂.A A φ₂ hφ₂.1.w
  have idφ₁ : (𝟙 c₁.A : c₁.A ⟶ c₁.A).left ≫ φ₁ = φ₁ ≫ (𝟙 A : A ⟶ A).left := by simp
  have idφ₂ : (𝟙 c₂.A : c₂.A ⟶ c₂.A).left ≫ φ₂ = φ₂ ≫ (𝟙 A : A ⟶ A).left := by simp
  have symm : LBIso L (L.pull (lift (snd A A) (fst A A)).left) := by
    have sw₁ := lift_square sφ₁ sφ₁.2.symm sφ₁.1.symm
    have sw₂ := lift_square sφ₂ sφ₂.2.symm sφ₂.1.symm
    refine (cls_eq_iff hL (pull_isLB hL _)).1 (sub_eq_zero.1 (lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
      (G2 A) (G2 c₁.A) (G2 c₂.A) φ₁₂ φ₂₂ hAA (isPullback_of_isSquare hφ₁.1 sφ₁)
      (isPullback_of_isSquare hφ₂.1 sφ₂) _ ?_ ?_))
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₁, pull_comp, ← clsP₁,
        ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₁.symm
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₂, pull_comp, ← clsP₂,
        ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₂.symm

  have hpo := spec_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
  have levc : ∀ a, Spec.map g₁ ≫ (c₁.lev a).left ≫ φ₁ = Spec.map g₂ ≫ (c₂.lev a).left ≫ φ₂ := fun a => by
    simp only [← Category.assoc]
    rw [← lψ₁ a, ← lψ₂ a, Category.assoc, Category.assoc, hcomm]
  have sec : ∀ {X : Scheme.{0}} {Bv : Over X} (u : 𝟙_ (Over X) ⟶ Bv), u.left ≫ Bv.hom = 𝟙 X := fun u => by
    simpa using Over.w u
  have hlev : ∀ a, ∃ l : 𝟙_ (Over (Spec P)) ⟶ A, Spec.map f₁ ≫ l.left = (c₁.lev a).left ≫ φ₁ ∧
      Spec.map f₂ ≫ l.left = (c₂.lev a).left ≫ φ₂ := fun a =>
    ⟨Over.homMk (hpo.desc _ _ (levc a)) (by
      refine hpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hpo.inl_desc, Category.assoc, hφ₁.1.w, ← Category.assoc, sec]
        simp
      · rw [← Category.assoc, hpo.inr_desc, Category.assoc, hφ₂.1.w, ← Category.assoc, sec]
        simp), hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  choose lev hl₁ hl₂ using hlev
  obtain ⟨ρ₁, hρ₁⟩ := exists_liftHom hφ₁ (𝟙_ _) (𝟙_ _) (Spec.map f₁)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ρ₂, hρ₂⟩ := exists_liftHom hφ₂ (𝟙_ _) (𝟙_ _) (Spec.map f₂)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρl₁ : ∀ a, ρ₁ (lev a) = c₁.lev a := fun a => (hρ₁ _ _).2 (hl₁ a).symm
  have ρl₂ : ∀ a, ρ₂ (lev a) = c₂.lev a := fun a => (hρ₂ _ _).2 (hl₂ a).symm
  have inj : ∀ x y : 𝟙_ (Over (Spec P)) ⟶ A, ρ₁ x = ρ₁ y → ρ₂ x = ρ₂ y → x = y := fun x y e₁ e₂ =>
    Over.OverMorphism.ext (hpo.hom_ext
      (by rw [← (hρ₁ x _).1 rfl, ← (hρ₁ y _).1 rfl, e₁])
      (by rw [← (hρ₂ x _).1 rfl, ← (hρ₂ y _).1 rfl, e₂]))
  have diag₁ : LBIso (c₁.P.pull (lift (𝟙 c₁.A) (𝟙 c₁.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₁) :=
    lbIso_square c₁.isLB hL w₁ (lift_square sφ₁ idφ₁ idφ₁)
  have diag₂ : LBIso (c₂.P.pull (lift (𝟙 c₂.A) (𝟙 c₂.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₂) :=
    lbIso_square c₂.isLB hL w₂ (lift_square sφ₂ idφ₂ idφ₂)
  let c : SiegPre g n (zetaAway n) (Spec.map β) :=
    { A := A, ab := hA, P := L, isLB := hL
      rig₁ := rig _ _ _ (lift_square sφ₁ one₁ idφ₁) (lift_square sφ₂ one₂ idφ₂) c₁.rig₁ c₂.rig₁
      rig₂ := rig _ _ _ (lift_square sφ₁ idφ₁ one₁) (lift_square sφ₂ idφ₂ one₂) c₁.rig₂ c₂.rig₂
      symm := symm, lev := lev
      lev_add := fun a b => inj _ _ (by rw [map_mul, ρl₁, ρl₁, ρl₁, c₁.lev_add])
        (by rw [map_mul, ρl₂, ρl₂, ρl₂, c₂.lev_add])
      lev_tors := fun a => inj _ _ (by rw [map_pow, ρl₁, c₁.lev_tors, map_one])
        (by rw [map_pow, ρl₂, c₂.lev_tors, map_one])
      geom := by
        intro k _ _ x β' z hx hz
        rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ k x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact geom_transfer c₁ A (Spec.map f₁) φ₁ L lev rfl hφ₁ hL diag₁ (fun a => (hl₁ a).symm) k x y hy β' z hx hz
        · exact geom_transfer c₂ A (Spec.map f₂) φ₂ L lev rfl hφ₂ hL diag₂ (fun a => (hl₂ a).symm) k x y hy β' z hx hz }
  have pb₁ : SiegPB c₁ c (Spec.map f₁) := ⟨φ₁, φ₁₂, hφ₁, sφ₁, w₁, fun a => (hl₁ a).symm⟩
  have pb₂ : SiegPB c₂ c (Spec.map f₂) := ⟨φ₂, φ₂₂, hφ₂, sφ₂, w₂, fun a => (hl₂ a).symm⟩
  refine ⟨c, ?_, pb₁, pb₂⟩
  rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ (IsLocalRing.ResidueField P)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue P))) with ⟨y, -⟩ | ⟨y, -⟩
  · haveI := nontrivial_of_pt R₁ _ y
    exact lem_princ g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ inferInstance β c c₁ pb₁ hp₁
  · haveI := nontrivial_of_pt R₂ _ y
    exact lem_princ g n hn hodd P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hs₂ hs₁ inferInstance β c c₂ pb₂ hp₂

end GlobalTheory.ArtinGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.CrdMapBC

open GlobalTheory.ProjSpace GlobalTheory.Cartier GlobalTheory.QCoh.Qcqs

theorem secMaps_baseChangeIso {o k : Type} [CommRing o] [CommRing k] (β : o →+* k) (n : ℕ) (j : Fin (n + 1)) :
    SecMaps (baseChangeIso n β) (secPull (coord o n j) (baseChange n β)) (coord k n j) := by
  rintro ⟨i, l⟩
  refine (baseChangeIso_coord n β j i l).trans ?_
  congr 1

theorem pCrd_comp_baseChange {o k A : Type} [CommRing o] [CommRing k] [CommRing A] (β : o →+* k) {n : ℕ}
    (x : Sp A ⟶ PSpace k n) (v : Fin (n + 1) → A) (h : PCrd x v) : PCrd (x ≫ baseChange n β) v := by
  refine (RepBC.secCoord_pull (O1 o n) (coord o n) (baseChange n β) x v).1 ?_
  exact (FibreEmbed.secCoord_iff_of_secMaps (LB.isLB_pull (O1_isLB o n) _) (O1_isLB k n)
    (w := baseChangeIso n β) (fun j => secMaps_baseChangeIso β n j)
    (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord o n) _) (iSup_nonzeroLocus_coord k n)).2 h

theorem exists_map_of_hasDiv : ∀ (k Ω o : Type) [CommRing k] [Field Ω] [Algebra k Ω] [CommRing o] (β : o →+* k) (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace o n, h ≫ PSpace.str o n = M.s ≫ spMap β ∧ PCrd (M.pt ≫ h) c := by
  intro k Ω o _ _ _ _ β M n c hc
  obtain ⟨h₀, hs, hp⟩ := _root_.GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv k Ω M n c hc
  refine ⟨h₀ ≫ baseChange n β, ?_, ?_⟩
  · rw [Category.assoc, baseChange_str, ← Category.assoc, hs]
  · rw [← Category.assoc]
    exact pCrd_comp_baseChange β _ c hp

end GlobalTheory.SiegTh.CrdMapBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_element_of_local_field_point_values : ∀ (R : Type) [CommRing R] (P : (K : Type) → [Field K] → (R →+* K) → K → Prop), (∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v) → (∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K), P K (j.comp (algebraMap R (Localization.Away f))) (j c)) → ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  first | exact @GlobalTheory.glue_field_points | exact GlobalTheory.glue_field_points | (intros; apply GlobalTheory.glue_field_points <;> assumption)
end

