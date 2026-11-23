module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCover
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.HorFrame

def combDer {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) : R →+* DualNumber R where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (∑ i, A i * (δ i s).snd)
  map_one' := by
    have h : ∀ i, (δ i 1).snd = 0 := fun i => by rw [map_one]; rfl
    ext <;> simp [h]
  map_mul' x y := by
    have h : ∀ i, (δ i (x * y)).snd = x * (δ i y).snd + (δ i x).snd * y := fun i => by
      rw [map_mul, TrivSqZeroExt.snd_mul, hδ, hδ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, h, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    have h : ∀ i, (δ i 0).snd = 0 := fun i => by rw [map_zero]; rfl
    ext <;> simp [h]
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, mul_add]

theorem combDer_fst {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) : (combDer δ hδ A s).fst = s := by
  simp [combDer]

theorem combDer_snd {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) :
    (combDer δ hδ A s).snd = ∑ i, A i * (δ i s).snd := by
  simp [combDer]

theorem fst_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).fst = φ x.fst := by simp [dualMap]

theorem snd_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).snd = φ x.snd := by simp [dualMap]

end GlobalTheory.HorFrame


open GlobalTheory.HorFrame in
theorem GlobalTheory.HorFrame.exists_horizontal_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS k W hW p hp
  haveI := c.fin
  obtain ⟨W₁, hW₁, d, hpW₁, hW₁W, hd, hspan⟩ := GlobalTheory.T.exists_affine_cover_with_dual_number_derivations M W p hp
  have hoff : W₁ ≤ M.off := fun x hx => (hW (hW₁W hx)).1
  have hτ : ⊤ ≤ tau hW₁ ⁻¹ᵁ W₁ := tau_le hW₁ le_rfl
  have hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ => (hW (hW₁W (hτ (Set.mem_univ s)))).2
  have hF₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
    have := hoff (hτ (Set.mem_univ s))
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg₁, hch⟩ := GlobalTheory.CompHS.exists_chartFr (tau hW₁ ≫ toFlag M) hF₁
  obtain ⟨Q₀, hQ₀⟩ := hch k hk₁
  have hdalg : ∀ b, (d b).comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber Γ(M.X, W₁)) :=
    fun b => RingHom.ext fun a => TrivSqZeroExt.ext
      (by rw [RingHom.comp_apply, hd]; rfl) (by
      rw [_root_.GlobalTheory.ringHom_dualNumber_snd_eq_zero c.F ((d b).comp (algebraMap c.F _)) a]; rfl)
  have hx1 : ∀ b, (spMap (d b) ≫ Q₀.x) ≫ Xo.s = sOf c (DualNumber Γ(M.X, W₁)) := fun b => by
    rw [Category.assoc, Q₀.x_over]
    unfold sOf
    rw [spMap_comp', ← RingHom.comp_assoc, hdalg]
  have hx2 : ∀ b, spMap (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom ≫ spMap (d b) ≫ Q₀.x
      = Q₀.x := fun b => by
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom.comp (d b) = RingHom.id _ :=
      RingHom.ext fun s => hd b s
    rw [this]
    exact (congrArg (· ≫ Q₀.x) (Spec.map_id _)).trans (Category.id_comp _)
  choose Mx hMx using fun b => _root_.GlobalTheory.KSFam.ksFamily hP Q₀ (spMap (d b) ≫ Q₀.x) (hx1 b) (hx2 b)
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.HorFrame.exists_basicOpen_det_ks M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx p hpW₁
  set MxM : Matrix (Fin (dimFlag Dw)) (HIx Dw (psiSet H)) Γ(M.X, W₁) := Matrix.of (fun a h => Mx a h) with hMxM
  set g : Γ(M.X, W₁) := (B * MxM).det with hg
  have hW' : IsAffineOpen (M.X.basicOpen g) := hW₁.basicOpen g
  have hW'W₁ : M.X.basicOpen g ≤ W₁ := M.X.basicOpen_le g
  haveI := hW₁.isLocalization_basicOpen g
  set ρ := algebraMap Γ(M.X, W₁) Γ(M.X, M.X.basicOpen g) with hρ
  choose d' hd'1 hd'2 using fun b => _root_.GlobalTheory.dualNumber_deformation_extends_away (S' := Γ(M.X, M.X.basicOpen g)) g (d b) (hd b)
  have hunit : IsUnit ((B * MxM).map ρ).det := by
    have : ((B * MxM).map ρ).det = ρ (B * MxM).det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit g
  set A := ((B * MxM).map ρ)⁻¹ * B.map ρ with hA
  have hAM : A * MxM.map ρ = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hunit]
  have hτ' : spMap ρ ≫ tau hW₁ = tau hW' := by
    have e1 := spMap_ev (tau hW') hW₁ (tau_le hW' hW'W₁)
    have e2 : ev (tau hW') W₁ (tau_le hW' hW'W₁) = ρ := RingHom.ext fun a => ev_tau hW' hW'W₁ _ a
    rw [← e2]
    exact e1
  refine ⟨M.X.basicOpen g, hW', fun b => combDer d' hd'1 (fun a => A b a), hB, hW'W₁.trans hW₁W,
    fun b s => combDer_fst _ _ _ _, ?_⟩
  intro K _ _ ψ hk Q hQ b
  have ez : (spMap ψ ≫ tau hW') ≫ toFlag M = (spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M := by
    rw [← hτ', ← spMap_comp' ρ ψ]
    simp only [Category.assoc]
  have hk' : ⊤ ≤ ((spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := ez ▸ hk
  have hQ' : X.F.ChartFr k _ hk' Q :=
    hQ.frMap (frMap_refl Q) ((spMap_algId _).trans ez) hk'
  obtain ⟨w, hwD, hwKS, hwpt⟩ := _root_.GlobalTheory.HorFrame.exists_deform_of_comb M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K (ψ.comp ρ) hk' Q hQ'
    ((dualMap ψ).comp ((combDer d' hd'1 (fun a => A b a)).comp ρ)) (fun a => ψ (A b a))
    (fun s => by rw [RingHom.comp_apply, fst_dualMap, RingHom.comp_apply, combDer_fst]; rfl)
    (fun s => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.comp_apply, snd_dualMap, RingHom.comp_apply, combDer_snd, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hd'2]
      rfl)
  refine ⟨w, hwD, ?_, ?_⟩
  · have key : ∀ h, ∑ a, ψ (A b a) * ψ (ρ (Mx a h)) = (Pi.single b (1 : K) : HIx Dw (psiSet H) → K) h := fun h => by
      have e := congrArg (fun N => ψ (N b h)) hAM
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.map_apply, hMxM, Matrix.of_apply, map_sum, map_mul] at e
      rw [e, Matrix.one_apply, Pi.single_apply]
      by_cases hh : h = b
      · subst hh; simp
      · simp [hh, Ne.symm hh]
    convert hwKS using 1
    funext h
    rw [Finset.sum_apply, ← key h]
    rfl
  · rw [← hwpt, ← hτ']
    simp only [← Category.assoc, spMap_comp']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPow
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.HodgePow

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CechPic

theorem lbIso_hodge_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B)
    (he : η[A] ≫ e.hom = η[B]) (r : ℕ) (hA : IsVB (omega A) r) :
    IsVB (omega B) r ∧ LBIso (GlobalTheory.SiegelTor.hodge A r) (GlobalTheory.SiegelTor.hodge B r) := by
  have he' : η[B] ≫ e.inv = η[A] := by rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  let φ : omega A ≅ omega B :=
    { hom := cotMap e.inv he'
      inv := cotMap e.hom he
      hom_inv_id := (cotMap_comp he' he e.hom_inv_id (Category.comp_id _)).trans (cotMap_id rfl _)
      inv_hom_id := (cotMap_comp he he' e.inv_hom_id (Category.comp_id _)).trans (cotMap_id rfl _) }
  exact ⟨hA.of_iso φ, hA.lbIso_det_of_iso φ⟩

def prodUnitIso {S : Scheme.{0}} (G : Over S) : G ⊗ 𝟙_ (Over S) ≅ G where
  hom := fst _ _
  inv := lift (𝟙 G) (toUnit G)
  hom_inv_id := by ext1 <;> simp <;> exact toUnit_unique _ _
  inv_hom_id := by simp

section Pow

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [QuasiSeparated G.hom] (g : ℕ)

theorem cls_hodge_powObj [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
    (hs : SmoothOfRelativeDimension g G.hom) (hG : IsVB (omega G) g) (n : ℕ) :
    ∃ h : IsVB (omega (powObj G (n + 1))) ((n + 1) * g),
      cls _ h.isLB_det = (n + 1) • cls _ hG.isLB_det := by
  have hV : ∀ m, IsVB (omega (powObj G m)) (m * g) := fun m => by
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G m).2.1
    haveI := smoothOfRelativeDimension_powObj G g hs m
    exact isVB_omega _ _
  refine ⟨hV (n + 1), ?_⟩
  induction n with
  | zero =>
    have hE : η[G ⊗ 𝟙_ (Over S)] ≫ (prodUnitIso G).hom = η[G] := by simp [prodUnitIso]
    have h1 := hV 1
    rw [Nat.one_mul] at h1
    have := (lbIso_hodge_of_iso (prodUnitIso G) hE g h1).2
    rw [Nat.zero_add, one_smul]
    have hh : ∀ (r : ℕ) (hr : r = 1 * g) (h₁ : IsVB (omega (powObj G 1)) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det := by
      intro r hr h₁
      rw [Nat.one_mul] at hr
      subst hr
      exact (cls_eq_iff _ _).2 this
    exact hh _ rfl (hV 1)
  | succ n ih =>
    haveI := (GlobalFunctionsDvrGeneric.powObj_props G (n + 1)).2.1
    have key := GlobalTheory.HodgeProd.lbIso_det_conormal_prod G (powObj G (n + 1)) g ((n + 1) * g) hG (hV (n + 1))
      η[G ⊗ powObj G (n + 1)] (by ext1 <;> simp)
    have hT := isLB_tens hG.isLB_det (hV (n + 1)).isLB_det
    have hh : ∀ (r : ℕ) (hr : r = g + (n + 1) * g) (h₁ : IsVB (omega (powObj G (n + 1 + 1))) r),
        cls _ h₁.isLB_det = cls _ hG.isLB_det + cls _ (hV (n + 1)).isLB_det := by
      intro r hr h₁
      subst hr
      rw [← cls_tens _ _ hT]
      exact (cls_eq_iff _ _).2 key
    rw [hh _ (by ring) (hV _), ih, succ_nsmul' _ (n + 1)]

theorem one_powPr {n : ℕ} (i : Fin n) : η[powObj G n] ≫ powPr G i = η[G] := by
  haveI := powPr.isMonHom G i
  exact IsMonHom.one_hom _

end Pow

theorem hodge_eight_mul_iso_hodge_pow_eight : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)),
    (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) →
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  intro S G H _ _ g pr hpr hU hG hs
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : SmoothOfRelativeDimension g G.hom := hs
  have hVG : IsVB (omega G) g := isVB_omega G g
  obtain ⟨hP, hc⟩ := cls_hodge_powObj G g hs hVG 7
  let lim : IsLimit (Fan.mk H pr) := mkFanLimit _ (fun s => (hU s.pt s.proj).exists.choose)
    (fun s i => (hU s.pt s.proj).exists.choose_spec i)
    (fun s m hm => (hU s.pt s.proj).unique hm (hU s.pt s.proj).exists.choose_spec)
  let e : H ≅ powObj G 8 := lim.conePointUniqueUpToIso (powIsLimit G 8)
  have he : ∀ i, e.hom ≫ powPr G i = pr i := fun i =>
    lim.conePointUniqueUpToIso_hom_comp (powIsLimit G 8) ⟨i⟩
  have hη : η[powObj G 8] ≫ e.inv = η[H] := by
    refine lim.hom_ext fun ⟨i⟩ => ?_
    have h1 : e.inv ≫ pr i = powPr G i := by rw [← he, Iso.inv_hom_id_assoc]
    haveI := hpr i
    simp only [Fan.mk_π_app, Category.assoc, h1]
    exact (one_powPr G i).trans (IsMonHom.one_hom (pr i)).symm
  obtain ⟨hH, hiso⟩ := lbIso_hodge_of_iso e.symm hη (8 * g) hP
  have hL := hVG.isLB_det
  refine (cls_eq_iff hH.isLB_det (isLB_lbPow hL 8)).1 ?_
  rw [cls_lbPow hL, ← (cls_eq_iff hP.isLB_det hH.isLB_det).2 hiso]
  exact hc

end GlobalTheory.HodgePow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateGluedSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem eq_ptMap' {O : Type} [CommRing O] {D B : Type} [CommRing D] [Algebra O D] [CommRing B] [Algebra O B]
    (x : specO O D ⟶ specO O B) : ∃ α : B →ₐ[O] D, x = ptMap α := by
  obtain ⟨f, hf⟩ := Spec.map_surjective x.left
  have hw : x.left ≫ (specO O B).hom = (specO O D).hom := Over.w x
  rw [← hf] at hw
  change Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap O B)) = Spec.map (CommRingCat.ofHom (algebraMap O D)) at hw
  rw [← Spec.map_comp] at hw
  have hc := Spec.map_injective hw
  refine ⟨{ f.hom with commutes' := fun c => congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of D => g.hom c) hc }, ?_⟩
  ext1
  rw [← hf]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapPowEqOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem aH_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π), aH P' x0 hu hg.1 ^ q = 1 := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg
  have hinj : Function.Injective (pushHom hg (Hs P' x0 hu)) := by
    intro x y hxy
    apply Over.OverMorphism.ext
    apply hg.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · rw [Over.w x, Over.w y]
  have hw : (pushHom hg (Hs P' x0 hu) (aH P' x0 hu hg.1)) ^ q = 1 :=
    GlobalTheory.HTMap.tors_of (g := spMap (inB P' x0 hu)) (w := P'.u) (aH_left_π P' x0 hu hg.1) P'.fin.tors
  apply hinj
  rw [map_pow, hw, map_one]

end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFinite
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem hs_isFinite (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O)
    (hu : IsUnit (x0 P'.f)) : IsFinite (Hs P' x0 hu).hom := by
  haveI : Module.Finite (Localization.Away P'.f) P'.B := P'.fin.finite
  haveI : Module.Finite (OL P' x0 hu) (Bt P' x0 hu) := Module.Finite.base_change _ _ _
  haveI : Module.Finite O (OL P' x0 hu) := inferInstanceAs (Module.Finite O O)
  haveI : Module.Finite O (Bt P' x0 hu) := Module.Finite.trans (OL P' x0 hu) (Bt P' x0 hu)
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [IsFinite.SpecMap_iff]
  rw [CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFlat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem flat_Bt : Module.Flat O (Bt P' x0 hu) := by
  haveI : Module.Free (Localization.Away P'.f) P'.B := P'.fin.free
  haveI : Module.Flat (OL P' x0 hu) (Bt P' x0 hu) := Module.Flat.baseChange _ _ _
  haveI : Module.Flat O (OL P' x0 hu) := inferInstanceAs (Module.Flat O O)
  exact Module.Flat.trans O (OL P' x0 hu) (Bt P' x0 hu)

theorem flat_Hs : Flat (Hs P' x0 hu).hom := by
  haveI := flat_Bt P' x0 hu
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff).2 inferInstance

end GlobalTheory.FinPartAt

theorem GlobalTheory.FinPartAt.flat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), Flat (Hs P' x0 hu).hom := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu
  exact GlobalTheory.FinPartAt.flat_Hs P' x0 hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFramePartialSumDiffNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicFrame_partialSum_diff_ne_zero : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y : Fin g → ℂ) (j : thK → D.P.L.ι) (I : thK), DifferentiableOn ℂ (fun z => geo.frG (j I) (wI x y z I)) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ ∀ z, ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → geo.frG (j I) (wI x y z I) ≠ 0 := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne | exact GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne | (intros; apply GlobalTheory.MBLow.Cl.CubHol.frG_wI_hol_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InhabitedAndRefines
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg
variable {R : Type} [CommRing R] [IsDomain R]

def ofDeg (D : DegPre R) (hB : D.TauBimult) : Data R := Wit.ofDeg D hB

theorem refines_ofDeg (D : DegPre R) (hB : D.TauBimult) :
    Refines (ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) :=
  Wit.refines_ofDeg D hB


end GlobalTheory.PolDeg
end
end

