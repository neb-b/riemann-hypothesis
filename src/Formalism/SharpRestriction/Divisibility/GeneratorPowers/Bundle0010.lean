module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PrimUniqPf

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrSt
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartPrimTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (wPT : PrimTyG I.G),
    IsPrimG I.G wPT →
    letI := io.toAlgebra
    ∃ wP : PrimTy H Xo, IsPrim wP ∧
      ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
        (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
          LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
        ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
          LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
          LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.DescentPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

section Jet

variable {k : Type} [CommRing k] {n : ℕ}

end Jet

section Lin

variable {k : Type} [CommRing k] {n : ℕ}

theorem DpolyN_sub {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ e ∈ S, MvPowerSeries.C (P.coeff e) * DmonN F cp u e g := by
  unfold DpolyN
  refine Finset.sum_subset hS (fun e _ he => ?_)
  have h0 : P.coeff e = 0 := by simpa using he
  rw [h0, map_zero, zero_mul]

theorem DpolyN_addP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (P Q : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [DpolyN_sub F cp u (P + Q) g (P.support ∪ Q.support) MvPolynomial.support_add,
    DpolyN_sub F cp u P g (P.support ∪ Q.support) Finset.subset_union_left,
    DpolyN_sub F cp u Q g (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem DpolyN_smulP {ι : Type} [Fintype ι] (F : Fin d → PS k 2 d) (cp : ι → Fin n) (u : ι → Fin d → k)
    (c : k) (P : MvPolynomial ι k) (g : PS k n d) :
    DpolyN F cp u (c • P) g = c • DpolyN F cp u P g := by
  rw [DpolyN_sub F cp u (c • P) g P.support MvPolynomial.support_smul,
    DpolyN_sub F cp u P g P.support subset_rfl, Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, mul_assoc, ← MvPowerSeries.smul_eq_C_mul]

end Lin

theorem nabValN_addP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (P Q : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (P + Q) = nabValN B k h w0 m f cp u P + nabValN B k h w0 m f cp u Q := by
  unfold nabValN
  rw [DpolyN_addP, map_add (f := _)]

theorem nabValN_smulP (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O)
    (m : ℕ) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (c : k) (P : MvPolynomial ι k)
    (f : PS k n d) :
    nabValN B k h w0 m f cp u (c • P) = c * nabValN B k h w0 m f cp u P := by
  unfold nabValN
  rw [DpolyN_smulP, MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

end Gen

section Asm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

end Asm

section Main

open ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1.DescentPf
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem isChartG_reindex (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left))
    (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (h : IsChartG t x0 d F act tg uvec x) (e : κ' ≃ κ) :
    IsChartG t x0 d F act (fun ℓ => tg (e ℓ)) (fun ℓ => uvec (e ℓ)) x := by
  refine ⟨h.zero, h.trunc, h.law, h.act, fun ℓ => h.tan (e ℓ), ?_⟩
  intro v
  obtain ⟨b, hb, hbu⟩ := h.basis v
  refine ⟨fun ℓ => b (e ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [← hb j]
    exact Equiv.sum_comp e (fun ℓ => b ℓ * uvec ℓ j)
  · have h1 : (fun ℓ => a (e.symm ℓ)) = b := hbu _ fun j => by
      rw [← ha j, ← Equiv.sum_comp e (fun ℓ => a (e.symm ℓ) * uvec ℓ j)]
      simp only [Equiv.symm_apply_apply]
    funext ℓ
    rw [← h1]
    simp only [Equiv.symm_apply_apply]

variable {V : Type} [CommRing V] (t : SAB H (Sp V))

theorem combAt_iff {n : ℕ} {x} (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart t.G n x) {m : ℕ}
    (f : Fin m → (Sp (DualNumber V) ⟶ t.G.left)) (hf : ∀ i, f i ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hft : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t (f i) (hf i))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    IsCombAtG t (𝟙 (Sp V)) f a w ↔ ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw),
      ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ h = ∑ i, a i • ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ (hft i) := by
  constructor
  · intro hc
    have e := prodPts_of_combAt (t := t) f hf a w hw hc
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    have hT : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw) := by rw [e]; exact h
    exact ⟨hT, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e hT h).trans hh⟩
  · rintro ⟨h, hh⟩
    apply combAt_of_prodPts (t := t) f hf a w hw
    obtain ⟨h', hh'⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    exact ReciprocityTheory.ChartRestriction.G.Chart.tan_ext hx h h' (hh.trans hh'.symm)

theorem dir_tan {d : ℕ} (xc : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (hz : ∀ m, homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xc m = 1) (j : Fin d)
    (ho : (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫
      xc 1).left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t _ ho) := by
  apply chartTan_of
  refine ⟨ho.trans (Category.comp_id _).symm, ?_⟩
  have h1 := congrArg CommaMorphism.left (hz 1)
  simp only [Over.comp_left] at h1 ⊢
  have h2 : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫
      (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V)).left =
      (homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V)).left := by
    show spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg (fun φ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V => φ.toRingHom) (fst_comp_jetTan ((0 : Fin 1), j))
  rw [← Category.assoc, h2, h1]
  have hobj : spMap (algebraMap V V) ≫ 𝟙 (Sp V) = 𝟙 (Sp V) := by
    rw [Category.comp_id]
    first
      | (rw [Algebra.algebraMap_self]; exact Spec.map_id _)
      | simp [spMap]
  have h3 : ∀ (f g : Sp V ⟶ Sp V), f = g →
      (1 : Over.mk f ⟶ t.G).left = (1 : Over.mk g ⟶ t.G).left := by
    rintro f g rfl; rfl
  exact h3 _ _ hobj

end Lemmas

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

theorem res_top_mul {U V : Y.Opens} (hV : V ≤ U) (a : Γ(Y, ⊤)ˣ) (x : Γ(Y, U)ˣ) :
    res hV (res le_top a * x) = res le_top a * res hV x := by
  rw [map_mul, DVR.res_res']

theorem pull_top_res (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]

theorem scaleGenG_one (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε 1 g = g := by
  cases g
  simp only [scaleGenG, map_one, one_mul]

theorem pullGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen t.PP.L φ ε (scaleGenG t φ ε v g) h =
      scaleGenG t (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen t.PP.L φ ε g h) := by
  unfold LB.pullGen scaleGenG
  congr 1
  funext j
  erw [map_mul, map_mul, pull_top_res]

theorem mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl

theorem invGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.invGen t.PP.L φ ε (scaleGenG t φ ε v g) = scaleGenG t φ _ v⁻¹ (LB.invGen t.PP.L φ ε g) := by
  unfold LB.invGen scaleGenG
  congr 1
  funext j
  erw [map_inv, mul_inv_rev, mul_comm]
  rfl

theorem corr_scaleGenG {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') (v : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v g') := by
  intro j j' hj hj' hm
  have e := hc j j' hj hj' hm
  unfold scaleGenG
  dsimp only
  erw [res_top_mul, res_top_mul, e]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem unitΓ_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (u : Aˣ) :
    Units.map (Formalism.L2.Pj.homAt x0 f).left.appTop.hom.toMonoidHom (unitΓ u) = unitΓ (Units.map f.toMonoidHom u) := by
  ext
  simp only [unitΓ, toΓ, Formalism.L2.Pj.homAt, Over.homMk_left, spMap, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupCopies
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

variable {R : Type} [CommRing R] {d n : ℕ}

theorem dofN_mul_left (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (A B : PS R n d)
    (hA : ∀ j, pderiv (R := R) (b, j) A = 0) : DofN F b u (A * B) = A * DofN F b u B := by
  unfold DofN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Derivation.leibniz, hA j, smul_zero, add_zero, smul_eq_mul]
  ring

section Fold

variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem dmon_zero (g : PS R n d) : DmonN F cp u 0 g = g := by
  simp [DmonN]

theorem dpoly_sup (P : MvPolynomial ι R) (T : Finset (ι →₀ ℕ)) (hT : P.support ⊆ T)
    (g : PS R n d) : DpolyN F cp u P g = ∑ mm ∈ T, C (P.coeff mm) * DmonN F cp u mm g := by
  unfold DpolyN
  apply Finset.sum_subset hT
  intro mm _ hmm
  have h0 : P.coeff mm = 0 := by simpa [MvPolynomial.mem_support_iff] using hmm
  rw [h0, map_zero, zero_mul]

theorem dpoly_add (P Q : MvPolynomial ι R) (g : PS R n d) :
    DpolyN F cp u (P + Q) g = DpolyN F cp u P g + DpolyN F cp u Q g := by
  classical
  rw [dpoly_sup F cp u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    dpoly_sup F cp u P (P.support ∪ Q.support) Finset.subset_union_left,
    dpoly_sup F cp u Q (P.support ∪ Q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mm _ => ?_)
  rw [MvPolynomial.coeff_add, map_add (f := _), add_mul]

theorem dpoly_monomial (mm : ι →₀ ℕ) (a : R) (g : PS R n d) :
    DpolyN F cp u (MvPolynomial.monomial mm a) g = C a * DmonN F cp u mm g := by
  classical
  rw [dpoly_sup F cp u _ {mm} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def dpolyHom (g : PS R n d) : MvPolynomial ι R →+ PS R n d where
  toFun P := DpolyN F cp u P g
  map_zero' := by simp [DpolyN]
  map_add' P Q := dpoly_add F cp u P Q g

end Fold

end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField TopologicalSpace Opposite MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def BetaUniqSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (a : 𝓞 E) (β β' : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε)),
    β.IsGen → β'.IsGen →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ β' (eSec Xo.univ.t.G))
      (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) →
    β = β'

namespace GaugeBeta

theorem pull_unit_eq_one_k {X Y S0 : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : S0 ⟶ Y) (ψ : S0 ⟶ X) (k : ℤ)
    (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => k))
    (t t' : LB.Gen (LB.LinComb L φ ε)) (u : Γ(Y, ⊤)ˣ)
    (hu : ∀ j, t.s j = res (le_top : (LB.LinComb L φ ε).U j ≤ ⊤) u * t'.s j)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t h) rig)
    (hc' : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' h) rig) :
    (h.app ⊤).hom (u : Γ(Y, ⊤)) = 1 := by

  let rig1 : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1) := ⟨rig.s⟩
  exact pull_unit_eq_one L hL φ ε h ψ rig1 t t' u hu hc hc'

end GaugeBeta

theorem betaUniq_of_global (hglob : GlobalFnsSt) : BetaUniqSt := by
  intro E _ _ _ H Dw l Xo a β β' hβ hβ' hc hc'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  obtain ⟨u, hu⟩ := gen_ratio _ (wchart_cover Xo.univ.t.PP.L hL _) β β' hβ hβ'
  have h1 := GaugeBeta.pull_unit_eq_one_k Xo.univ.t.PP.L hL _ _ (eSec Xo.univ.t.G)
    (eSec Xo.univ.t.G) (-3) (rigPow Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (-3)) β β' u hu hc hc'
  have hu1 : u = 1 := by
    obtain ⟨v, hv⟩ := (hglob _ Xo.univ.t.G (isAbelianScheme_univ Xo)).2 (u : Γ(Xo.univ.t.G.left, ⊤))
    have hw : eSec Xo.univ.t.G ≫ Xo.univ.t.G.hom = 𝟙 _ := by
      unfold eSec
      exact Over.w _
    have e1 : (Scheme.Hom.app (eSec Xo.univ.t.G) ⊤).hom
        ((Scheme.Hom.appTop Xo.univ.t.G.hom).hom v) = v := by
      have := congrArg (fun f => (Scheme.Hom.appTop f).hom v) hw
      simp at this
      exact this
    rw [hv] at e1
    have hv1 : v = 1 := e1.symm.trans h1
    apply Units.ext
    rw [← hv, hv1, map_one]
    rfl
  cases β
  cases β'
  congr 1
  funext j
  have hj := hu j
  rw [hu1, map_one, one_mul] at hj
  exact hj

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

