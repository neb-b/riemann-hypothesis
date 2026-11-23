module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntAfIntCast
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.MultScale

variable {p : ℕ} [Fact p.Prime]

def EFA (D : Datum p) : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (D.EF.baseChange ℚ).baseChange (AfP p)

theorem EFA_tmul (D : Datum p) (a a' : AfP p) (x x' : D.La) :
    EFA D (a ⊗ₜ ((1 : ℚ) ⊗ₜ x)) (a' ⊗ₜ ((1 : ℚ) ⊗ₜ x')) = a * a' * ((D.EF x x' : ℤ) : AfP p) := by
  simp only [EFA, LinearMap.BilinForm.baseChange_tmul, _root_.mul_one]
  rw [Algebra.smul_def, zsmul_eq_mul, _root_.mul_one, map_intCast, mul_comm]

theorem EFA_inAf (D : Datum p) (x y : D.La) : EFA D (inAf D x) (inAf D y) = ((D.EF x y : ℤ) : AfP p) := by
  rw [inAf, inAf, EFA_tmul, _root_.one_mul, _root_.one_mul]

theorem isIntAf_intCast (z : ℤ) : IsIntAf ((z : AfP p)) := fun v => by
  rw [map_intCast]; exact intCast_mem _ z

theorem isIntAf_add {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isIntAf_neg {a : AfP p} (ha : IsIntAf a) : IsIntAf (-a) := fun v => by
  rw [map_neg]; exact neg_mem (ha v)

theorem isIntAf_mul {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isIntAf_zero : IsIntAf (0 : AfP p) := by simpa using isIntAf_intCast (p := p) 0

theorem isIntAf_EFA (D : Datum p) {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) :
    IsIntAf (EFA D v w) := by
  induction hv using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨a, x, ha, rfl⟩ := hv
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a', x', ha', rfl⟩ := hw
      rw [EFA_tmul]; exact isIntAf_mul (isIntAf_mul ha ha') (isIntAf_intCast _)
    | zero => simpa using isIntAf_zero
    | add u u' _ _ h h' => rw [map_add (f := _)]; exact isIntAf_add h h'
    | neg u _ h => rw [map_neg]; exact isIntAf_neg h
  | zero => simpa using isIntAf_zero
  | add u u' _ _ h h' => rw [map_add (f := _), LinearMap.add_apply]; exact isIntAf_add h h'
  | neg u _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

section Sim

variable {D : Datum p} {G : HTGroup p}

theorem bc_adj {V : Type} [AddCommGroup V] [Module ℚ V] (A : Type) [CommRing A] [Algebra ℚ A]
    (B : LinearMap.BilinForm ℚ V) (f g : Module.End ℚ V) (h : ∀ v w, B (f v) w = B v (g w)) (v w : A ⊗[ℚ] V) :
    B.baseChange A (f.baseChange A v) w = B.baseChange A v (g.baseChange A w) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v v' hv hv' => simp only [map_add (f := _), LinearMap.add_apply, hv, hv']
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
    | tmul a' y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]

theorem actOn_tmul {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (c : C) :
    actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
  rw [Algebra.smul_def]
  first
  | exact Algebra.TensorProduct.lift_tmul _ _ _ r c
  | (erw [Algebra.TensorProduct.lift_tmul]; rfl)
  | rfl

theorem EFA_actOn (L : Link D G) (X : AfP p ⊗[ℚ] G.C) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (actOn L.rep (AfP p) X v) w = EFA D v (actOn L.rep (AfP p) (starT G.star (AfP p) X).unop w) := by
  induction X using TensorProduct.induction_on with
  | zero => simp
  | add X X' hX hX' => simp only [map_add (f := _), MulOpposite.unop_add, LinearMap.add_apply, hX, hX']
  | tmul r c =>
    rw [starT_tmul, actOn_tmul, actOn_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.smul_apply, map_smul]
    congr 1
    exact bc_adj (AfP p) (D.EF.baseChange ℚ) (L.rep c) (L.rep (sh G c)) (fun v w => L.adj c v w) v w

theorem EFA_actG (L : Link D G) (g : G.GAf) (v w : AfP p ⊗[ℚ] VQ D) :
    EFA D (L.actG g v) (L.actG g w) = ((uSimR (AfP p) g : (AfP p)ˣ) : AfP p) * EFA D v w := by
  obtain ⟨⟨u, c⟩, hmem⟩ := g
  have h1 : (u : AfP p ⊗[ℚ] G.C) * (starT G.star (AfP p) u).unop = algebraMap (AfP p) _ (c : AfP p) := hmem
  have h2 : (starT G.star (AfP p) u).unop * u = algebraMap (AfP p) _ (c : AfP p) := by
    have e : (starT G.star (AfP p) u).unop = ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        algebraMap (AfP p) _ (c : AfP p) := by
      rw [← h1, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [e, _root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hg : ∀ z, L.actG ⟨⟨u, c⟩, hmem⟩ z = actOn L.rep (AfP p) (u : AfP p ⊗[ℚ] G.C) z := fun z => rfl
  rw [hg, hg, EFA_actOn, ← Module.End.mul_apply, ← map_mul, h2, AlgHom.commutes, Module.algebraMap_end_apply,
    map_smul, smul_eq_mul]
  rfl

end Sim

theorem isIntAf_one : IsIntAf (1 : AfP p) := by simpa using isIntAf_intCast (p := p) 1

theorem inAf_mem (D : Datum p) (z : D.La) : inAf D z ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, z, isIntAf_one, rfl⟩

end GlobalTheory.LKGeo.MultScale

namespace GlobalTheory.LKGeo

end GlobalTheory.LKGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure IsSBArgs (G : Grid k) (ϖ : kˣ) (n : ℕ) (F : ColArgs G → RowArgs G → ℂ) : Prop where
  dep : ∀ x x' y y', (∀ j, j < G.m → x j = x' j) → (∀ i, i < G.m → y i = y' i) → F x y = F x' y'
  per : ∀ x y a b, (∀ j, j < G.m → ∀ r s, valuation k (a j r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) →
    (∀ i, i < G.m → ∀ r s, valuation k (b i r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → F (x + a) (y + b) = F x y
  supp : ∀ x y, F x y ≠ 0 → (∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧
    ∀ i, i < G.m → ∀ r s, valuation k (y i r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)

end Local

section Half

variable {D : D7} {a b : ℕ}

def frAt (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x : Mx D b a) :
    Matrix (Fin b) (Fin a) (Kw w) :=
  (Comparison₂.fr β' β (x.map (toEAf D))).map (cpt (D := D) w)

def IsSmall (P : Finset (Pl D.host.E)) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (n : ℤ) (t : Mx D b a) : Prop :=
  ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w β' β t r s) ≤ valuation (Kw w) ((unifAt w ^ n : (Kw w)ˣ) : Kw w)


open Classical in
def cosLoc (P : Finset (Pl D.host.E)) (e : AE D) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (n : ℤ)
    (r t : Mx D b a) : ℂ :=
  if IsHalf e t ∧ IsSmall P β' β n (t - r) then 1 else 0

end Half

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isogeny_flat_finrank : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    A.dim = B.dim ∧ Flat f.hom.left ∧ 0 < deg f ∧ ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
  intro K _ A B f hf
  obtain ⟨hfin, hsurj⟩ := hf
  have hd := _root_.GlobalTheory.AV.DimLe.dim_le K A B f
  have hdim : A.dim = B.dim := le_antisymm (hd.1 hfin) (hd.2 hsurj)
  have hflat : Flat f.hom.left := by
    have hAg := A.smooth
    have hBg : SmoothOfRelativeDimension A.dim B.X.hom := hdim ▸ B.smooth
    have h := GlobalTheory.IsogenyQuasiInverse.flat_fibre A.X B.X A.dim A.ab B.ab hAg hBg f.hom K (𝟙 _)
    have e' : f.hom.left = ((Over.pullbackId (X := Sp K)).inv.app A.X).left ≫
        ((Over.pullback (𝟙 (Sp K))).map f.hom).left ≫
          ((Over.pullbackId (X := Sp K)).hom.app B.X).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      simp
    have i1 : IsIso ((Over.pullbackId (X := Sp K)).inv.app A.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).inv.app A.X)
    have i2 : IsIso ((Over.pullbackId (X := Sp K)).hom.app B.X).left :=
      (Over.forget (Sp K)).map_isIso ((Over.pullbackId (X := Sp K)).hom.app B.X)
    rw [e']
    exact Flat.comp _ _
  obtain ⟨hBint, hBnoeth, -⟩ := _root_.GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B
  have hdeg : deg f = f.hom.left.finrank B.origin := if_pos ⟨hfin, hsurj⟩
  have hconst : ∀ y : B.X.left, f.hom.left.finrank y = deg f := by
    intro y
    rw [hdeg]
    exact (Scheme.Hom.isLocallyConstant_finrank f.hom.left).apply_eq_of_preconnectedSpace y B.origin
  refine ⟨hdim, hflat, ?_, hconst⟩
  have h1 := (Scheme.Hom.one_le_finrank_iff_surjective f.hom.left).mpr hsurj B.origin
  rw [hdeg]
  exact h1

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedWeilDivisorSumSymmNoCommonDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem finsum_mul_comp_eq_sum_indicator {W Z : Type*} (c : W → ℝ) (hc : (Function.support c).Finite) (f : W → Z)
    (F : Finset Z) (hF : f '' Function.support c ⊆ ↑F) (g : Z → ℝ) :
    ∑ᶠ w, c w * g (f w) = ∑ x ∈ F, g x * ∑ᶠ w, c w * Set.indicator {x} 1 (f w) := by
  classical
  have hsub : ∀ h : Z → ℝ, Function.support (fun w => c w * h (f w)) ⊆ ↑hc.toFinset := fun h w hw => by
    rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hw
  rw [finsum_eq_sum_of_support_subset _ (hsub g)]
  have e : ∀ x : Z, ∑ᶠ w, c w * Set.indicator {x} 1 (f w) = ∑ w ∈ hc.toFinset, c w * Set.indicator {x} 1 (f w) :=
    fun x => finsum_eq_sum_of_support_subset _ (hsub (Set.indicator {x} 1))
  simp_rw [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwF : f w ∈ F := hF ⟨w, (Set.Finite.mem_toFinset hc).1 hw, rfl⟩
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq F (f w) (fun x => g x * c w), if_pos hwF, mul_comm]

theorem exists_finset_resCyc {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) (z : Y) :
    ∃ F : Finset Y, ∀ F' : Finset Y, F ⊆ F' → ∀ g : Y → ℝ,
      resCyc hB t g z = ∑ x ∈ F', g x * resCyc hB t (Set.indicator {x} 1) z := by
  classical
  by_cases h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z))
  · have : IsNoetherian (clo z) := (hq.sub (cloι z)).isNoetherian
    set D := divOfSec (LB.isLB_pull hB (cloι z)) _ h
    have hc : (Function.support fun w => (D.mult w : ℝ)).Finite :=
      D.finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
    refine ⟨(hc.image fun w => cloι z w).toFinset, fun F' hF' g => ?_⟩
    simp only [resCyc, dif_pos h]
    refine finsum_mul_comp_eq_sum_indicator _ hc _ F' ?_ g
    intro y hy
    exact hF' ((Set.Finite.mem_toFinset _).2 hy)
  · refine ⟨∅, fun F' _ g => ?_⟩
    simp [resCyc, dif_neg h]

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem iterDiv_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ g : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst g
  classical
  have : IsNoetherian Y := hq.isNoetherian
  choose Ft hFt using exists_finset_resCyc hq hB t
  choose Fs hFs using exists_finset_resCyc hq hA s
  have hms : (Function.support fun z => ((divOfSec hA s hs).mult z : ℝ)).Finite :=
    (divOfSec hA s hs).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  have hmt : (Function.support fun z => ((divOfSec hB t ht).mult z : ℝ)).Finite :=
    (divOfSec hB t ht).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  set F := hms.toFinset.biUnion Ft ∪ hmt.toFinset.biUnion Fs
  have Ls : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z =
      ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Lt : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z =
      ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Es : ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z =
      ∑ x ∈ F, g x * ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFt z F (Finset.subset_union_left.trans' (Finset.subset_biUnion_of_mem Ft hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have Et : ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z =
      ∑ x ∈ F, g x * ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFs z F (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem Fs hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Ls, Lt, Es, Et]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Ls, ← Lt, _root_.GlobalTheory.MixHt.finsum_mult_resCyc_indicator_symm k Y q hq A B hA hB s t hs ht hst x]

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRigExtMapRelFrobLeRangeRigOfOmega
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobRigKer

variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]


variable (O A) in
def evalZeroTwo : A ⊗[O] A →ₗ[O] O :=
  (TensorProduct.lid O O).toLinearMap ∘ₗ TensorProduct.map (counit (R := O)) (counit (R := O))

@[simp] theorem evalZeroTwo_tmul (a b : A) :
    evalZeroTwo O A (a ⊗ₜ b) = counit (R := O) a * counit (R := O) b := by
  simp [evalZeroTwo]

theorem evalZeroTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    evalZeroTwo O B (pullbackTwo f c) = evalZeroTwo O A c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo, evalZeroTwo_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]

theorem evalZeroTwo_comul (b : A) : evalZeroTwo O A (comul b) = counit (R := O) b := by
  have key : TensorProduct.map (counit (R := O)) (counit (R := O)) (comul (R := O) b) =
      LinearMap.lTensor O (counit (R := O)) (LinearMap.rTensor A (counit (R := O)) (comul b)) := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  show TensorProduct.lid O O (TensorProduct.map (counit (R := O)) (counit (R := O)) (comul b)) = _
  rw [key, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul]

theorem evalZeroTwo_cobOne (b : A) : evalZeroTwo O A (cobOne O A b) = - counit (R := O) b := by
  rw [cobOne_apply, map_sub, map_sub, evalZeroTwo_comul, evalZeroTwo_tmul, evalZeroTwo_tmul,
    Bialgebra.counit_one]
  ring

theorem mk_kerIdeal_apply (f : A →ₐc[O] B) (a : A) :
    Ideal.Quotient.mkₐ O (kerIdeal f) (f a) = counit (R := O) a • 1 := by
  have hmem : a - algebraMap O A (counit (R := O) a) ∈ augIdeal O A := by
    simp [RingHom.mem_ker]
  have himg := Ideal.mem_map_of_mem (f : A →ₐ[O] B) hmem
  have e : (f : A →ₐ[O] B) (algebraMap O A (counit (R := O) a)) = algebraMap O B (counit (R := O) a) :=
    AlgHom.commutes _ _
  rw [map_sub, e] at himg
  rw [Algebra.smul_def, mul_one, ← AlgHom.commutes (Ideal.Quotient.mkₐ O (kerIdeal f)),
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  exact himg

theorem map_mk_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (pullbackTwo f c) = evalZeroTwo O A c • 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [pullbackTwo, TensorProduct.map_tmul, BialgHom.coe_toLinearMap,
      Algebra.TensorProduct.map_tmul, mk_kerIdeal_apply, evalZeroTwo_tmul,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [mul_comm]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), add_smul]

theorem map_mk_cobOne_eq_zero (f : A →ₐc[O] B) {c : A ⊗[O] A} {b : B}
    (hb : counit (R := O) b = 0) (hc : cobOne O B b = pullbackTwo f c) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (cobOne O B b) = 0 := by
  rw [hc, map_mk_pullTwo, ← evalZeroTwo_pullTwo f c, ← hc, evalZeroTwo_cobOne, hb, neg_zero,
    zero_smul]

def oneFun {p : ℕ} (G : PDivGroup p O) : G.funs := ⟨fun _ => 1, fun _ => map_one _⟩

theorem funsMap_oneFun {p : ℕ} {G H : PDivGroup p O} (f : G ⟶ H) :
    funsMap f (oneFun H) = oneFun G :=
  Subtype.ext (funext fun n => map_one (f.app n))

theorem dUnit_one : dUnit (R := O) (1 : A) = 0 := by
  simp [dUnit]

end GlobalTheory.PDiv.FrobRigKer

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv.FrobRigKer

theorem ker_rigExtMap_relFrob_le_range_rigOfOmega (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hmk : Function.Surjective (frobTwist h G).rigMk := Submodule.mkQ_surjective _
  obtain ⟨⟨c, w⟩, rfl⟩ := hmk x
  rw [rigExtMap_mk] at hx
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
  have hB1 : G.cob B = cocyclesMap (relFrob h G) c := congrArg Prod.fst hB
  have hB2 : G.dFun B = G.omegaMap _ (relFrob h G) w := congrArg Prod.snd hB
  set t : K := counit (R := K) (B.1 1) with ht
  set B₁ : G.funs := B - t • oneFun G with hB₁
  set c₁ : (frobTwist h G).cocycles := c - t • (frobTwist h G).cob (oneFun (frobTwist h G))
    with hc₁def
  have hc₁ : G.cob B₁ = cocyclesMap (relFrob h G) c₁ := by
    simp only [hB₁, hc₁def, map_sub, map_smul, hB1, cocyclesMap_cob, funsMap_oneFun]
  have hb0 : counit (R := K) (B₁.1 1) = 0 := by
    show counit (R := K) (B.1 1 - t • (1 : G.A 1)) = 0
    rw [map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, ht, sub_self]
  have hbd : dUnit (R := K) (B₁.1 1) = 0 := by
    have e1 : G.dFun B = 0 := by rw [hB2, omegaMap_relFrob, LinearMap.zero_apply]
    have e2 : G.dFun (oneFun G) = 0 := Subtype.ext (funext fun n => dUnit_one)
    have e : G.dFun B₁ = 0 := by rw [hB₁, map_sub, map_smul, e1, e2, smul_zero, sub_zero]
    exact congrArg (fun z : G.omega => z.1 1) e
  have hcob : cobOne K (G.A 1) (B₁.1 1) = pullbackTwo ((relFrob h G).app 1) (c₁.1 1) :=
    congrArg (fun z : G.cocycles => z.1 1) hc₁
  have hker := _root_.GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob p K h G 1
  have hmem : B₁.1 1 ∈ frobKerIdeal p K (G.A 1) := by
    refine GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential p K (G.A 1) _ hb0 hbd ?_
    rw [hker]
    exact map_mk_cobOne_eq_zero ((relFrob h G).app 1) hb0 hcob
  rw [hker] at hmem
  have hV : (verschiebung h G).app 1 (B₁.1 1) = 0 :=
    _root_.GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) _ hmem
  have hcomp : cocyclesMap (verschiebung h G) (cocyclesMap (relFrob h G) c₁) =
      cocyclesMap (verschiebung h G ≫ relFrob h G) c₁ :=
    Subtype.ext (funext fun n => (pullTwo_comp _ _ _).symm)
  obtain ⟨B', hB'⟩ : c₁ ∈ LinearMap.range (frobTwist h G).cob := by
    refine _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP (frobTwist h G) c₁ (funsMap (verschiebung h G) B₁) ?_ hV
    rw [← cocyclesMap_cob, hc₁, hcomp, verschiebung_comp_relFrob]
  set B₀ : (frobTwist h G).funs := B' + t • oneFun (frobTwist h G) with hB₀
  have hc0 : (frobTwist h G).cob B₀ = c := by
    rw [hB₀, map_add (f := _), map_smul, hB', hc₁def, sub_add_cancel]
  refine ⟨w - (frobTwist h G).dFun B₀, ?_⟩
  show Submodule.Quotient.mk ((0 : (frobTwist h G).cocycles), w - (frobTwist h G).dFun B₀) =
    Submodule.Quotient.mk (c, w)
  refine ((Submodule.Quotient.eq
    (LinearMap.range ((frobTwist h G).cob.prod (frobTwist h G).dFun))).2
    (LinearMap.mem_range.2 ⟨B₀, Prod.ext ?_ ?_⟩)).symm
  · show (frobTwist h G).cob B₀ = c - 0
    rw [sub_zero]
    exact hc0
  · show (frobTwist h G).dFun B₀ = w - (w - (frobTwist h G).dFun B₀)
    exact (sub_sub_cancel w _).symm

end GlobalTheory.PDivGroup
end
end

