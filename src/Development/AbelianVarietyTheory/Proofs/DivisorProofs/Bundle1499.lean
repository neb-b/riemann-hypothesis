module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathUniqueOfAgreeLowDegrees
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_spMap_fromSpecStalk {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint (CommRingCat.of A)) = x) :
    ∃ g0 : X.presheaf.stalk x →+* A, spMap g0 ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨(Scheme.stalkClosedPointTo f).hom, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem ringHom_eq_of_fromSpecStalk {X : Scheme.{0}} (x : X) {B : Type} [CommRing B]
    (f f' : X.presheaf.stalk x →+* B) (h : spMap f ≫ X.fromSpecStalk x = spMap f' ≫ X.fromSpecStalk x) : f = f' := by
  have h' : spMap f = spMap f' := (cancel_mono (X.fromSpecStalk x)).mp h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_constantCoeff_closedPoint (R : Type) [CommRing R] [IsLocalRing R] : (spMap (PowerSeries.constantCoeff (R := R))) (IsLocalRing.closedPoint (CommRingCat.of R)) = IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R)) := by
  haveI : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (PowerSeries.constantCoeff (R := R)))) :=
    ⟨fun _ h => PowerSeries.isUnit_iff_constantCoeff.mpr h⟩
  exact Spec_closedPoint

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem path_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R) (n : ℕ), 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ ξ' : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G c b ξ' → (∀ (U : G.left.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(G.left, U)) (j : ℕ), 0 < j → j < n → PowerSeries.coeff j (evAt ξ h f) = PowerSeries.coeff j (evAt ξ' h' f)) → ξ = ξ' := by
  intro S G _ R _ _ hqs c n hn hc b ξ ξ' hξ hξ' hlow
  set s : S := b (IsLocalRing.closedPoint (CommRingCat.of R)) with hs
  set x : G.left := unitSec G s with hx
  have hpt : ∀ q0 : Sp (PowerSeries R) ⟶ G.left, IsPath G c b q0 →
      q0 (IsLocalRing.closedPoint (CommRingCat.of (PowerSeries R))) = x := by
    intro q0 hq0
    have e := congrArg (fun q : Sp R ⟶ G.left => q (IsLocalRing.closedPoint (CommRingCat.of R))) hq0.zero
    change q0 (spMap PowerSeries.constantCoeff (IsLocalRing.closedPoint (CommRingCat.of R))) = unitSec G s at e
    rw [spMap_constantCoeff_closedPoint] at e
    exact e
  obtain ⟨π, ε, m, hSD, h1, h2, h3⟩ := _root_.GlobalTheory.Nef.stalkData_exists S G s
  have hm := _root_.GlobalTheory.Nef.sqr_sub_two_mem S G hqs s π ε m hSD
  obtain ⟨β, hβ⟩ := exists_spMap_fromSpecStalk b s rfl
  obtain ⟨g, hg⟩ := exists_spMap_fromSpecStalk ξ x (hpt ξ hξ)
  obtain ⟨g', hg'⟩ := exists_spMap_fromSpecStalk ξ' x (hpt ξ' hξ')
  have E1 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      k.comp π = PowerSeries.C.comp β := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk s
    rw [spMap_comp' π k, spMap_comp' β PowerSeries.C, Category.assoc, Category.assoc, hβ, hSD.str, ← Category.assoc, hk.base]
  have E2 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      PowerSeries.constantCoeff.comp k = β.comp ε := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k PowerSeries.constantCoeff, spMap_comp' ε β, Category.assoc, Category.assoc, hSD.unit, ← Category.assoc (spMap β), hβ, hk.zero]
  have E3 : ∀ (k : G.left.presheaf.stalk x →+* PowerSeries R), IsPath G c b (spMap k ≫ G.left.fromSpecStalk x) →
      (PowerSeries.rescale c).comp k = k.comp m := by
    intro k hk
    apply ringHom_eq_of_fromSpecStalk x
    rw [spMap_comp' k (PowerSeries.rescale c), spMap_comp' m k, Category.assoc, Category.assoc, hSD.sq, hk.scale, Category.assoc]
  subst hg hg'
  have hlow' : ∀ j < n, ∀ f, PowerSeries.coeff j (g f) = PowerSeries.coeff j (g' f) := by
    intro j hj f
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have a := RingHom.congr_fun (E2 g hξ) f
      have a' := RingHom.congr_fun (E2 g' hξ') f
      simp only [RingHom.comp_apply] at a a'
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply, a, a']
    · obtain ⟨U, hxU, f0, rfl⟩ := TopCat.Presheaf.germ_exist _ f
      obtain ⟨hh, hev⟩ := (_root_.GlobalTheory.Nef.evAt_calculus).2.2.2.2.2.2 (PowerSeries R) G.left x g U hxU
      obtain ⟨hh', hev'⟩ := (_root_.GlobalTheory.Nef.evAt_calculus).2.2.2.2.2.2 (PowerSeries R) G.left x g' U hxU
      have := hlow U hh hh' f0 j hj0 hj
      rw [hev, hev'] at this
      exact this
  have := ringHom_powerSeries_eq_of_rescale _ _ R π ε m β c n h1 h2 h3 hm hn hc g g' (E1 g hξ) (E1 g' hξ')
    (E2 g hξ) (E2 g' hξ') (E3 g hξ) (E3 g' hξ') hlow'
  rw [this]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def gfcToGf (V : HSp D) : GfC V →* Bridge.Gf V := (finHom V).rangeRestrict.comp (GfC V).subtype

theorem gfcToGf_surjective (V : HSp D) : Function.Surjective (gfcToGf V) := by
  rintro ⟨_, h, rfl⟩
  obtain ⟨k, hk, e⟩ := GlobalTheory.VolHeckeCompare.exists_finite_part V h
  exact ⟨⟨k, hk⟩, Subtype.ext e⟩

theorem bc_swapAE_injective (n : ℕ) :
    Function.Injective (Formalism.UG.bc (Lev.swapAE D) : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →* _) := by
  intro a b e
  apply Units.ext
  have h := congrArg Units.val e
  exact Matrix.map_injective (f := Lev.swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finG_injective (V : HSp D) : Function.Injective (finG V) := by
  intro a b e
  have e' : finHom V a.1 = finHom V b.1 := bc_swapAE_injective V.rank e
  have h1 : finHom V (a.1⁻¹ * b.1) = 1 := by rw [map_mul, map_inv, e', inv_mul_cancel]
  have := GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (mul_mem (inv_mem a.2) b.2) h1
  exact Subtype.ext (inv_mul_eq_one.1 this)

def finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Subgroup (Bridge.Gf V) :=
  (K.comap (Formalism.UG.bc (Lev.swapAE D))).comap (Bridge.Gf V).subtype

theorem mem_finLev_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (g : GfC V) :
    gfcToGf V g ∈ finLev V K ↔ g ∈ K.comap (finG V) := Iff.rfl

theorem isOpenLev_finLev (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsCO V K) :
    GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V (finLev V K) := by
  have e : (((finLev V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) =
      ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
  rw [e]
  exact hK.1

theorem finite_finCl (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) : Finite (FinCl V K) := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV (finLev V K) (isOpenLev_finLev V K hK)
  choose x hx using fun a => gfcToGf_surjective V (c a)
  refine Finite.of_surjective (fun a : Fin m => (DoubleCoset.mk (ratFin V) (K.comap (finG V)) (x a) : FinCl V K)) ?_
  intro q
  rw [← DoubleCoset.out_eq' q]
  set y := Quotient.out q
  obtain ⟨a, γ, k, e⟩ := hc (gfcToGf V y)
  obtain ⟨z, hz⟩ := gfcToGf_surjective V (Bridge.ratF V γ)
  refine ⟨a, (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨z, ?_, (x a)⁻¹ * z⁻¹ * y, ?_, by group⟩⟩
  · have hz' : finHom V z.1 = finHom V γ.1 := congrArg Subtype.val hz
    refine ⟨γ.1, γ.2, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V γ.1) = Formalism.UG.bc (Lev.swapAE D) (finHom V z.1)
    rw [hz']
  · refine (mem_finLev_iff V K _).1 ?_
    have h1 : gfcToGf V ((x a)⁻¹ * z⁻¹ * y) = (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y := by
      simp only [map_mul, map_inv]
    have h2 : (gfcToGf V (x a))⁻¹ * (gfcToGf V z)⁻¹ * gfcToGf V y = (k : Bridge.Gf V) := by
      simp only [hx a, hz, e]; group
    exact (congrArg (· ∈ finLev V K) (h1.trans h2)).mpr k.2

theorem continuous_finHom (V : HSp D) : Continuous (finHom V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  exact (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ

theorem gamOrd_ne_zero (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hV : ∀ τ, (gramAt D V τ).PosDef) (hK : IsCO V K) (x : GfC V) : gamOrd V K x ≠ 0 := by
  set C : Set (Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⋃ p : Fin V.rank × Fin V.rank, (fun g : GA D V => (finHom V g).1 p.1 p.2) '' (Lev.levA V K : Set (GA D V)) with hCdef
  have hC : IsCompact C := isCompact_iUnion fun p =>
    hK.2.image ((Units.continuous_val.comp (continuous_finHom V)).matrix_elem p.1 p.2)
  have hCJ : ∀ k ∈ finLev V K, ∀ i j, (k : Bridge.Gf V).1.1 i j ∈ C := by
    intro k hk i j
    obtain ⟨g, rfl⟩ := gfcToGf_surjective V k
    exact Set.mem_iUnion.2 ⟨(i, j), g.1, ⟨g.2, (mem_finLev_iff V K g).1 hk⟩, rfl⟩
  have hs := GlobalTheory.RepsObj.finite_stab V hV (finLev V K) hC hCJ (gfcToGf V x)
  have hq : ∀ γ : ratFin V, ∃ q : GQ V, Lev.finE V q.1 = finG V γ.1 := fun γ => by
    obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 γ.2
    exact ⟨⟨q, hq⟩, e⟩
  choose q hq using hq
  have hfin : Finite {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K} := by
    refine Finite.of_injective (β := Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x))
      (fun γ => ⟨q γ.1, ?_⟩) ?_
    · have e0 : Bridge.ratF V (q γ.1) = gfcToGf V γ.1.1 :=
        Subtype.ext (bc_swapAE_injective V.rank (hq γ.1))
      have e1 : (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) = gfcToGf V (x⁻¹ * γ.1.1 * x) := by
        simp only [e0, map_mul, map_inv, MulAut.conj_inv_apply]
      show (MulAut.conj (gfcToGf V x)⁻¹) (Bridge.ratF V (q γ.1)) ∈ finLev V K
      exact (congrArg (· ∈ finLev V K) e1).mpr ((mem_finLev_iff V K _).2 γ.2)
    · intro γ γ' e
      have e1 : Lev.finE V (q γ.1).1 = Lev.finE V (q γ'.1).1 := by
        have := congrArg (fun s : Bridge.stab (Bridge.ratF V) (finLev V K) (gfcToGf V x) => Lev.finE V s.1.1) e
        exact this
      rw [hq, hq] at e1
      exact Subtype.ext (Subtype.ext (finG_injective V e1))
  refine Nat.card_ne_zero.2 ⟨⟨⟨1, one_mem _⟩, ?_⟩, hfin⟩
  simp only [mul_one, inv_mul_cancel, map_one]
  exact one_mem K

theorem finite_finCl_and_gamOrd : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))),
    (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) → IsCO V K → Finite (FinCl V K) ∧ ∀ x, gamOrd V K x ≠ 0 :=
  fun V K hV hK => ⟨finite_finCl V K (fun τ => hV (tauE _ τ)) hK, gamOrd_ne_zero V K (fun τ => hV (tauE _ τ)) hK⟩

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterBoundedConductorKillsIdeleNorms
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.SplitChar GlobalTheory.NormSum.UnramHecke Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.NormKill

variable {D : D7}

theorem vl_le_of_dvd {p N : ℕ} (h : p ∣ N) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    vl D v (N : AE D) ≤ vl D v (p : AE D) := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (vl_le (natCast_mem _ _) v)

theorem exists_global_congN {N : ℕ} (hN : 1 < N) (x : (AE D)ˣ) :
    ∃ a : D.host.Eˣ, ∃ s ∈ OhE D, ((incU D a * x⁻¹ : (AE D)ˣ) : AE D) - 1 = (N : AE D) * s := by
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (by omega : 0 < N) hn)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 = (N : AE D) * (-(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (Nat.minFac_prime (by omega : N ≠ 1))
    have h2 := congrArg (vl D v) h1
    rw [map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one, map_mul] at h2
    have h3 : vl D v (N : AE D) < 1 := (vl_le_of_dvd (Nat.minFac_dvd N) v).trans_lt (val_nat_lt hv)
    have h4 := (mul_le_of_le_one_right' (vl_le (neg_mem (mul_mem hr hx)) v)).trans_lt h3
    rw [← h2] at h4
    exact lt_irrefl _ h4
  exact ⟨Units.mk0 a ha, _, neg_mem (mul_mem hr hx), h1⟩

theorem vl_norm_sub_one {N : ℕ} {z : (AE D)ˣ} {s : AE D} (hs : s ∈ OhE D) (e : (z : AE D) - 1 = (N : AE D) * s)
    (v : HeightOneSpectrum (𝓞 D.host.E)) :
    vl D v (((z * sgU D z : (AE D)ˣ) : AE D) - 1) ≤ vl D v (N : AE D) := by
  obtain ⟨v', hv', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv v
  have hN1 : ∀ w, vl D w (N : AE D) ≤ 1 := fun w => vl_le (natCast_mem _ _) w
  have h1 : ∀ w, vl D w ((z : AE D) - 1) ≤ vl D w (N : AE D) := fun w => by
    rw [e, map_mul]
    exact mul_le_of_le_one_right' (vl_le hs w)
  have h2 : vl D v (sgA D z - 1) ≤ vl D v (N : AE D) := by
    rw [← map_one (sgA D), ← map_sub, vl_sgA (conjPl_symm hv')]
    refine (h1 v').trans (le_of_eq ?_)
    rw [← vl_sgA (conjPl_symm hv'), map_natCast]
  have e2 : ((z * sgU D z : (AE D)ˣ) : AE D) - 1 =
      ((z : AE D) - 1) * (sgA D z - 1) + (((z : AE D) - 1) + (sgA D z - 1)) := by
    change (z : AE D) * sgA D z - 1 = _
    ring
  rw [e2]
  refine Valuation.map_add_le _ ?_ (Valuation.map_add_le _ (h1 v) h2)
  rw [map_mul]
  exact (mul_le_of_le_one_right' (h2.trans (hN1 v))).trans (h1 v)

theorem vl_pow_le {p m : ℕ} (hp : p ∣ m) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : Formalism.L2.Host.OverP D.host p v) (k : ℕ) :
    vl D v ((m ^ (k + 1) : ℕ) : AE D) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  have h1 : vl D v (m : AE D) ≤ WithZero.exp (-1) := by
    have := GlobalTheory.Mem.KerDet.le_exp_neg_one ((vl_le_of_dvd hp v).trans_lt (val_nat_lt hv))
    simpa using this
  rw [Nat.cast_pow, map_pow]
  calc vl D v (m : AE D) ^ (k + 1) ≤ WithZero.exp (-1) ^ (k + 1) := pow_le_pow_left₀ zero_le h1 _
    _ = WithZero.exp (-((k : ℤ) + 1)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp

theorem chi_norm_global (χ : Formalism.L2.Host.HChar D.host.E) {n : D.what₂.Tau → ℤ} (hi : χ.HasInf (embT D) n) (a : D.host.Eˣ) :
    χ.1 (finIdl D (incU D a * sgU D (incU D a))) = 1 := by
  obtain ⟨k', hk⟩ := exists_real_norm a
  have hu : ((Formalism.L2.Host.upF D.host.F k' : D.host.Eˣ) : D.host.E) = (a : D.host.E) * D.host.conj a := by
    haveI : Nontrivial (AE D) := by
      obtain ⟨v, -⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E Nat.prime_two
      refine ⟨⟨0, 1, fun h => ?_⟩⟩
      have := congrArg (vl D v) h
      rw [map_zero, map_one] at this
      exact zero_ne_one this
    apply (inc D).injective
    have := congrArg Units.val hk
    change inc D a * sgA D (inc D a) = inc D _ at this
    rw [← this, sgA_inc, map_mul]
  have hinf : χ.inf (Formalism.L2.Host.upF D.host.F k') = 1 := by
    apply Units.ext
    rw [hi, Units.val_one]
    refine Finset.prod_eq_one fun τ _ => ?_
    have h0 : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    have h1 : embT D τ ((Formalism.L2.Host.upF D.host.F k' : D.host.Eˣ) : D.host.E) = ((Complex.normSq (embT D τ (a : D.host.E)) : ℝ) : ℂ) := by
      rw [hu, map_mul, emb_conj, Complex.mul_conj]
    have h2 : (0 : ℝ) < Complex.normSq (embT D τ (a : D.host.E)) := Complex.normSq_pos.2 h0
    rw [h1, Complex.norm_real, Real.norm_of_nonneg h2.le, div_self (by exact_mod_cast h2.ne'), one_zpow]
  rw [hk, finIdl_incU]
  have h1 := χ.2.2 (Formalism.L2.Host.upF D.host.F k')
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul] at h1
  have h2 : χ.1 (Formalism.L2.Host.infDiag (Formalism.L2.Host.upF D.host.F k')) = 1 := hinf
  rw [h2, one_mul] at h1
  exact h1

theorem chi_norm_cong (χ : Formalism.L2.Host.HChar D.host.E) (S : Finset ℕ) (k : ℕ) (ht : χ.TrivOn D.host.F)
    (hl : ∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) (z : (AE D)ˣ)
    (hz : ∀ q ∈ S, ∀ v, Formalism.L2.Host.OverP D.host q v →
      vl D v (((z * sgU D z : (AE D)ˣ) : AE D) - 1) ≤ WithZero.exp (-((k : ℤ) + 1))) :
    χ.1 (finIdl D (z * sgU D z)) = 1 := by
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hG : ∀ v k', GlobalTheory.Mem.Chr.locF (L := D.host.E) D.host.F v k' ∈ (χ.1.comp (finPartI D.host.E)).ker := fun v k' => by
    rw [MonoidHom.mem_ker]
    exact GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k'
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu _ hG _ (norm_balanced z)
  rw [MonoidHom.mem_ker] at hb
  rw [← finPartI_finIdl, ← mul_inv_cancel_left b (finIdl D (z * sgU D z)), map_mul, map_mul]
  rw [show χ.1 (finPartI D.host.E b) = 1 from hb, one_mul]
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hun) (fun _ => rfl) fun v y hy => ?_
  have hy' : (y : v.adicCompletion D.host.E) = ((b⁻¹ * finIdl D (z * sgU D z) : Neutral.B1.Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := hy
  have hyu : Formalism.L2.Host.IsUnitAt v y := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [hy']
    exact hun v
  change χ.loc v y = 1
  rcases hl v with hU | ⟨q, hq, hov, hL⟩
  · exact hU y hyu
  · have hlt : WithZero.exp (-((k : ℤ) + 1)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have h0 : Valued.v ((finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v - 1) < 1 := by
      rw [vl_sub_one]
      exact (hz q hq v hov).trans_lt hlt
    have hv1 : IdlFact.valAt v (finIdl D (z * sgU D z)) = 1 := by
      rw [IdlFact.valAt_apply, ← sub_add_cancel ((finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v) 1, add_comm]
      exact Valuation.map_one_add_of_lt _ h0
    have h3 : Units.map (GlobalTheory.Mem.LocTriv.ev v) (b⁻¹ * finIdl D (z * sgU D z)) = Units.map (GlobalTheory.Mem.LocTriv.ev v) (finIdl D (z * sgU D z)) := by
      rw [map_mul, map_inv, hc v hv1, inv_one, one_mul]
    have h4 := congrArg Units.val h3
    refine hL y hyu ?_
    rw [hy']
    change Valued.v (((b⁻¹ * finIdl D (z * sgU D z) : Neutral.B1.Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v - 1) ≤ _
    have h4' : ((b⁻¹ * finIdl D (z * sgU D z) : Neutral.B1.Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 v =
        (finIdl D (z * sgU D z) : AdeleRing (𝓞 D.host.E) D.host.E).2 v := h4
    rw [h4', vl_sub_one]
    refine (hz q hq v hov).trans ?_
    rw [WithZero.exp_le_exp]
    omega

theorem mul_eq_mul_mul_inv {G : Type} [CommGroup G] (x y u v : G) : x * y = (u * v) * ((u * x⁻¹) * (v * y⁻¹))⁻¹ := by
  simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem chi_finIdl_norm_eq_one : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.what₂.Tau → ℤ) (S : Finset ℕ) (k : ℕ), χ.TrivOn D.host.F → χ.HasInf (embT D) n → (∀ q ∈ S, q.Prime) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 := by
  intro D χ n S k ht hi hS hl x
  have hP : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  have hm : 1 < (2 * ∏ q ∈ S, q) ^ (k + 1) := Nat.one_lt_pow (by omega) (by omega)
  obtain ⟨a, s, hs, e⟩ := exists_global_congN (D := D) hm x
  have hz : ∀ q ∈ S, ∀ v, Formalism.L2.Host.OverP D.host q v →
      vl D v ((((incU D a * x⁻¹) * sgU D (incU D a * x⁻¹) : (AE D)ˣ) : AE D) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) :=
    fun q hq v hov => (vl_norm_sub_one hs e v).trans
      (vl_pow_le (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hq) 2) hov k)
  have h1 := chi_norm_cong χ S k ht hl _ hz
  have h2 := chi_norm_global χ hi a
  have e2 : x * sgU D x = (incU D a * sgU D (incU D a)) * ((incU D a * x⁻¹) * sgU D (incU D a * x⁻¹))⁻¹ := by
    rw [map_mul, map_inv]
    exact mul_eq_mul_mul_inv _ _ _ _
  rw [e2, map_mul, map_mul, map_inv, map_inv, h2, h1, inv_one, one_mul]

end GlobalTheory.NormKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterNonInertBoundedLevelKillsUnits
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum.UnrKill

open GlobalTheory.Mem.Col2.SplitChar

theorem vl_nat_coprime {D : D7} {q m : ℕ} (hm : Nat.Coprime m q) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : Formalism.L2.Host.OverP D.host q v) : vl D v (m : AE D) = 1 := by
  refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have hab' := congrArg (Int.cast : ℤ → AE D) hab
  push_cast at hab'
  have h2 : vl D v ((a : AE D) * m) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
  have h3 : vl D v ((b : AE D) * q) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [hab', map_one] at h4
  exact lt_irrefl _ h4

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem vl_le_of_zeroAt {D : D7} {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : Formalism.L2.Host.OverP D.host q v) (k : ℕ) : vl D v x ≤ WithZero.exp (-(k : ℤ)) := by
  obtain ⟨m, -, hm, s, hs, e⟩ := h k
  have h1 := vl_nat_coprime hm hv
  have h2 : vl D v x = vl D v (q : AE D) ^ k * vl D v s := by
    rw [← one_mul (vl D v x), ← h1, ← map_mul, e, map_mul, map_pow]
  rw [h2]
  refine (mul_le_of_le_one_right' (vl_le hs v)).trans ?_
  calc vl D v (q : AE D) ^ k ≤ WithZero.exp (-1 : ℤ) ^ k := pow_le_pow_left₀ zero_le' (le_exp_neg_one (val_nat_lt hv)) k
    _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp

end GlobalTheory.FunObj.SqNum.UnrKill


open GlobalTheory.FunObj.SqNum.UnrKill GlobalTheory.Mem.Col2.SplitChar in
theorem GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (S : Finset ℕ) (k : ℕ), (∀ q ∈ S, q.Prime ∧ ¬ InertQ D q) → (∀ v, χ.UnrAt v ∨ ∃ q ∈ S, Formalism.L2.Host.OverP D.host q v ∧ χ.LevelLe v k) → ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1 := by
  intro D χ S k hS hχ u hu hz
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  rcases hχ v with h | ⟨q, hq, hov, hl⟩
  · exact h x hxu
  · refine hl x hxu ?_
    rw [hx, vl_sub_one]
    exact vl_le_of_zeroAt (hz q (hS q hq).1 (hS q hq).2) hov k
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralConjEqOfTest
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

def conjNormalEquiv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) (b : G) (h : ∀ u, u ∈ N ↔ b * u * b⁻¹ ∈ N) : N ≃ₜ* N := GlobalTheory.ConjugationEquiv.conjEquiv N b h

end GlobalTheory.ResLine
end

