module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedOneSubLeOfMovesIdealCompletion
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

namespace GlobalTheory.CosetOrth

theorem exists_single_adele {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    ∃ s : FiniteAdeleRing (𝓞 E) E, s w = x ∧ ∀ u, u ≠ w → s u = 0 := by
  refine ⟨⟨Pi.single w x, ?_⟩, ?_, ?_⟩
  · refine Filter.eventually_cofinite.2 ((Set.finite_singleton w).subset fun u hu => ?_)
    by_contra hne
    apply hu
    rw [Pi.single_eq_of_ne hne]
    exact zero_mem _
  · exact Pi.single_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w x
  · intro u hu
    exact Pi.single_eq_of_ne (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) hu x

theorem row_bound {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (hv : Function.Surjective v) {ι : Type} [Fintype ι] (δ h : ι → K) (hδ : ∀ k, v (δ k) ≤ 1) {C : Γ} (hC : 1 < C)
    (H : ∀ x, v x ≤ C → (∀ k, v (x * h k) ≤ C) → ∀ j, v (x * (δ j - h j)) ≤ 1) (j : ι) :
    v (δ j - h j) ≤ C⁻¹ := by
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hint : ∀ k, v (h k) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₀⟩ := hcon
    obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun k => v (h k)) ⟨k₀, Finset.mem_univ _⟩
    have h1 : 1 < v (h k) := hk₀.trans_le (hk k₀ (Finset.mem_univ _))
    have h0 : 0 < v (h k) := zero_lt_one.trans h1
    obtain ⟨x, hx⟩ := hv (C * (v (h k))⁻¹)
    have hxk : v x * v (h k) = C := by rw [hx, mul_assoc, inv_mul_cancel₀ h0.ne', mul_one]
    have key := H x (by rw [← hxk]; exact le_mul_of_one_le_right' h1.le)
      (fun l => by rw [map_mul, ← hxk]; gcongr; exact hk l (Finset.mem_univ _)) k
    rw [map_mul, v.map_sub_eq_of_lt_right ((hδ k).trans_lt h1), hxk] at key
    exact absurd hC (not_lt.2 key)
  obtain ⟨x, hx⟩ := hv C
  have key := H x hx.le (fun l => by rw [map_mul, hx]; exact mul_le_of_le_one_right' (hint l)) j
  rw [map_mul, hx] at key
  calc v (δ j - h j) = C⁻¹ * (C * v (δ j - h j)) := by rw [← mul_assoc, inv_mul_cancel₀ hC0.ne', one_mul]
    _ ≤ C⁻¹ * 1 := by gcongr
    _ = C⁻¹ := mul_one _

theorem valued_one_sub_le_of_moves_integral : ∀ {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (𝓞 E)⁰ E) (w : HeightOneSpectrum (𝓞 E)) (c : ℤ) (n : E)
  {a : ℕ} (H : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)), w.valuation E n = 1 → FractionalIdeal.count E w I = -c → 1 ≤ c →
  (∀ (s : FiniteAdeleRing (𝓞 E) E) (i j : Fin a), InHat I s → (∀ k, InHat I (s * H i k)) →
    InHat 1 (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i j))) →
  ∀ i j, Valued.v ((1 - H) i j w) ≤ WithZero.exp (-c) := by
  intro E _ _ I w c n a H hn hI hc hH i j
  have hsub : ∀ l, (1 - H) i l w = (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w - H i l w :=
    fun l => rfl
  rw [hsub, WithZero.exp_neg]
  refine row_bound Valued.v (w.valuedAdicCompletion_surjective E)
    (fun l => (1 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i l w) (fun l => H i l w) (fun k => ?_) ?_ ?_ j
  · by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq]
      have : (1 : FiniteAdeleRing (𝓞 E) E) w = 1 := rfl
      rw [this, map_one]
    · rw [Matrix.one_apply_ne hik]
      have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
      rw [this, map_zero]; exact zero_le
  · rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro x hx hxh l
    obtain ⟨s, hsw, hsu⟩ := exists_single_adele w x
    have h1 : InHat I s := fun u => by
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hx
      · rw [hsu u hu, map_zero]; exact zero_le
    have h2 : ∀ k, InHat I (s * H i k) := fun k u => by
      have : (s * H i k) u = s u * H i k u := rfl
      rw [this]
      by_cases hu : u = w
      · subst hu; rw [hsw, hI, neg_neg]; exact hxh k
      · rw [hsu u hu, zero_mul, map_zero]; exact zero_le
    have key := (inHat_one_iff _).1 (hH s i l h1 h2) w
    have e : (algebraMap E (FiniteAdeleRing (𝓞 E) E) n * (s * (1 - H) i l)) w =
        (n : w.adicCompletion E) * (s w * (1 - H) i l w) := rfl
    rw [e, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hn, one_mul, hsw, hsub] at key
    exact key

end GlobalTheory.CosetOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldFollowsDerivationOnSmallerOpenAtField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocVal

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_mul {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_add {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f + g) = valR x U f + valR x U g := by
  simp only [valR_eq x U h, map_add (f := _)]

theorem valR_pow {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) (n : ℕ) : valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_eq x U h, map_pow]

theorem valR_one {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valR x U (1 : Γ(X, U)) = 1 := by
  simp only [valR_eq x U h, map_one]

theorem valR_res {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : valR x V (resG X e f) = valR x U f := by
  rw [valR_eq x V h, valR_eq x U (h.trans (x.preimage_mono e))]
  congr 1
  rw [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_field_of_le : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ Z),
    ⊤ ≤ ξ ⁻¹ᵁ U → ∀ (d : Fld Z), IsField U d → ∀ (D : F → F), (∀ x y, D (x + y) = D x + D y) →
    (∀ x y, D (x * y) = x * D y + y * D x) → (∀ f : Γ(Z, U), valR ξ U (d U f) = D (valR ξ U f)) →
    ∀ O : Z.Opens, O ≤ U → ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h : Γ(Z, O), valR ξ O (d O h) = D (valR ξ O h) := by
  intro Z U hU F _ ξ _ d hd D _ hDm hDU O hOU hξO h
  obtain ⟨p₀⟩ : Nonempty (Sp F) := inferInstance
  have hp₀ : ξ.base p₀ ∈ O := hξO (Set.mem_univ p₀)
  obtain ⟨g, hgO, hg⟩ := hU.exists_basicOpen_le (V := O) ⟨_, hp₀⟩ (hOU hp₀)
  set B := Z.basicOpen g
  have hBU : B ≤ U := hgO.trans hOU
  have hξB : ⊤ ≤ ξ ⁻¹ᵁ B := by
    intro p _
    have : p = p₀ := Subsingleton.elim _ _
    subst this
    exact hg
  have := hU.isLocalization_basicOpen g
  obtain ⟨m, f, hf⟩ := IsLocalization.Away.surj g (resG Z hgO h)
  have hf' : resG Z hgO h * resG Z hBU g ^ m = resG Z hBU f := hf

  have hgu : IsUnit (resG Z hBU g) := Z.toRingedSpace.isUnit_res_basicOpen g
  have hg0 : valR ξ U g ≠ 0 := by
    obtain ⟨u, hu⟩ := hgu
    intro h0
    have e1 := congrArg (valR ξ B) u.mul_inv
    rw [valR_mul ξ B hξB, valR_one ξ B hξB, hu, valR_res ξ hBU hξB, h0, zero_mul] at e1
    exact zero_ne_one e1

  have hL := congrArg (d B) hf'
  rw [hd.2.1 B hBU, ← map_pow, hd.2.2 U B hBU le_rfl, hd.2.2 U B hBU le_rfl, hd.2.2 O B hgO hOU] at hL
  have hV := congrArg (valR ξ B) hL
  rw [valR_add ξ B hξB, valR_mul ξ B hξB, valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB,
    valR_res ξ hBU hξB, valR_res ξ hBU hξB, hDU, hDU] at hV
  have hfv : valR ξ U f = valR ξ O h * valR ξ U g ^ m := by
    have := congrArg (valR ξ B) hf'
    rw [valR_mul ξ B hξB, valR_res ξ hgO hξB, valR_res ξ hBU hξB, valR_pow ξ B hξB, valR_res ξ hBU hξB] at this
    exact this.symm
  rw [hfv, hDm, valR_pow ξ U (hξB.trans (ξ.preimage_mono hBU))] at hV
  have key : valR ξ U g ^ m * (valR ξ B (resG Z hgO (d O h)) - D (valR ξ O h)) = 0 := by
    linear_combination hV
  rcases mul_eq_zero.1 key with h1 | h1
  · exact absurd (pow_eq_zero_iff'.1 h1).1 hg0
  · rw [← valR_res ξ hgO hξB]
    exact sub_eq_zero.1 h1

end GlobalTheory.LocVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalDerivationLiftingPrincipalPolarizationEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn.Vert
open GlobalTheory.KS

theorem transport {k : Type} [Field k] {R : Type} [CommRing R] (A : Over (Sp R)) (L : LB A.left)
    (A₀ B₀ : Over (Sp k)) (m₀ : A₀.left ⟶ A.left) (e : B₀.left ⟶ A₀.left) (he : e ≫ A₀.hom = B₀.hom)
    (D' : R → k) {J : Type} (V : J → A.left.Opens) (jj : J → L.ι)
    (v : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK A L A₀ m₀ D' V jj v q) :
    GlobalTheory.HeatConn.IsConnK A L B₀ (e ≫ m₀) D' V jj (fun W f => pbT e (v W f) ((e ≫ m₀) ⁻¹ᵁ W))
      (fun i => pbT e (q i) ((e ≫ m₀) ⁻¹ᵁ V i)) := by
  obtain ⟨hd, hcov, hle, htr⟩ := hc
  have le : ∀ W : A.left.Opens, (e ≫ m₀) ⁻¹ᵁ W ≤ e ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun W => le_rfl
  have app : ∀ W (f : Γ(A.left, W)), pbT e ((m₀.app W).hom f) ((e ≫ m₀) ⁻¹ᵁ W) = ((e ≫ m₀).app W).hom f := by
    intro W f
    rw [AdjDlog.app_eq_pbT m₀, AdjDlog.app_eq_pbT (e ≫ m₀), AdjDlog.pbT_pbT e m₀ le_rfl (le W)]
  refine ⟨⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, hcov, hle, fun i i' => ?_⟩
  · simp only [hd.add W le_top, pbT_add]
  · rw [hd.mul W le_top, pbT_add, pbT_mul, pbT_mul, app, app]
  · show pbT e (v W' (resG A.left h f)) _ = rsT (pbT e (v W f) _) _
    rw [hd.res W W' h le_top, pbT_rsT e (m₀.preimage_mono h) (le W'), rsT_pbT e (le W) ((e ≫ m₀).preimage_mono h)]
  · show pbT e (v W (constFn A.hom W r)) _ = _
    rw [hd.base W le_top, pbT_constFn A₀.hom e (le W), he]
  · show pbT e (v (V i ⊓ V i') _) _ = _
    rw [htr i i', pbT_mul, pbT_sub, AdjDlog.pbT_pbT e m₀ (m₀.preimage_mono (le_inf (inf_le_left.trans (hle i)) (inf_le_right.trans (hle i')))) (le _),
      pbT_rsT e (m₀.preimage_mono inf_le_left) (le _), pbT_rsT e (m₀.preimage_mono inf_le_right) (le _),
      rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_left), rsT_pbT e (le _) ((e ≫ m₀).preimage_mono inf_le_right)]

theorem coeff_const (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W))
    (hv : LocDerK P₀.A.hom P.A.hom θ (fun _ => (0 : k)) ⊤ v) :
    ∃ c : Fin n → k, ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f) := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  have hU : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top _
  obtain ⟨c0, hc0, -⟩ := GlobalTheory.KSUniq.coeff_id hs hu hdd (spMap x₀) P.A.hom θ hθ hU ⊤ (fun _ _ => trivial) v
    (fun W _ => hv.add W le_top) (fun W _ => hv.mul W le_top) (fun W W' h _ => hv.res W W' h le_top) (fun W _ r => by
      have e1 : pbT P.A.hom r W = constFn P.A.hom W ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
        rw [pbT_of_le _ (by simp)]
        simp [constFn]
      rw [e1, hv.base W le_top]
      simp [constFn])
  have hGF := GlobalTheory.allSixLaws.1.globalFns
  choose s hs' using fun a => (hGF _ P₀.A P₀.isAb).2 (rsT (c0 a) ⊤)
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (s a), fun W f => ?_⟩
  rw [hc0 W le_top f]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← rsT_rsT (O₁ := ⊤) (by simp) le_top, ← hs' a, rsT_of_le le_top]
  simp [constFn]
  rfl

theorem cob_of_conn (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R))
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left)
    {n : ℕ} (u : Fin n → (epsR k ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => θ ⁻¹ᵁ P.L.U i)) (hφ : IsDlog θ P.L dd φ) (hcoc : ∀ a, IsCoc _ (φ a))
    {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (c : Fin n → k)
    (hcv : ∀ W f, v W f = ∑ a, constFn P₀.A.hom (θ ⁻¹ᵁ W) (c a) * dd a (θ ⁻¹ᵁ W) ((θ.app W).hom f)) :
    IsCob _ (lc P₀.A.hom c φ) := by
  obtain ⟨-, hcov, hle, htr⟩ := hc
  have hres : ∀ a, ∀ W W' (f : Γ(P₀.A.left, W)), W' ≤ W → dd a W' (rsT f W') = rsT (dd a W f) W' :=
    fun a => ((GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).2 (dd a) (hdd a)).2.2.1
  have hcovθ : ⨆ p, θ ⁻¹ᵁ V p = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    have hz : θ z ∈ ⨆ i, V i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine _root_.GlobalTheory.KS.Refine.isCob_of_refine (fun i => θ ⁻¹ᵁ P.L.U i) (lc P₀.A.hom c φ) (GlobalTheory.KSUniq.isCoc_lc _ _ _ hcoc)
    (fun p => θ ⁻¹ᵁ V p) jj (fun p => θ.preimage_mono (hle p)) hcovθ q (fun p p' => ?_)
  have hWU : V p ⊓ V p' ≤ P.L.U (jj p) ⊓ P.L.U (jj p') := le_inf (inf_le_left.trans (hle p)) (inf_le_right.trans (hle p'))
  have hOU : θ ⁻¹ᵁ (V p ⊓ V p') ≤ θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p') := θ.preimage_mono hWU
  change rsT (lc P₀.A.hom c φ (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) =
    rsT (q p') (θ ⁻¹ᵁ (V p ⊓ V p')) - rsT (q p) (θ ⁻¹ᵁ (V p ⊓ V p'))
  have E := htr p p'
  rw [hcv] at E
  set g := (P.L.g (jj p) (jj p')).val with hg
  have r1 : rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) = pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) :=
    rsT_pbT θ (O₀ := P.L.U (jj p) ⊓ P.L.U (jj p')) (O₁ := θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p')) le_rfl hOU _
  have e1 : (θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p')) =
      rsT (pbT θ g (θ ⁻¹ᵁ P.L.U (jj p) ⊓ θ ⁻¹ᵁ P.L.U (jj p'))) (θ ⁻¹ᵁ (V p ⊓ V p')) := by
    rw [AdjDlog.app_eq_pbT, pbT_rsT θ hWU le_rfl, r1]
  have e2 : ∀ a, dd a (θ ⁻¹ᵁ (V p ⊓ V p')) ((θ.app (V p ⊓ V p')).hom (rsT g (V p ⊓ V p'))) =
      pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p')) * rsT (φ a (jj p) (jj p')) (θ ⁻¹ᵁ (V p ⊓ V p')) := fun a => by
    rw [e1, hres a _ _ _ hOU, ← hφ a (jj p) (jj p'), rsT_mul, r1]
  simp only [e2] at E
  have hunit : IsUnit (pbT θ g (θ ⁻¹ᵁ (V p ⊓ V p'))) := AdjDlog.isUnit_pbT θ (θ.preimage_mono hWU) _
  refine (hunit.mul_left_cancel ?_).symm
  rw [← E, lc, rsT_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_mul, rsT_constFn _ hOU]
  ring

theorem vert_polAV (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k)
    (P₀ : PolAV (Sp k)) (θ : P₀.A.left ⟶ P.A.left) (hθ : IsPullback θ P₀.A.hom P.A.hom (spMap x₀))
    (hiso : LBIso P₀.L (P.L.pull θ)) {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι)
    (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(P₀.A.left, θ ⁻¹ᵁ W)) (q : ∀ i, Γ(P₀.A.left, θ ⁻¹ᵁ V i))
    (hc : GlobalTheory.HeatConn.IsConnK P.A P.L P₀.A θ (fun _ => 0) V jj v q) (W : P.A.left.Opens) (f : Γ(P.A.left, W)) :
    v W f = 0 := by
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis P₀.A P₀.smoothDim
  choose dd hdd using fun a => (GlobalTheory.KS.InvField.main k P₀.A (u a) (hu.1 a)).1
  obtain ⟨⟨φ, hφ⟩, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent k P₀ P₀.g u dd hu hdd _ θ P.L P.isLB hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  obtain ⟨c, hcv⟩ := coeff_const k R P x₀ P₀ θ hθ u hu dd hdd v hc.1
  have c0 := hcob c (cob_of_conn k R P P₀ θ u hu dd hdd φ hφ hcoc V jj v q hc c hcv)
  rw [hcv]
  simp [c0, constFn]

theorem vert_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  intro k _ R _ P x₀ A₀ _ m₀ hm J V jj v q hc W f
  obtain ⟨P₀, θ, hθ, hiso⟩ := GlobalTheory.UniformisedModel.exists_polBaseChange GlobalTheory.allSixLaws.1.polBaseChange (spMap x₀) P
  obtain ⟨e, -, he⟩ := grpPullback_iso hθ hm
  subst he
  have hw : e.hom.left ≫ A₀.hom = P₀.A.hom := Over.w e.hom
  have hc' := transport P.A P.L A₀ P₀.A m₀ e.hom.left hw (fun _ => 0) V jj v q hc
  have h0 := vert_polAV k R P x₀ P₀ _ hθ.1 hiso V jj _ _ hc' W f
  haveI : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  have hle : m₀ ⁻¹ᵁ W ≤ (inv e.hom.left) ⁻¹ᵁ ((e.hom.left ≫ m₀) ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id_assoc]
  have key := congrArg (fun s => pbT (inv e.hom.left) s (m₀ ⁻¹ᵁ W)) h0
  rw [AdjDlog.pbT_pbT (inv e.hom.left) e.hom.left (U := m₀ ⁻¹ᵁ W) (V := (e.hom.left ≫ m₀) ⁻¹ᵁ W) le_rfl hle, IsIso.inv_hom_id, LinDir.pbT_id, pbT_zero] at key
  exact key

end GlobalTheory.HeatConn.Vert
end
end

