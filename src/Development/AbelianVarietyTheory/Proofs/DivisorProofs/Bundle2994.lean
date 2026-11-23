module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.ScaleTorus

theorem unitOn_mul' {R : Type} [CommRing R] (x y : Rˣ) : unitOn (x * y) = unitOn x * unitOn y := by
  apply Units.ext
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (x : R) (y : R)

theorem isUnitTau_scaleGen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C N s ε τ₀ hs hε hτ u hu a b
  obtain ⟨hgen, k, hk, hval⟩ := hτ a b
  set w : Rˣ := ∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) with hw
  let w' : (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom w
  have hw' : (w' : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s (.inr k)) ^
      ((l.M' : ℤ) • (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b := by
    simp only [w', hw, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
      LinearMap.smul_apply, smul_eq_mul, ← hu]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.scaleGen_isGen _ _ hgen, k * w'⁻¹, ?_, fun zz J hJ => ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_eq_iff_eq_mul₀ w'.ne_zero, hk, hw']
    refine (finSumFinEquiv.symm.prod_comp fun k => algebraMap R (FractionRing R) (s k) ^
      ((l.M' : ℤ) • (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [hs, hε]
  · have e₁ : val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen (unitOn w) (τ₀ a b)) (toUnit (TK R)).left zz J =
        gm (toUnit (TK R)).left zz ⊤ (unitOn w) * val (τ₀ a b) (toUnit (TK R)).left zz J :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ zz le_top (hJ.mem _ _) _) rfl)
    have e₂ : gm (toUnit (TK R)).left zz ⊤ (unitOn w) = gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      have e : (toUnit (TK R)).left = spMap (algebraMap R (FractionRing R)) := by simp
      rw [e]
      exact SepBModel.gm_spMap _ zz w
    have e₃ : gm (𝟙 (TK R).left) zz ⊤ (unitOn k) =
        gm (𝟙 (TK R).left) zz ⊤ (unitOn (k * w'⁻¹)) * gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      refine Eq.trans ?_ (map_mul _ _ _)
      refine congrArg _ (Eq.trans ?_ (unitOn_mul' _ _))
      rw [inv_mul_cancel_right]
    refine (hval zz J hJ).trans (Eq.trans ?_ (congrArg _ e₁.symm))
    rw [e₂, ← _root_.mul_assoc, ← e₃]

end GlobalTheory.UCanon.ScaleTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColength
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.ColengthDegree

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem map_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.map (f ≫ g) = T.map f ∘ₗ T.map g :=
  (_root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k X Y Z trivial trivial trivial).2.1 f g

theorem map_id (X : PDivGroup p k) : T.map (𝟙 X) = LinearMap.id :=
  (_root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k X X X trivial trivial trivial).1

theorem map_iso_bijective {X Y : PDivGroup p k} (i : X ≅ Y) : Function.Bijective (T.map i.hom) := by
  have e₁ : T.map i.inv ∘ₗ T.map i.hom = LinearMap.id := by rw [← map_comp, i.inv_hom_id, map_id]
  constructor
  · exact Function.LeftInverse.injective (g := T.map i.inv) fun a => congrArg (fun g => g a) e₁
  · intro a
    refine ⟨T.map i.inv a, ?_⟩
    have e : T.map i.hom ∘ₗ T.map i.inv = LinearMap.id := by rw [← map_comp, i.hom_inv_id, map_id]
    exact congrArg (fun g => g a) e

theorem colen_comp {X Y Z : PDivGroup p k} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : Function.Injective (T.map f)) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map (f ≫ g))) =
      Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map f)) +
        Module.length (WittVector p k) (T.M Y ⧸ LinearMap.range (T.map g)) := by
  rw [map_comp]
  exact (_root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M X) (T.M Y) (T.M Z)).1 _ _ hf

theorem colen_iso {X Y : PDivGroup p k} (i : X ≅ Y) :
    Module.length (WittVector p k) (T.M X ⧸ LinearMap.range (T.map i.hom)) = 0 := by
  rw [LinearMap.range_eq_top.2 (map_iso_bijective T i).2]
  exact Module.length_eq_zero_iff.2 inferInstance


omit [PerfectRing k p] in
theorem omegaMap_surjective_of_isIso {X Y : PDivGroup p k} (f : X ⟶ Y) [IsIso f] :
    Function.Surjective (omegaMap X Y f) := by
  intro w
  refine ⟨omegaMap Y X (inv f) w, ?_⟩
  rw [← LinearMap.comp_apply, ← omegaMap_comp, IsIso.hom_inv_id, omegaMap_id, LinearMap.id_apply]


omit [PerfectRing k p] in
theorem exists_step {X Y : PDivGroup p k} (f : X ⟶ Y) (hω : ¬ Function.Surjective (omegaMap X Y f)) :
    ∃ (Q : PDivGroup p k) (q₁ : X ⟶ Q) (q₁' : Q ⟶ X) (r : Q ⟶ Y),
      q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X ∧ q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q ∧
      frobKerIdeal p k (X.A 1) ≤ kerIdeal (q₁.app 1) ∧ q₁ ≫ r = f ∧
      ¬ Function.Surjective (omegaMap X Q q₁) := by
  obtain ⟨C, _, _, _, _, π, hπs, hker, -, hfrob⟩ := _root_.GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal p k X Y f
  obtain ⟨Q, q₁, q₁', h1, h2, hk1⟩ := _root_.GlobalTheory.HTPair.exists_quot_field p k X C π hπs
  have hle : kerIdeal (f.app 1) ≤ kerIdeal (q₁.app 1) := by rw [hk1, hker]; exact le_sup_left
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le p k X Q Y 1 q₁ q₁' f (by rw [pow_one]; exact h1)
    (by rw [pow_one]; exact h2) hle
  refine ⟨Q, q₁, q₁', r, h1, h2, by rw [hk1, hker]; exact le_sup_right, hr, ?_⟩
  intro hs
  apply hω
  have e1 := (_root_.GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap p k X Q q₁ C π hπs).2.1 (by rw [hk1]; exact le_sup_left) (by rw [hk1])
  have e2 := (_root_.GlobalTheory.PDivGroup.cot_kernel_eq_coker_omegaMap p k X Y f C π hπs).2.1 (by rw [hker]; exact sup_le_sup_left hfrob _)
    (by rw [hker]; exact le_sup_left)
  haveI := finite_omega_of_eq_zero (CharP.cast_eq_zero k p) X
  have h0 : Module.finrank k (X.omega ⧸ LinearMap.range (omegaMap X Q q₁)) = 0 := by
    rw [LinearMap.range_eq_top.2 hs]
    exact Module.finrank_zero_of_subsingleton
  rw [e1, ← e2] at h0
  have hsub := Module.finrank_zero_iff.1 h0
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)


omit [PerfectRing k p] in
theorem one_le_deg {X Q : PDivGroup p k} (q₁ : X ⟶ Q) (q₁' : Q ⟶ X)
    (h1 : q₁ ≫ q₁' = (p : ℤ_[p]) • 𝟙 X) (h2 : q₁' ≫ q₁ = (p : ℤ_[p]) • 𝟙 Q)
    (hns : ¬ Function.Surjective (omegaMap X Q q₁)) (e₁ : ℕ) (he₁ : HasLogDeg q₁ e₁) : 1 ≤ e₁ := by
  rcases Nat.eq_zero_or_pos e₁ with h | h
  · subst h
    have hI : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    haveI := ((_root_.GlobalTheory.Dieu.isog_basics p k X).2.2.2 Q q₁ hI).1 he₁
    exact absurd (omegaMap_surjective_of_isIso q₁) hns
  · exact h

theorem kernelDegree_le_dieudonneColength_of_colength_eq (n : ℕ) : ∀ (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = n → e ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G H q e hq he hn
  by_cases hA : Function.Surjective (omegaMap G H q)
  · by_cases hB : Function.Surjective (omegaMap H.dual G.dual (dualHom G H q))
    · haveI := _root_.GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective p k G H q hq hA hB
      have h0 : HasLogDeg q 0 := ((_root_.GlobalTheory.Dieu.isog_basics p k G).2.2.2 H q hq).2 inferInstance
      have := (_root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k G H q hq).unique he h0
      omega
    · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step (dualHom G H q) hB
      have hg := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
      have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
      have hrI : IsIsog r := (_root_.GlobalTheory.Dieu.isog_basics p k H.dual).2.2.1 Q G.dual q₁ r hq₁ (hr ▸ hg.2.1)
      obtain ⟨e₁, he₁⟩ := (_root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k H.dual Q q₁ hq₁).exists
      obtain ⟨e₂, he₂⟩ := (_root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k Q G.dual r hrI).exists
      have hle : e ≤ e₁ + e₂ :=
        _root_.GlobalTheory.Dieu.hasLogDeg_comp_le p k H.dual Q G.dual q₁ r e₁ e₂ e he₁ he₂ (hr ▸ hg.2.2 e he)
      have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
      have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k H.dual Q q₁ q₁' e₁ h1 h2 hfr he₁).2.1
      have hgr := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k Q G.dual r hrI
      have hg₁ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k H.dual Q q₁ hq₁
      have hcomp : dualHom _ _ (dualHom G H q) = dualHom Q G.dual r ≫ dualHom H.dual Q q₁ := by
        rw [← hr]; rfl
      have hlen : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) =
          Module.length (WittVector p k)
              (T.M G.dual.dual ⧸ LinearMap.range (T.map (dualHom Q G.dual r))) +
            Module.length (WittVector p k)
              (T.M Q.dual ⧸ LinearMap.range (T.map (dualHom H.dual Q q₁))) := by
        have a1 := colen_comp T G.bidual.hom (dualHom _ _ (dualHom G H q)) (map_iso_bijective T _).1
        have a2 := colen_comp T q H.bidual.hom (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k G H q hq).1
        rw [bidual_hom_dualHom_dualHom q, a2] at a1
        simp only [colen_iso, add_zero, zero_add] at a1
        rw [a1, hcomp, colen_comp T _ _ (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k _ _ _ hgr.2.1).1]
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k _ _ _ hgr.2.1).2.1
      obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k _ _ _ hg₁.2.1).2.1
      rw [← ha, ← hb] at hlen
      rw [← hb] at hL1
      rw [hlen] at hn
      have hab : a + b = n := by exact_mod_cast hn
      have hbe : e₁ ≤ b := by exact_mod_cast hL1
      have := ih a (by omega) _ _ (dualHom Q G.dual r) e₂ hgr.2.1 (hgr.2.2 e₂ he₂) ha.symm
      omega
  · obtain ⟨Q, q₁, q₁', r, h1, h2, hfr, hr, hns⟩ := exists_step q hA
    have hq₁ : IsIsog q₁ := ⟨1, q₁', by rw [pow_one]; exact h1, by rw [pow_one]; exact h2⟩
    have hrI : IsIsog r := (_root_.GlobalTheory.Dieu.isog_basics p k G).2.2.1 Q H q₁ r hq₁ (hr ▸ hq)
    obtain ⟨e₁, he₁⟩ := (_root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k G Q q₁ hq₁).exists
    obtain ⟨e₂, he₂⟩ := (_root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k Q H r hrI).exists
    have hle : e ≤ e₁ + e₂ := _root_.GlobalTheory.Dieu.hasLogDeg_comp_le p k G Q H q₁ r e₁ e₂ e he₁ he₂ (hr ▸ he)
    have h1e := one_le_deg q₁ q₁' h1 h2 hns e₁ he₁
    have hL1 := (GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne p T k G Q q₁ q₁' e₁ h1 h2 hfr he₁).1
    have hlen := colen_comp T q₁ r (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k G Q q₁ hq₁).1
    rw [hr] at hlen
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k G Q q₁ hq₁).2.1
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k Q H r hrI).2.1
    rw [← ha, ← hb] at hlen
    rw [← ha] at hL1
    rw [hlen] at hn
    have hab : a + b = n := by exact_mod_cast hn
    have hae : e₁ ≤ a := by exact_mod_cast hL1
    have := ih b (by omega) _ _ r e₂ hrI he₂ hb.symm
    omega

end GlobalTheory.Dieu.ColengthDegree

namespace GlobalTheory.Dieu

theorem le_length_coker_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (_root_.GlobalTheory.Dieu.isog_finrank_omega p T k G H q hq).2.1
  rw [← hn]
  exact_mod_cast ColengthDegree.kernelDegree_le_dieudonneColength_of_colength_eq T n G H q e hq he hn.symm

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfActionCompatibleMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.MatchBundle

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R]

theorem pull_one (D : DegPre R) (T : Over (Sp R)) : CechPic.pull (1 : T ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := by
  have h : CechPic.pull (eSec D.P.A) (cls D.P.L D.P.isLB) = 0 :=
    (cls_pull D.P.isLB _ (pull_isLB D.P.isLB _)).symm.trans
      ((cls_eq_zero_iff (pull_isLB D.P.isLB _)).2 ⟨D.rig, D.rig_gen⟩)
  have e : (1 : T ⟶ D.P.A).left = (toUnit T).left ≫ eSec D.P.A := rfl
  rw [e, pull_comp, h, map_zero]

theorem cls_eq_lam (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O)
    (h : TraceFormTwistIso D oa w0) : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) (oa.onB.act w0) := by
  obtain ⟨u, hu, -⟩ := h
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb D.P.isLB _ _)).2 ⟨u, hu⟩
  rw [cls_linComb D.P.isLB, Fin.sum_univ_four] at h₀
  have h₁ : (1 : ℤ) • CechPic.pull (𝟙 D.P.A * oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (-2 : ℤ) • CechPic.pull (𝟙 D.P.A.left) (cls D.P.L D.P.isLB) +
      (-1 : ℤ) • CechPic.pull (oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (2 : ℤ) • CechPic.pull (1 : D.P.A ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := h₀
  rw [lam, Over.id_left]
  rw [pull_one] at h₁ ⊢
  rw [pull_id] at h₁ ⊢
  linear_combination (norm := abel) -h₁

theorem cls_eq_lam_pull {V : Type} [CommRing V] [IsDomain V] {f : R →+* V} {D : DegPre R} {D' : DegPre V}
    (hD : IsPullDeg f D D') (a : D.P.A ⟶ D.P.A) (a' : D'.P.A ⟶ D'.P.A)
    (ha : a' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf f)).map a)
    (h : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) a) :
    cls D'.P.L D'.P.isLB = lam (cls D'.P.L D'.P.isLB) (𝟙 _) a' := by
  have gp := pull_grp hD
  have e : cls D'.P.L D'.P.isLB =
      CechPic.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f)) (cls D.P.L D.P.isLB) :=
    ((cls_eq_iff D'.P.isLB (pull_isLB D.P.isLB _)).2 ⟨hD.w, hD.w_gen⟩).trans (cls_pull D.P.isLB _ _)
  have p1 : (pushHom gp _ (𝟙 D'.P.A)).left = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f) := Category.id_comp _
  have q : pushHom gp _ a' = pushHom gp _ (𝟙 D'.P.A) ≫ a := Over.OverMorphism.ext (by
    rw [Over.comp_left, p1]
    have a₂ : ((Over.pullback (specOf f)).map a).left ≫ pullback.fst D.P.A.hom (specOf f) =
        pullback.fst _ _ ≫ a.left := pullback.lift_fst _ _ _
    show a'.left ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, ha, Over.comp_left, Category.assoc, a₂, Category.assoc])
  have k := congrArg (CechPic.pull (pushHom gp _ (𝟙 D'.P.A)).left) h
  rw [pull_lam, Category.comp_id, ← q, p1] at k
  rw [e, lam_pull_of_isGrpPullback gp]
  exact k

theorem lbIso_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → LBIso D₁.toPre.P.L (D₂.toPre.P.L.pull b.left) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C _ V _ _ _ _ _ f₁ f₂ _ _ _ _ D₁ D₂ hD₁ hD₂ _ _ b φ' _ _ hM hact
  letI := H.starRing
  obtain ⟨a₁, a₂, h₁, h₂, hb⟩ := hact H.w0
  have k := cls_eq_lam C.P.D.toPre C.P.oD H.w0 C.P.w0
  have k₁ := cls_eq_lam_pull hD₁ _ a₁ h₁ k
  have k₂ := cls_eq_lam_pull hD₂ _ a₂ h₂ k
  have hL₁ := D₁.toPre.P.isLB
  have hL₂ := D₂.toPre.P.isLB
  have i₁ : (abelian₂ D₁.toPre.P.A D₁.toPre.P.L).IsLB := LB.isLB_linComb hL₁ _ _
  have i₂ : (abelian₂ D₂.toPre.P.A D₂.toPre.P.L).IsLB := LB.isLB_linComb hL₂ _ _
  have m := ((cls_eq_iff i₁ (pull_isLB i₂ _)).2 hM.2.2.1).trans (cls_pull i₂ _ _)
  have c₁ : cls _ i₁ = lam (cls _ hL₁) (fst _ _) (snd _ _) := cls_cube_two hL₁ _ _ _
  have c₂ : cls _ i₂ = lam (cls _ hL₂) (fst _ _) (snd _ _) := cls_cube_two hL₂ _ _ _
  rw [c₁, c₂] at m
  have m' := congrArg (CechPic.pull (lift (𝟙 D₁.toPre.P.A) a₁).left) m
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp] at m'
  refine (cls_eq_iff hL₁ (pull_isLB hL₂ _)).1 ?_
  rw [cls_pull hL₂, k₁, m', hb]
  conv_rhs => rw [k₂, pull_lam, Category.comp_id]

end GlobalTheory.UCanon.MatchBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivCoordinateSubPotentialsConst
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
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem exists_const_of_glue : ∀ {K : Type} [Field K] (A₀ : Over (Sp K)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ {I : Type} (U : I → A₀.left.Opens) (f : ∀ i, Γ(A₀.left, U i)), ⨆ i, U i = ⊤ → (∀ i i', resG A₀.left (inf_le_left : U i ⊓ U i' ≤ U i) (f i) = resG A₀.left (inf_le_right : U i ⊓ U i' ≤ U i') (f i')) → ∃ c : K, ∀ (Z : Scheme.{0}) (b : Z ⟶ A₀.left) (z : Z) (i : I), b z ∈ U i → gs b z (U i) (f i) = cst (b ≫ A₀.hom) z c := by
  intro K _ A₀ _ hab I U f hcov hcomp
  obtain ⟨F, hF, -⟩ := A₀.left.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) (by rw [hcov]) f hcomp
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨s, hs⟩ := (hG (Sp K) A₀ hab).2 F
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom s, fun Z b z i hz => ?_⟩
  rw [cst, Iso.hom_inv_id_apply, ← gs_pull b A₀.hom z ⊤ trivial s, ← hF i]
  refine (gs_res b z (le_top : U i ≤ ⊤) hz F).trans ?_
  rw [← hs]
  rfl

theorem exists_coordEq : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α → ∃ c : K, CoordEq Y h ν m₀ V pb α c := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD α hfree
  obtain ⟨T, hT₁, hT₂⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
  have hT0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have hab : IsAbelianScheme A₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · haveI := Q.P.isAb.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hF.pull.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hF.pull.2 T x y (pushPt hF.pull.1.w x) (pushPt hF.pull.1.w y) rfl rfl,
        ← hF.pull.2 T y x (pushPt hF.pull.1.w y) (pushPt hF.pull.1.w x) rfl rfl, _root_.mul_comm]
    · exact MorphismProperty.of_isPullback (P := @Smooth) hF.pull.1 Q.P.isAb.smooth
    · exact MorphismProperty.of_isPullback (P := @IsProper) hF.pull.1 Q.P.isAb.proper
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hF.pull.1 Q.P.isAb.geomConnected
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hC.2.2.1
  let U : (Fin 4 → h.J) → Q.P.A.left.Opens := fun i =>
    V (i 0) ⊓ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j))
  have hU : ∀ i, Y.q.left ⁻¹ᵁ U i ≤ h.W (i 0) ⊓ xU Y α (fun j => h.j (i j)) := by
    intro i y hy
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · rw [hD.1]; exact hy.1
    · have := Set.mem_iInter.1 hy.2 (![1, 2, 0, 3] k)
      show y ∈ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k ⁻¹ᵁ Q.P.L.U (h.j (i (![1, 2, 0, 3] k)))
      rw [gtφT_eq, Scheme.Hom.comp_preimage]
      exact this
  have exA : ∀ i : Fin 4 → h.J, ∃ A : Γ(Q.P.A.left, U i), (Y.q.left.app (U i)).hom A *
      rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
      dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) := fun i =>
    _root_.GlobalTheory.HeatConn.LogDerDesc.exists_app_mul_eq_dE Y h ν hF.wt hF.basic (i 0) α (U i) ((hU i).trans inf_le_left) _
      (by rw [GlobalTheory.KS.GlueDer.rsT_eq ((hU i).trans inf_le_right)]; exact (Units.isUnit _).map _)
      (_root_.GlobalTheory.HeatConn.CoordWt.isWt_xc Y α _ _ ((hU i).trans inf_le_right))
  choose A hA using exA
  let Oi : (Fin 4 → h.J) → A₀.left.Opens := fun i =>
    T 0 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 0)) ⊓ T 1 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 1)) ⊓ T 2 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 2)) ⊓ T 3 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 3))
  have memO : ∀ i (p : A₀.left), p ∈ Oi i ↔ ∀ j, m₀ (T j p) ∈ V (i j) := by
    intro i p
    constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ j
      fin_cases j
      exacts [h0, h1, h2, h3]
    · intro H
      exact ⟨⟨⟨H 0, H 1⟩, H 2⟩, H 3⟩
  have hOU : ∀ i, Oi i ≤ m₀ ⁻¹ᵁ U i := by
    intro i p hp
    have H := (memO i p).1 hp
    refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
    · have := H 0
      rw [hT0] at this
      exact this
    · have := hV _ (H k)
      rw [← Scheme.Hom.comp_apply, hT₁ k, Scheme.Hom.comp_apply] at this
      exact this
  have hOT : ∀ i j, Oi i ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j)) := fun i j p hp => (memO i p).1 hp j
  let f : ∀ i, Γ(A₀.left, Oi i) := fun i =>
    pbT m₀ (A i) (Oi i) + pbT (T 0) (pb (i 0)) (Oi i) - pbT (T 1) (pb (i 1)) (Oi i) +
      pbT (T 2) (pb (i 2)) (Oi i) - pbT (T 3) (pb (i 3)) (Oi i)
  have hCA : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ z, b z ∈ Oi i →
      CoordAt Y h ν m₀ V pb α i T a b z (gs b z (Oi i) (f i)) := by
    intro i Z a b w z hz
    have hza : a z ∈ Y.q.left ⁻¹ᵁ U i := by
      show Y.q.left (a z) ∈ U i
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
      exact hOU i hz
    have e1 : rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i) =
        resG _ (hU i) (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
      rw [← GlobalTheory.KS.GlueDer.rsT_eq (hU i)]
      refine fn_ext fun y hy => ?_
      rw [gs_rsT (𝟙 _) y ((hU i).trans inf_le_right) hy, gs_rsT (𝟙 _) y (hU i) hy,
        gs_rsT (𝟙 _) y inf_le_right (hU i hy)]
    have e2 : dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (Y.q.left ⁻¹ᵁ U i)) =
        resG _ (hU i) (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) := by
      rw [e1]
      exact (isField_dE h ν hF.field (i 0)).2.2 _ _ (hU i) inf_le_left _
    have lhs : gs a z (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
        (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) =
        gs (b ≫ m₀) z (U i) (A i) * gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val := by
      rw [← gs_res a z (hU i) hza, ← e2, ← hA i, gs_mul a z _ hza, gs_rsT a z ((hU i).trans inf_le_right) hza,
        gs_pull a Y.q.left z (U i) hza, w]
    have rhs : gs b z (Oi i) (f i) = gs (b ≫ m₀) z (U i) (A i) +
        gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) - gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) +
        gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) - gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) := by
      simp only [f, gs_add b z _ hz, gs_sub b z _ hz, gs_pbT b m₀ z (hOU i) hz, gs_pbT b (T _) z (hOT i _) hz]
    unfold CoordAt
    rw [lhs, rhs]
    ring
  have uniq : ∀ i (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left) (z : Z) (w₁ w₂ : Z.presheaf.stalk z),
      a z ∈ xU Y α (fun j => h.j (i j)) → CoordAt Y h ν m₀ V pb α i T a b z w₁ →
      CoordAt Y h ν m₀ V pb α i T a b z w₂ → w₁ = w₂ := by
    intro i Z a b z w₁ w₂ hm h₁ h₂
    unfold CoordAt at h₁ h₂
    rw [h₁, gs_unit a z _ hm] at h₂
    exact add_left_cancel ((Units.isUnit _).mul_left_cancel h₂)
  have hover : ∀ i i', resG A₀.left (inf_le_left : Oi i ⊓ Oi i' ≤ Oi i) (f i) =
      resG A₀.left (inf_le_right : Oi i ⊓ Oi i' ≤ Oi i') (f i') := by
    intro i i'
    refine ext_lift Y m₀ fun Z a b w z hz => ?_
    rw [gs_res b z inf_le_left hz, gs_res b z inf_le_right hz]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => (memO i (b z)).1 hz.1 j
    have hi' : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i' j) := fun j => (memO i' (b z)).1 hz.2 j
    have h₁ := hfree T hT₁ hT₂ Z a b w z i i' hi hi' _ (hCA i Z a b w z hz.1)
    exact uniq i' Z a b z _ _ (hF.mem_chart hD hV hT₁ w hi').2 h₁ (hCA i' Z a b w z hz.2)
  have hcov : ⨆ i, Oi i = ⊤ := by
    refine eq_top_iff.2 fun p _ => ?_
    have ex : ∀ j, ∃ k, m₀ (T j p) ∈ V k := fun j => by
      have : m₀ (T j p) ∈ (⨆ k, V k) := by rw [hC.2.1]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    choose i hi using ex
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (memO i p).2 hi⟩
  obtain ⟨c, hc⟩ := exists_const_of_glue A₀ hab Oi f hcov hover
  refine ⟨c, fun T' hT'₁ hT'₂ Z a b w z i hi => ?_⟩
  obtain rfl : T' = T := funext fun j =>
    hF.pull.1.hom_ext ((hT'₁ j).trans (hT₁ j).symm) ((hT'₂ j).trans (hT₂ j).symm)
  have hz : b z ∈ Oi i := (memO i (b z)).2 hi
  rw [← hc Z b z i hz]
  exact hCA i Z a b w z hz

end GlobalTheory.HeatConn
end
end

