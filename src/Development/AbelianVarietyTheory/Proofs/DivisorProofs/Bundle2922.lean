module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSSymmAbLocus
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
namespace GlobalTheory.HeatV

theorem isKS_symm_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R), (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (c : R), c = ∏ i, tt i → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (dd' : Fin n → Fld t.G.left), (∀ a, IsInv t.G (v' a) (dd' a)) → ∀ (DV : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), IsKS t (GlobalTheory.HeatV.bo R c).1 (GlobalTheory.HeatV.bo R c) (fun a => spMap (dualMap (GlobalTheory.HeatV.resV R c)) ≫ (tv (v' a)).left) DV Θ₁ → Θ₁ᵀ = Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt htt hab c hc n v' dd' hinv DV Θ₁ hKS

  have hc' : spMap (resV R c) ≫ 𝟙 (Sp R) = chart (bo R c) := by
    rw [Category.comp_id]; exact spMap_resV R c
  obtain ⟨hv, hb⟩ : (∀ i, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
        (spMap (dualMap (resV R c)) ≫ (tv (v' i)).left)) ∧
      ∀ w, IsTanAtG t (spMap (resV R c) ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → Γ(Sp R, (bo R c).1), IsCombAtG t (spMap (resV R c) ≫ 𝟙 (Sp R))
          (fun i => spMap (dualMap (resV R c)) ≫ (tv (v' i)).left) a w := by
    refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t (resV R c) (𝟙 (Sp R)) n _
      (fun i => GlobalTheory.LieMet.isTan_tv (v' i)) ?_
    intro w hw
    refine ⟨v'.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
    · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
      rw [GlobalTheory.LieMet.isComb_iff]
      exact (v'.sum_repr _).symm
    · have h := (GlobalTheory.LieMet.isComb_iff v' a (GlobalTheory.LieMet.tanOf hw)).1 ha
      rw [h]
      ext i
      simp [Finsupp.single_apply]
  rw [hc'] at hv hb

  have hc0 : c ≠ 0 := by
    rw [hc]; exact Finset.prod_ne_zero_iff.2 fun i _ => htt i
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing R :=
    (algebraMap R (FractionRing R)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s = c := by simp [s]
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, RingHom.comp_apply, hs]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  have gg_inj : Function.Injective gg := by
    intro x y h
    have h1 := IsFractionRing.injective R (FractionRing R) h
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h1
  let x₀ : Γ(Sp R, (bo R c).1) →+* FractionRing R :=
    IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
  have hx₀ : ∀ y, x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) y) = gg y := by
    intro y
    show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu _ = _
    rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hinj : Function.Injective x₀ := by
    show Function.Injective (IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg x₀ h
      rwa [hx₀, hx₀] at this
    · intro h
      rw [gg_inj h]
  have hres : x₀.comp (resV R c) = algebraMap R (FractionRing R) := by
    ext r
    show x₀ (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [hx₀]
    simp [gg]
  have hsp : spMap x₀ ≫ chart (bo R c) = ReciprocityTheory.ChartRestriction.G.Out.jK R := by
    rw [← spMap_resV R c]
    show Spec.map (CommRingCat.ofHom x₀) ≫ Spec.map (CommRingCat.ofHom (resV R c)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
    rw [← hres, ← Spec.map_comp]
    rfl

  have gpG := GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left)
      (t.PP.L.pull (pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) _ P.U.gen.inv.left
          fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  have key := _root_.GlobalTheory.FibSym.map_transpose_eq E H (Sp R) t (bo R c).1 (bo R c) n _ hv hb (FractionRing R) x₀ P.A
    (P.U.gen.inv.left ≫ pullback.fst t.G.hom (ReciprocityTheory.ChartRestriction.G.Out.jK R)) (gpG.congr hsp.symm rfl) hL le_rfl DV Θ₁ hKS
  ext a b
  apply hinj
  have := congrFun (congrFun key a) b
  simpa [Matrix.transpose_apply, Matrix.map_apply] using this

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenousPDivGroupFinrankOmegaDual
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) : Submodule (WittVector p k) N where
  carrier := {m | ∃ n ∈ X, F n = m}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, X.add_mem ha hb, map_add F a b⟩
  zero_mem' := ⟨0, X.zero_mem, map_zero F⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
    refine ⟨d • a, X.smul_mem d ha, ?_⟩
    rw [map_smulₛₗ, WittVector.frobeniusEquiv_apply]

theorem mem_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (X : Submodule (WittVector p k) N) (m : N) : m ∈ frobImage F X ↔ ∃ n ∈ X, F n = m := Iff.rfl

theorem length_frobImage {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (hF : Function.Injective F)
    (X : Submodule (WittVector p k) N) :
    Module.length (WittVector p k)
        (frobImage F ⊤ ⧸ Submodule.comap (frobImage F ⊤).subtype (frobImage F X)) =
      Module.length (WittVector p k) (N ⧸ X) := by
  haveI : RingHomSurjective (WittVector.frobenius : WittVector p k →+* WittVector p k) :=
    ⟨fun c => by
      obtain ⟨d, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective c
      exact ⟨d, by rw [WittVector.frobeniusEquiv_apply]⟩⟩
  let f : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] frobImage F ⊤ :=
    LinearMap.codRestrict (frobImage F ⊤) F (fun c => ⟨c, Submodule.mem_top, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hF (congrArg Subtype.val h), ?_⟩
    rintro ⟨m, n, -, rfl⟩
    exact ⟨n, rfl⟩
  have hX : Submodule.orderIsoMapComapOfBijective f hf X =
      Submodule.comap (frobImage F ⊤).subtype (frobImage F X) := by
    ext ⟨m, hm⟩
    change (⟨m, hm⟩ : frobImage F ⊤) ∈ Submodule.map f X ↔ _
    rw [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, congrArg Subtype.val h⟩
    · rintro ⟨n, hn, h⟩
      exact ⟨n, hn, Subtype.ext h⟩
  rw [Module.length_quotient, Module.length_quotient, ← hX, Order.coheight_orderIso]

theorem finite_of_frob_surj {N U : Type} [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Finite (WittVector p k) N] [AddCommGroup U] [Module k U] (θ : N →+ U)
    (hθ : Function.Surjective θ)
    (hs : ∀ (a : WittVector p k) n, θ (WittVector.frobenius a • n) = WittVector.constantCoeff a • θ n) :
    Module.Finite k U := by
  classical
  obtain ⟨s, hs'⟩ := (Module.Finite.fg_top : (⊤ : Submodule (WittVector p k) N).FG)
  refine ⟨⟨s.image θ, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro u -
  obtain ⟨n, rfl⟩ := hθ u
  have hn : n ∈ Submodule.span (WittVector p k) (s : Set N) := hs' ▸ Submodule.mem_top
  induction hn using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    obtain ⟨b, rfl⟩ := (WittVector.frobeniusEquiv p k).surjective a
    rw [WittVector.frobeniusEquiv_apply, hs]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu.IsogDim

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem isog_core (T : GlobalTheory.Dieu.Theory p) {G H : PDivGroup p k} (q : G ⟶ H)
    (hq : IsIsog q) :
    Function.Injective (T.map q) ∧
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
    Module.finrank k G.omega = Module.finrank k H.omega := by
  obtain ⟨n, q', h1, h2⟩ := hq
  have huv : ∀ m : T.M G, T.map q (T.map q' m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← T.base.map_comp' trivial trivial trivial q q', h1,
      T.base.map_pow_smul trivial trivial, T.base.map_id' trivial, LinearMap.id_apply]
  have hvu : ∀ m : T.M H, T.map q' (T.map q m) = p ^ n • m := by
    intro m
    rw [← LinearMap.comp_apply, ← T.base.map_comp' trivial trivial trivial q' q, h2,
      T.base.map_pow_smul trivial trivial, T.base.map_id' trivial, LinearMap.id_apply]
  have hinj : Function.Injective (T.map q) := by
    intro a b hab
    have h := congrArg (T.map q') hab
    rw [hvu a, hvu b] at h
    have h0 : p ^ n • (a - b) = 0 := by rw [smul_sub, h, sub_self]
    exact sub_eq_zero.1 (T.base.eq_zero_of_pow_smul (G := H) trivial n _ h0)
  have LA := (_root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) (T.M H) (T.M G)).1 (T.map q) (T.map q') hinj
  have LB := (_root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) (T.M G) (T.M G)).2.1 (T.base.free G trivial)
    (T.base.finite G trivial) n (T.map q ∘ₗ T.map q') (fun a => huv a)
  rw [LB] at LA
  have hfin : Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ := by
    intro h
    rw [h, top_add] at LA
    exact ENat.natCast_ne_top _ LA
  refine ⟨hinj, hfin, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  have dimω : ∀ K : PDivGroup p k,
      Module.length (WittVector p k) (T.M K ⧸ frobImage (T.F K) ⊤) = Module.finrank k K.omega := by
    intro K
    obtain ⟨-, hs, hk, hl, -⟩ := hθ K
    haveI : Module.Finite (WittVector p k) (T.M K) := T.base.finite K trivial
    haveI := finite_of_frob_surj (θ K) hs hl
    refine (_root_.GlobalTheory.Dieu.length_ge_finrank_of_semilinear_surj p k (T.M K) K.omega (WittVector.frobeniusEquiv p k) (θ K) hs ?_
      (frobImage (T.F K) ⊤)).2 ?_
    · intro a m
      rw [WittVector.frobeniusEquiv_apply]
      exact hl a m
    · intro m
      rw [hk, mem_frobImage]
      constructor
      · rintro ⟨c, -, h⟩
        exact ⟨c, h.symm⟩
      · rintro ⟨c, h⟩
        exact ⟨c, Submodule.mem_top, h.symm⟩
  have hF : ∀ y : T.M H, T.map q (T.F H y) = T.F G (T.map q y) :=
    T.base.map_F trivial trivial q
  set X := LinearMap.range (T.map q) with hXdef
  set L3 := frobImage (T.F G) X with hL3
  set FG := frobImage (T.F G) ⊤ with hFG
  set FH := frobImage (T.F H) ⊤ with hFH
  have hle : L3 ≤ FG := by
    rintro m ⟨c, -, rfl⟩
    exact ⟨c, Submodule.mem_top, rfl⟩
  have hr1 : LinearMap.range (FG.subtype ∘ₗ (Submodule.comap FG.subtype L3).subtype) = L3 := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hle]
  have hr2 : LinearMap.range (T.map q ∘ₗ FH.subtype) = L3 := by
    ext m
    rw [LinearMap.mem_range, hL3, mem_frobImage]
    constructor
    · rintro ⟨⟨x, y, -, rfl⟩, rfl⟩
      exact ⟨T.map q y, LinearMap.mem_range.2 ⟨y, rfl⟩, (hF y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hz
      exact ⟨⟨T.F H y, y, Submodule.mem_top, rfl⟩, hF y⟩
  have eA := (_root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) FG (Submodule.comap FG.subtype L3)).1
    FG.subtype (Submodule.comap FG.subtype L3).subtype (Submodule.injective_subtype _)
  rw [hr1, Submodule.range_subtype, Submodule.range_subtype] at eA
  have eB := (_root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) (T.M H) FH).1 (T.map q) FH.subtype hinj
  rw [hr2, Submodule.range_subtype] at eB
  have hC : Module.length (WittVector p k) (FG ⧸ Submodule.comap FG.subtype L3) =
      Module.length (WittVector p k) (T.M G ⧸ X) :=
    length_frobImage (T.F G) (_root_.GlobalTheory.Dieu.theory_V_verschiebung p T k G).1 X
  rw [hC, hFG, dimω G] at eA
  rw [hFH, dimω H] at eB
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hd] at eA eB
  have h' : ((Module.finrank k G.omega + d : ℕ) : ℕ∞) = ((d + Module.finrank k H.omega : ℕ) : ℕ∞) := by
    push_cast
    exact eA.symm.trans eB
  have h'' := Nat.cast_injective h'
  omega

end GlobalTheory.Dieu.IsogDim

namespace GlobalTheory.Dieu

theorem isog_finrank_omega : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H),
    IsIsog q → Function.Injective (T.map q) ∧
      Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ≠ ⊤ ∧
      Module.finrank k G.omega = Module.finrank k H.omega ∧
      Module.finrank k G.dual.omega = Module.finrank k H.dual.omega := by
  intro p _ T k _ _ _ G H q hq
  obtain ⟨h1, h2, h3⟩ := IsogDim.isog_core T q hq
  obtain ⟨-, hd, -⟩ := GlobalTheory.T.pDivGroupIsogeny_height_eq_dual_sameDegree p k G H q hq
  exact ⟨h1, h2, h3, (IsogDim.isog_core T (dualHom G H q) hd).2.2.symm⟩

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaEvenDegenerationGlobalOfLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEvenGlue

theorem lbPow_U' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j : (lbPow M n).ι) : (lbPow M n).U j = M.U (j PUnit.unit) := by
  ext x
  simp only [lbPow, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h i => h⟩

theorem germ_lbPow_g' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j j' : (lbPow M n).ι) (x : S)
    (h : x ∈ (lbPow M n).U j ⊓ (lbPow M n).U j') (h' : x ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :
    S.presheaf.germ _ x h ((lbPow M n).g j j' : Γ(S, (lbPow M n).U j ⊓ (lbPow M n).U j')) =
      S.presheaf.germ _ x h' (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(S, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) ^ n := by
  simp only [lbPow, LB.LinComb, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  congr 1
  simp [res, pullU]
  erw [map_pow]
  congr 1
  erw [Units.coe_map, Units.coe_map]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem keyGlob_of_keyLoc : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → KeyGlob := by
  intro κ hH hF hL S s G _ _ g L δ σ hg hS hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI := hS
  obtain ⟨f, hloc, hcomp⟩ := _root_.GlobalTheory.KeyValsPf.keyVals κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  refine _root_.GlobalTheory.GlueRat.lbIso_of_rat S (lbPow δ 8) (lbPow (SiegelTor.hodge G g) 4) (fun p => f (p.1 PUnit.unit) (p.2 PUnit.unit)) ?_ ?_
  · rintro ⟨c, i⟩ x hx
    rw [lbPow_U', lbPow_U'] at hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hloc _ _ x hx
    exact ⟨V, by rw [lbPow_U', lbPow_U']; exact hV, hxV, u, hu⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h1 h2
    have h1' : genericPoint S ∈ (VB.det (LieVB.omega G) g).U (c PUnit.unit) ⊓ (VB.det (LieVB.omega G) g).U (c' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h1; exact h1
    have h2' : genericPoint S ∈ δ.U (i PUnit.unit) ⊓ δ.U (i' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h2; exact h2
    dsimp only
    rw [germ_lbPow_g' δ 8 i i' _ h2 h2', germ_lbPow_g' _ 4 c c' _ h1 h1']
    exact hcomp _ _ _ _ h1' h2'

end GlobalTheory.KeyEvenGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUniqueOverChartAbelianLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartKSUniq

theorem isKS_unique_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤)), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ' → Θ = Θ' := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _ n v hv hb D Θ Θ' h h'
  haveI : CharZero (ChartRing k m d) :=
    charZero_of_injective_algebraMap (R := k) (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d)))
  let φ : Γ(Sp (ChartRing k m d), ⊤) →+* FractionRing (ChartRing k m d) :=
    (algebraMap (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
  have hφ : Function.Injective φ := by
    exact (IsFractionRing.injective (ChartRing k m d) (FractionRing (ChartRing k m d))).comp
      (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).commRingCatIsoToRingEquiv.injective
  have hx : spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) = jK (ChartRing k m d) := by
    show spMap φ ≫ (isAffineOpen_top (Sp (ChartRing k m d))).fromSpec = _
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp [φ]
  set R := ChartRing k m d with hRdef
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) :=
    GlobalTheory.ThetaBaseChange.grp_generic P.U.toUnifPre
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
    have h := P.U.ext
    rw [P.bundle] at h
    exact h
  have hL : LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) := by
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull P.A.L _ hgi)
      (chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have hf : (∏ i, bdParam k m d i : R) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ h0 => by
      have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
      simp [bdParam, MvPowerSeries.coeff_X] at this
  have hV : ⊤ ≤ (spMap φ ≫ chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ
      (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, bdParam k m d i)) := by
    intro p _
    change (spMap φ) p ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen _
    rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen]
    show PrimeSpectrum.comap φ p ∈ PrimeSpectrum.basicOpen _
    rw [PrimeSpectrum.mem_basicOpen]
    show _ ∉ Ideal.comap φ p.asIdeal
    haveI := p.isPrime
    rw [Ideal.mem_comap, Ideal.eq_bot_of_prime p.asIdeal, Ideal.mem_bot]
    intro h0
    apply hf
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_zero, ← h0]
    show _ = algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom _))
    rw [Iso.inv_hom_id_apply]
  have key := _root_.GlobalTheory.KSPtUniq.isKS_unique_at_point E H (Sp R) t _ (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) n v hv hb
    (FractionRing R) φ P.A _ hV (by rw [hx]; exact gpG) hL _ Θ Θ' h h'
  ext a b
  exact hφ (congrFun₂ key a b)

end GlobalTheory.ChartKSUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqIntegralMatrixIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_vacuum_eq_integralMatrix_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToA G t i j w, IsMixModelA W B t e Γ w ι →
      ι (Γ.M.vac _) = ι (Γ.M.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  first | exact @GlobalTheory.MixVacBig.mix_vac | exact GlobalTheory.MixVacBig.mix_vac | (intros; apply GlobalTheory.MixVacBig.mix_vac <;> assumption)
end

