module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormStepIntegrality
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.OrbFinAf
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem normStep_isIntV_add {G : HTGroup p} {v : AwayP p} {y z : Qv v ⊗[ℚ] G.C} (hy : IsIntV G v y)
    (hz : IsIntV G v z) : IsIntV G v (y + z) := by
  intro i; rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hy i) (hz i)

theorem normStep_isIntV_neg {G : HTGroup p} {v : AwayP p} {y : Qv v ⊗[ℚ] G.C} (hy : IsIntV G v y) :
    IsIntV G v (-y) := by
  intro i; rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hy i)

theorem normStep_isIntV_zero {G : HTGroup p} {v : AwayP p} : IsIntV G v 0 := by
  intro i; rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem normStep_isIntV_smul {G : HTGroup p} {v : AwayP p} {r : Qv v} {y : Qv v ⊗[ℚ] G.C}
    (hr : r ∈ v.1.adicCompletionIntegers ℚ) (hy : IsIntV G v y) : IsIntV G v (r • y) := by
  intro i; rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hr (hy i)

theorem normStep_star_star (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y : R ⊗[ℚ] G.C) :
    (starT G.star R (starT G.star R y).unop).unop = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem normStep_star_mul (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (y z : R ⊗[ℚ] G.C) :
    (starT G.star R (y * z)).unop = (starT G.star R z).unop * (starT G.star R y).unop := by
  rw [map_mul, MulOpposite.unop_mul]

theorem normStep_star_comm (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ) (c : (Qv v)ˣ)
    (hg : (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c)
    (y : Qv v ⊗[ℚ] G.C) (hy : y * g = g * y) :
    (starT G.star (Qv v) y).unop * g = g * (starT G.star (Qv v) y).unop := by
  set yh := (starT G.star (Qv v) y).unop with hyh
  set gh := (starT G.star (Qv v) (g : Qv v ⊗[ℚ] G.C)).unop with hgh
  set cc := algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c with hcc'
  have key : gh * yh = yh * gh := by
    have := congrArg (fun x => (starT G.star (Qv v) x).unop) hy
    simpa only [normStep_star_mul] using this
  have hgi : gh = (↑g⁻¹ : Qv v ⊗[ℚ] G.C) * cc := by rw [← hg, ← mul_assoc, Units.inv_mul, one_mul]
  have hcu : IsUnit cc := c.isUnit.map _
  have hcc : ∀ x, cc * x = x * cc := fun x => Algebra.commutes _ _
  have h1 : yh * (↑g⁻¹ : Qv v ⊗[ℚ] G.C) = ↑g⁻¹ * yh := by
    apply hcu.mul_left_injective
    show yh * ↑g⁻¹ * cc = ↑g⁻¹ * yh * cc
    calc yh * ↑g⁻¹ * cc = yh * gh := by rw [hgi, mul_assoc]
      _ = gh * yh := key.symm
      _ = ↑g⁻¹ * yh * cc := by rw [hgi, mul_assoc, mul_assoc, hcc yh]
  calc yh * ↑g = ↑g * (↑g⁻¹ * yh) * ↑g := by rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = ↑g * (yh * ↑g⁻¹) * ↑g := by rw [h1]
    _ = ↑g * yh := by rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem normStep_exists (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (g : (Qv v ⊗[ℚ] G.C)ˣ)
    (c : (Qv v)ˣ)
    (hg : (g : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) g).unop = algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) c)
    (h1 : IsIntV G v 1)
    (hmul : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z))
    (hstar : ∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop)
    (hcomm : ∀ y z : Qv v ⊗[ℚ] G.C, y * g = g * y → z * g = g * z → y * z = z * y)
    (θ θ' h : Qv v ⊗[ℚ] G.C) (hθg : θ * g = g * θ) (hθ'g : θ' * g = g * θ') (hhg : h * g = g * h)
    (hθi : IsIntV G v θ) (hθ'i : IsIntV G v θ') (hhi : IsIntV G v h)
    (hθθ' : (θ - (starT G.star (Qv v) θ).unop) * θ' = 1) (h2 : 2 * h = 1)
    (s : (Qv v ⊗[ℚ] G.C)ˣ) (hsg : s * g = g * s) (hsi : IsIntV G v (s : Qv v ⊗[ℚ] G.C))
    (hsii : IsIntV G v ((s⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))
    (hsfix : (starT G.star (Qv v) s).unop = s) :
    ∃ u : (Qv v ⊗[ℚ] G.C)ˣ, u * g = g * u ∧ IsIntV G v (u : Qv v ⊗[ℚ] G.C) ∧
      IsIntV G v ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
      (u : Qv v ⊗[ℚ] G.C) * (starT G.star (Qv v) u).unop = s := by
  classical
  let A : Subring (Qv v ⊗[ℚ] G.C) :=
    { carrier := {y | y * g = g * y ∧ IsIntV G v y}
      mul_mem' := fun {a b} ha hb => ⟨Commute.mul_left ha.1 hb.1, hmul _ _ ha.2 hb.2⟩
      one_mem' := ⟨Commute.one_left _, h1⟩
      add_mem' := fun {a b} ha hb => ⟨Commute.add_left ha.1 hb.1, normStep_isIntV_add ha.2 hb.2⟩
      zero_mem' := ⟨Commute.zero_left _, normStep_isIntV_zero⟩
      neg_mem' := fun {a} ha => ⟨Commute.neg_left ha.1, normStep_isIntV_neg ha.2⟩ }
  letI : CommRing A :=
    { (inferInstance : Ring A) with mul_comm := fun a b => Subtype.ext (hcomm _ _ a.2.1 b.2.1) }
  have hτmem : ∀ y ∈ A, (starT G.star (Qv v) y).unop ∈ A := fun y hy =>
    ⟨normStep_star_comm G v g c hg y hy.1, hstar y hy.2⟩
  let τ : A →+* A :=
    { toFun := fun y => ⟨(starT G.star (Qv v) y).unop, hτmem y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (starT G.star (Qv v) ((a : Qv v ⊗[ℚ] G.C) * b)).unop =
          (starT G.star (Qv v) a).unop * (starT G.star (Qv v) b).unop
        rw [normStep_star_mul]; exact hcomm _ _ (hτmem b b.2).1 (hτmem a a.2).1)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by
        show (starT G.star (Qv v) ((a : Qv v ⊗[ℚ] G.C) + b)).unop =
          (starT G.star (Qv v) a).unop + (starT G.star (Qv v) b).unop
        rw [map_add (f := _), MulOpposite.unop_add]) }
  have hτinv : ∀ a, τ (τ a) = a := fun a => Subtype.ext (normStep_star_star G (Qv v) a)
  let O := v.1.adicCompletionIntegers ℚ
  let φ : O →+* A := ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (algebraMap O (Qv v))).codRestrict A
    (fun r => ⟨Algebra.commutes _ _, by
      show IsIntV G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (algebraMap O (Qv v) r))
      rw [Algebra.algebraMap_eq_smul_one]
      exact normStep_isIntV_smul r.2 h1⟩)
  letI : Algebra O A := φ.toAlgebra
  let cf : A →ₗ[O] (Fin (Module.finrank ℚ G.C) → O) :=
    { toFun := fun y i => ⟨(basV G v).repr (y : Qv v ⊗[ℚ] G.C) i, y.2.2 i⟩
      map_add' := fun a b => by
        funext i; apply Subtype.ext
        show (basV G v).repr ((a : Qv v ⊗[ℚ] G.C) + b) i = (basV G v).repr a i + (basV G v).repr b i
        rw [map_add (f := _), Finsupp.add_apply]
      map_smul' := fun r a => by
        funext i; apply Subtype.ext
        show (basV G v).repr (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (algebraMap O (Qv v) r) * a) i =
          (r : Qv v) * (basV G v).repr a i
        rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
        rfl }
  have hinj : Function.Injective cf := by
    intro a b hab
    apply Subtype.ext
    apply (basV G v).repr.injective
    exact Finsupp.ext fun i => congrArg (fun f => ((f i : O) : Qv v)) hab
  haveI : Module.Finite O A := Module.Finite.of_injective cf hinj
  obtain ⟨hhen, hfin⟩ := GlobalTheory.T.padicIntegers_henselian_finiteResidue v.1
  haveI := hhen
  haveI := hfin
  let θA : A := ⟨θ, hθg, hθi⟩
  have hθu : IsUnit (θA - τ θA) := IsUnit.of_mul_eq_one (a := θA - τ θA) (⟨θ', hθ'g, hθ'i⟩ : A) (Subtype.ext hθθ')
  have hsg' : s⁻¹ * g = g * s⁻¹ := Commute.inv_left hsg
  let sA : A := ⟨s, congrArg Units.val hsg, hsi⟩
  let siA : A := ⟨↑s⁻¹, congrArg Units.val hsg', hsii⟩
  have hsu : IsUnit sA := IsUnit.of_mul_eq_one (a := sA) siA (Subtype.ext s.mul_inv)
  have hτs : τ sA = sA := Subtype.ext hsfix
  obtain ⟨t₀, ht₀, ht₀J⟩ := GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson O A τ hτinv θA hθu sA hsu hτs
  haveI : HenselianRing A (⊥ : Ideal A).jacobson := GlobalTheory.henselianRing_of_finite O _ le_rfl
  have hτJ : ∀ a ∈ (⊥ : Ideal A).jacobson, τ a ∈ (⊥ : Ideal A).jacobson := by
    intro a ha
    rw [Ideal.mem_jacobson_bot] at ha ⊢
    intro b
    have := (ha (τ b)).map τ
    rwa [τ.map_add, τ.map_mul, hτinv, τ.map_one] at this
  have h2A : IsUnit (2 : A) := IsUnit.of_mul_eq_one (a := (2 : A)) (⟨h, hhg, hhi⟩ : A) (Subtype.ext (by
    show ((2 : A) : Qv v ⊗[ℚ] G.C) * h = 1
    rw [show ((2 : A) : Qv v ⊗[ℚ] G.C) = 2 from map_ofNat A.subtype 2]
    exact h2))
  obtain ⟨t, ht, htt⟩ := GlobalTheory.T.henselian_norm_lift A _ τ hτinv h2A hτJ sA t₀ hsu hτs ht₀ ht₀J
  refine ⟨Units.map (A.subtype : A →* Qv v ⊗[ℚ] G.C) ht.unit, ?_, ?_, ?_, ?_⟩
  · exact Units.ext t.2.1
  · exact t.2.2
  · exact ((ht.unit⁻¹ : Aˣ) : A).2.2
  · exact congrArg Subtype.val htt

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllComparison
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.OneMapAllCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory CategoryTheory.Hom.group in
theorem levR_congr (c : Coeff l) (hA : l.A = 1) {p q : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ a, p.1 a - q.1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) : levR p y y' ↔ levR q y y' := by
  have e : ∀ a, Xo.univ.eta (p.1 a) = Xo.univ.eta (q.1 a) := fun a => by
    rw [← sub_add_cancel (p.1 a) (q.1 a), Xo.univ.eta_add, Xo.univ.eta_ker _ (h a), one_mul]
  have e1 : ∀ a, Xo.univ.etaA a = 1 := fun a => by
    have := Xo.univ.etaA_ker a
    rwa [hA, one_smul] at this
  unfold levR IsLevMove
  simp only [e, e1]

variable {G : Type} [Group G] {lev lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem rel_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_congr c hA (h g) y y')

theorem actLev_congr (c : Coeff l) (hA : l.A = 1)
    (h : ∀ g a, (lev g).1 a - (lev' g).1 a ∈ l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)) :
    actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [rel_congr c hA h]

theorem second_level_eq_one {c : Coeff l} {n : ℕ} {Tup : Type} {dδ : Tup → DeltaDat Xo c n} (h : CovPin Xo c dδ) (t : Tup) :
    l.A = 1 := by
  have h1 := (h t).1.1.2.2
  rw [(h t).2.1] at h1
  exact Nat.dvd_one.1 h1

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def TypeCoprime : Prop :=
  ∀ PP ∈ R.Pg, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal






def LevUnique (i : Fin D.R.m) : Prop :=
  ∀ lev lev' : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev' →
      ∀ g a, lev g a - lev' g a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw ((i : ℕ) + 1)).La)

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

variable {T R κ v₀ O ph}

variable (T R κ v₀ O ph)

end GlobalTheory.OneMapAllCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumVanishesOfParabolicSums
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_vanishes_of_parabolic_sums : ∀ (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ), T ≤ P →
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  (∀ y : H, GlobalTheory.OrbDesc.dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_par  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumsOverConjugacyClasses
section
open MulAction

namespace GlobalTheory.OrbitUnfold

section Restrict

variable {G Y Y' : Type} [Group G] [MulAction G Y] [MulAction G Y']

theorem out_mk_mem_orbit (x : Y) :
    Quotient.out (Quotient.mk (orbitRel G Y) x) ∈ orbit G x :=
  orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G Y) x)

theorem injective_mk_comp_out (i : Y' → Y) (hi : Function.Injective i)
    (heq : ∀ (η : G) (y : Y'), i (η • y) = η • i y) :
    Function.Injective (fun o : orbitRel.Quotient G Y' =>
      (Quotient.mk (orbitRel G Y) (i (Quotient.out o)) : orbitRel.Quotient G Y)) := by
  intro o₁ o₂ h
  have h' : i (Quotient.out o₁) ∈ orbit G (i (Quotient.out o₂)) :=
    orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨η, hη⟩ := h'
  simp only at hη
  rw [← heq] at hη
  have h2 := hi hη
  rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂]
  exact Quotient.sound (orbitRel_apply.mpr ⟨η, h2⟩)

theorem finsum_orbits_restrict (i : Y' → Y) (hi : Function.Injective i)
    (heq : ∀ (η : G) (y : Y'), i (η • y) = η • i y) (g : Y → ℂ) (g' : Y' → ℂ)
    (hgg : ∀ y, g' y = g (i y)) (hg : ∀ (η : G) (y : Y), g (η • y) = g y)
    (h0 : ∀ y, g y ≠ 0 → y ∈ Set.range i) :
    ∑ᶠ o : orbitRel.Quotient G Y, g (Quotient.out o) =
      ∑ᶠ o : orbitRel.Quotient G Y', g' (Quotient.out o) := by
  have hgo : ∀ x : Y, g (Quotient.out (Quotient.mk (orbitRel G Y) x)) = g x := by
    intro x
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := G) x
    simp only at hη
    rw [← hη, hg]
  have hφ := injective_mk_comp_out i hi heq
  have hsupp : Function.support (fun o : orbitRel.Quotient G Y => g (Quotient.out o)) ⊆
      Set.range (fun o : orbitRel.Quotient G Y' =>
        (Quotient.mk (orbitRel G Y) (i (Quotient.out o)) : orbitRel.Quotient G Y)) := by
    intro o ho
    obtain ⟨y, hy⟩ := h0 _ ho
    refine ⟨Quotient.mk (orbitRel G Y') y, ?_⟩
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := G) y
    simp only at hη
    show Quotient.mk (orbitRel G Y) (i (Quotient.out (Quotient.mk (orbitRel G Y') y))) = o
    rw [← hη, heq, hy]
    conv_rhs => rw [← Quotient.out_eq o]
    exact Quotient.sound (orbitRel_apply.mpr (mem_orbit _ _))
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ _
    (fun x hx => ⟨fun _ => hsupp hx, fun _ => trivial⟩), finsum_mem_range hφ]
  exact finsum_congr fun o => by rw [hgo, hgg]

end Restrict

section Stab

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

def finiteStabilizerSubMulAction (Γ Y : Type) [Group Γ] [MulAction Γ Y] : SubMulAction Γ Y where
  carrier := {y | (stabilizer Γ y : Set Γ).Finite}
  smul_mem' η y hy := by
    show (stabilizer Γ (η • y) : Set Γ).Finite
    rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.coe_map]
    exact Set.Finite.image _ hy

theorem mem_stabilizer_conj_iff (η x : Γ) (y : Y) :
    x ∈ stabilizer Γ y ↔ η * x * η⁻¹ ∈ stabilizer Γ (η • y) := by
  simp only [mem_stabilizer_iff, mul_smul, inv_smul_smul]
  exact (smul_left_cancel_iff η).symm

theorem natCard_stabilizer_inf_smul (K : Subgroup Γ) (η : Γ) (hK : ∀ x, x ∈ K ↔ η * x * η⁻¹ ∈ K)
    (y : Y) : Nat.card (stabilizer Γ (η • y) ⊓ K : Subgroup Γ) = Nat.card (stabilizer Γ y ⊓ K : Subgroup Γ) := by
  symm
  refine Nat.card_congr ((MulAut.conj η).toEquiv.subtypeEquiv fun x => ?_)
  simp only [Subgroup.mem_inf, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [mem_stabilizer_conj_iff η x y, hK x]

theorem natCard_stabilizer_smul (η : Γ) (y : Y) :
    Nat.card (stabilizer Γ (η • y)) = Nat.card (stabilizer Γ y) := by
  symm
  refine Nat.card_congr ((MulAut.conj η).toEquiv.subtypeEquiv fun x => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  exact mem_stabilizer_conj_iff η x y

theorem mem_iff_conj_mem (K : Subgroup Γ) {η : Γ} (hη : η ∈ K) (x : Γ) :
    x ∈ K ↔ η * x * η⁻¹ ∈ K := by
  constructor
  · intro h; exact K.mul_mem (K.mul_mem hη h) (K.inv_mem hη)
  · intro h
    have := K.mul_mem (K.mul_mem (K.inv_mem hη) h) hη
    simpa [mul_assoc] using this

theorem stabilizer_inf_centralizer_infinite (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hs : (Function.support (F y)).Finite) (c : Γ) (hc : F y c ≠ 0)
    (hinf : (stabilizer Γ y : Set Γ).Infinite) :
    ((stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : Set Γ).Infinite := by
  haveI : Infinite (stabilizer Γ y) := hinf.to_subtype
  haveI : Finite (Function.support (F y)) := hs.to_subtype
  let f : stabilizer Γ y → Function.support (F y) := fun η =>
    ⟨(η : Γ) * c * (η : Γ)⁻¹, by
      show F y _ ≠ 0
      have h1 : (η : Γ) • y = y := η.2
      have := hF η y c
      rw [h1] at this
      rw [this]; exact hc⟩
  obtain ⟨z, hz⟩ := Finite.exists_infinite_fiber f
  obtain ⟨⟨η₀, hη₀⟩⟩ : Nonempty ↑(f ⁻¹' {z}) := inferInstance
  refine Set.infinite_of_injective_forall_mem (α := ↑(f ⁻¹' {z}))
    (f := fun η => (η₀ : Γ)⁻¹ * ((η : stabilizer Γ y) : Γ)) ?_ ?_
  · intro a b hab
    have : ((a : stabilizer Γ y) : Γ) = ((b : stabilizer Γ y) : Γ) := mul_left_cancel hab
    exact Subtype.ext (Subtype.ext this)
  · intro ⟨η, hη⟩
    have E : (η : Γ) * c * (η : Γ)⁻¹ = (η₀ : Γ) * c * (η₀ : Γ)⁻¹ := by
      have h1 : f η = z := hη
      have h2 : f η₀ = z := hη₀
      have := congrArg Subtype.val (h1.trans h2.symm)
      exact this
    refine Subgroup.mem_inf.mpr ⟨(stabilizer Γ y).mul_mem ((stabilizer Γ y).inv_mem η₀.2) η.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h2 : (η₀ : Γ)⁻¹ * ((η : Γ) * h * (η : Γ)⁻¹) * η = (η₀ : Γ)⁻¹ * ((η₀ : Γ) * h * (η₀ : Γ)⁻¹) * η := by
      rw [E]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h2
    simp only [mul_assoc]
    exact h2.symm

end Stab

theorem finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  intro Γ Y _ _ F hF hs ho
  let S := finiteStabilizerSubMulAction Γ Y
  have hstabS : ∀ y : S, stabilizer Γ y = stabilizer Γ (y : Y) := fun y =>
    SubMulAction.stabilizer_of_subMul y
  have hF' : ∀ (η : Γ) (y : S) (γ : Γ), F ((η • y : S) : Y) (η * γ * η⁻¹) = F (y : Y) γ :=
    fun η y γ => hF η y γ
  have hst' : ∀ y : S, (stabilizer Γ y : Set Γ).Finite := fun y => by rw [hstabS]; exact y.2
  have hs' : ∀ y : S, (Function.support (fun γ => F (y : Y) γ)).Finite := fun y => hs y
  have ho' : {o : orbitRel.Quotient Γ S | ∃ γ, F ((Quotient.out o : S) : Y) γ ≠ 0}.Finite := by
    have hφ := injective_mk_comp_out (G := Γ) (Y := Y) (Y' := S) Subtype.val
      Subtype.val_injective (fun _ _ => rfl)
    refine (ho.preimage hφ.injOn).subset ?_
    rintro o ⟨γ, hγ⟩
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := Γ) ((Quotient.out o : S) : Y)
    simp only at hη
    refine ⟨η * γ * η⁻¹, ?_⟩
    show F (Quotient.out (Quotient.mk (orbitRel Γ Y) ((Quotient.out o : S) : Y))) (η * γ * η⁻¹) ≠ 0
    rw [← hη, hF]; exact hγ
  have key := finsum_orbits_eq_finsum_conjClasses (fun (y : S) γ => F (y : Y) γ) hF' hst' hs' ho'
  refine Eq.trans ?_ (key.trans (finsum_congr fun c => ?_))
  · refine finsum_orbits_restrict (G := Γ) Subtype.val Subtype.val_injective (fun _ _ => rfl)
      (fun y => ((Nat.card (stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ)
      (fun y : S => ((Nat.card (stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (y : Y) γ)
      (fun y => by simp only [hstabS]) (fun η y => ?_) (fun y hy => ?_)
    · simp only [natCard_stabilizer_smul]
      congr 1
      rw [← finsum_comp_equiv (MulAut.conj η).toEquiv]
      refine finsum_congr fun γ => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      exact hF η y γ
    · by_contra hn
      apply hy
      have hinf : ¬ (stabilizer Γ y : Set Γ).Finite := fun h => hn ⟨⟨y, h⟩, rfl⟩
      haveI : Infinite (stabilizer Γ y) := Set.Infinite.to_subtype hinf
      rw [Nat.card_eq_zero_of_infinite (α := stabilizer Γ y), Nat.cast_zero, inv_zero, zero_mul]
  · set c' := Quotient.out c
    refine (finsum_orbits_restrict (G := Subgroup.centralizer {c'}) (Y := Y) (Y' := S)
      Subtype.val Subtype.val_injective (fun _ _ => rfl)
      (fun y => ((Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c')
      (fun y : S => ((Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (y : Y) c')
      (fun y => by simp only [hstabS]) (fun η y => ?_) (fun y hy => ?_)).symm
    · have hc : (η : Γ) * c' * (η : Γ)⁻¹ = c' := by
        have := Subgroup.mem_centralizer_iff.mp η.2 c' (Set.mem_singleton _)
        rw [← this, mul_inv_cancel_right]
      have hFc := hF η y c'
      rw [hc] at hFc
      simp only [Subgroup.smul_def]
      rw [natCard_stabilizer_inf_smul _ (η : Γ) (mem_iff_conj_mem _ η.2) y, hFc]
    · by_contra hn
      apply hy
      have hinf : ¬ (stabilizer Γ y : Set Γ).Finite := fun h => hn ⟨⟨y, h⟩, rfl⟩
      by_cases hc : F y c' = 0
      · simp [hc]
      have hI := stabilizer_inf_centralizer_infinite F hF y (hs y) c' hc hinf
      have h0 : Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) = 0 := by
        haveI : Infinite (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) := hI.to_subtype
        exact Nat.card_eq_zero_of_infinite
      rw [h0, Nat.cast_zero, inv_zero, zero_mul]

end GlobalTheory.OrbitUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCardStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ τ : E →+* ℂ, (primeBelow io X τ).IsMaximal ∧ ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h := by
  first | exact @GlobalTheory.PrimePart.primeBelow_isMaximal_card | exact GlobalTheory.PrimePart.primeBelow_isMaximal_card | (intros; apply GlobalTheory.PrimePart.primeBelow_isMaximal_card <;> assumption)
end

