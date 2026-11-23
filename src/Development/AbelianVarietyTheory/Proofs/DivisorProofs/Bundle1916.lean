module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphism
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
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.NeatUnip

theorem iter_comp {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (α : G ⟶ G) (n : ℕ)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) :
    x ≫ (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = (fun z => z ≫ α)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [← ih, Category.assoc]

theorem finite_order_unipotent_eq_id : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G] (act : OAct (𝓞 E) G) (α : G ⟶ G) (n m g r : ℕ) (I : Ideal (𝓞 E)), IsSemiAbelian G → IsMonHom α → (∀ a, act.act a ≫ α = α ≫ act.act a) → 0 < n → (fun f : G ⟶ G => f ≫ α)^[n] (𝟙 G) = 𝟙 G → g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → r + 1 < g → (∃ T : Finset (𝟙_ (Over (Sp k)) ⟶ G), T.card ≤ g ^ r ∧ ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → x ∈ T) → (∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (∀ a ∈ I, x ≫ act.act a = 1) → (fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[m] x = 1) → α = 𝟙 G := by
  intro E _ _ k _ _ _ G _ act α n m g r I hG hα hcomm hn hpow hg hI hI2 hr hfin hunip
  classical
  haveI := hG.comm
  haveI := hα
  haveI : ∀ a, IsMonHom (act.act a) := act.hom
  letI cg : CommGroup (𝟙_ (Over (Sp k)) ⟶ G) := Hom.commGroup
  have act0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  letI inst : Module (𝓞 E) (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { smul := fun a x => Additive.ofMul (x.toMul ≫ act.act a)
    one_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 1) = x
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a * b)) = Additive.ofMul ((x.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm a b, act.mul, Category.assoc]
    smul_zero := fun a => by
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp k)) ⟶ G) ≫ act.act a) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun a x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ act.act a) = Additive.ofMul ((x.toMul ≫ act.act a) * (y.toMul ≫ act.act a))
      rw [MonObj.mul_comp]
    add_smul := fun a b x => by
      show Additive.ofMul (x.toMul ≫ act.act (a + b)) = Additive.ofMul ((x.toMul ≫ act.act a) * (x.toMul ≫ act.act b))
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun x => by
      show Additive.ofMul (x.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [act0, MonObj.comp_one] }
  have hsmul : ∀ (a : 𝓞 E) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)), a • x = Additive.ofMul (x.toMul ≫ act.act a) :=
    fun _ _ => rfl
  have htors : ∀ (J : Ideal (𝓞 E)) (x : 𝟙_ (Over (Sp k)) ⟶ G),
      (∀ a ∈ J, a • Additive.ofMul x = 0) ↔ ∀ a ∈ J, x ≫ act.act a = 1 := fun J x =>
    forall₂_congr fun a _ => by rw [hsmul]; exact ofMul_eq_zero
  let β : Additive (𝟙_ (Over (Sp k)) ⟶ G) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp k)) ⟶ G) :=
  { toFun := fun x => Additive.ofMul (x.toMul ≫ α)
    map_add' := fun x y => by
      show Additive.ofMul ((x.toMul * y.toMul) ≫ α) = Additive.ofMul ((x.toMul ≫ α) * (y.toMul ≫ α))
      rw [MonObj.mul_comp]
    map_smul' := fun a x => by
      show Additive.ofMul ((x.toMul ≫ act.act a) ≫ α) = Additive.ofMul ((x.toMul ≫ α) ≫ act.act a)
      rw [Category.assoc, hcomm, Category.assoc] }
  have hβ : ∀ x, β x = Additive.ofMul (x.toMul ≫ α) := fun _ => rfl

  let A : AddSubgroup (Additive (𝟙_ (Over (Sp k)) ⟶ G)) :=
  { carrier := {x | ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0}
    add_mem' := by
      rintro x y ⟨i, hi⟩ ⟨j, hj⟩
      refine ⟨i + j, fun a ha => ?_⟩
      rw [smul_add, hi a (Ideal.pow_le_pow_right (by omega) ha),
        hj a (Ideal.pow_le_pow_right (by omega) ha), add_zero]
    zero_mem' := ⟨0, fun a _ => smul_zero a⟩
    neg_mem' := by
      rintro x ⟨j, hj⟩
      exact ⟨j, fun a ha => by rw [smul_neg, hj a ha, neg_zero]⟩ }
  have memA : ∀ x, x ∈ A ↔ ∃ j : ℕ, ∀ a ∈ I ^ j, a • x = 0 := fun _ => Iff.rfl
  let βA : A →+ A :=
  { toFun := fun x => ⟨β x.1, by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      exact ⟨j, fun a ha => by rw [← LinearMap.map_smul, hj a ha, map_zero]⟩⟩
    map_zero' := Subtype.ext (map_zero β)
    map_add' := fun x y => Subtype.ext (map_add β x.1 y.1) }
  have hβA : ∀ x : A, ((βA x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β x.1 := fun _ => rfl
  have hβAit : ∀ (N : ℕ) (x : A), ((βA^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) = β^[N] x.1 := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hβA, ih]
  have hβit : ∀ (N : ℕ) (x : Additive (𝟙_ (Over (Sp k)) ⟶ G)),
      β^[N] x = Additive.ofMul ((fun z => z ≫ α)^[N] x.toMul) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl
  have hsubit : ∀ (N : ℕ) (x : A),
      (((fun z : A => βA z - z)^[N] x : A) : Additive (𝟙_ (Over (Sp k)) ⟶ G)) =
        Additive.ofMul ((fun z : 𝟙_ (Over (Sp k)) ⟶ G => (z ≫ α) * z⁻¹)^[N] (Additive.toMul x.1)) := by
    intro N; induction N with
    | zero => intro x; rfl
    | succ N ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AddSubgroup.coe_sub, hβA, ih, hβ,
        toMul_ofMul, ← ofMul_div, div_eq_mul_inv]
  have hgI : (g : 𝓞 E) ∈ I := hI ▸ Ideal.absNorm_mem I
  have hdivM : ∀ x : Additive (𝟙_ (Over (Sp k)) ⟶ G), ∃ y, g • y = x := by
    intro x
    obtain ⟨y, hy⟩ := GlobalTheory.SS.torusExtension_points_divisible k G (GlobalTheory.TorsionDense.nonempty_torusExtension G hG)
      g hg.one_le x.toMul
    exact ⟨Additive.ofMul y, by rw [← ofMul_pow, hy]; rfl⟩
  obtain ⟨hred1, hred2⟩ := _root_.GlobalTheory.primaryTorsion_divisible_and_gTorsion E (Additive (𝟙_ (Over (Sp k)) ⟶ G)) g I hg hI hI2 hdivM
  have key := _root_.GlobalTheory.finite_order_unipotent_eq_id A βA n g r m hn
    (fun x => Subtype.ext (by
      rw [hβAit, hβit, ← iter_comp, hpow, Category.comp_id]; rfl))
    hg (by omega)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      obtain ⟨y, hy, hy'⟩ := hred1 j x.1 hj
      exact ⟨⟨y, j + 1, hy'⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hy)⟩)
    (fun x => by
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      refine ⟨j, Subtype.ext ?_⟩
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← Nat.cast_smul_eq_nsmul (𝓞 E), Nat.cast_pow]
      exact hj _ (Ideal.pow_mem_pow hgI j))
    (by
      obtain ⟨T, hT, hTm⟩ := hfin
      refine ⟨(T.map Additive.ofMul.toEmbedding).subtype (· ∈ A), ?_, fun x hx => ?_⟩
      · rw [Finset.card_subtype]
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_map]; exact hT)
      · have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
        obtain ⟨j, hj⟩ := (memA x.1).1 x.2
        have h1 := hred2 j x.1 hj hx'
        rw [Finset.mem_subtype, Finset.mem_map]
        exact ⟨Additive.toMul x.1, hTm _ ((htors I _).1 h1), rfl⟩)
    (fun x hx => by
      have hx' : g • x.1 = 0 := by have := congrArg Subtype.val hx; simpa using this
      obtain ⟨j, hj⟩ := (memA x.1).1 x.2
      have h1 := hred2 j x.1 hj hx'
      refine Subtype.ext ?_
      have h2 := hunip (Additive.toMul x.1) ((htors I _).1 h1)
      rw [hsubit, h2]; rfl)
  have hfix : ∀ (j : ℕ) (x : 𝟙_ (Over (Sp k)) ⟶ G), (∀ a ∈ I ^ j, x ≫ act.act a = 1) → x ≫ α = x := by
    intro j x hx
    have h := congrArg Subtype.val (key ⟨Additive.ofMul x, j, (htors _ x).2 hx⟩)
    exact congrArg Additive.toMul h
  have hγ : IsMonHom (α * (𝟙 G)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  have hI1 : I ≠ ⊤ := fun h => by
    rw [h, Ideal.absNorm_top] at hI
    exact hg.one_lt.ne hI
  have h1 := _root_.GlobalTheory.IdealTorsion.eq_one_of_idealTorsion_comp_eq_one E k G act (α * (𝟙 G)⁻¹) I hG hγ
    (fun a => by
      rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp, GrpObj.inv_comp, hcomm, Category.comp_id,
        Category.id_comp])
    hI1
    (fun j x hx => by rw [MonObj.comp_mul, GrpObj.comp_inv, hfix j x hx, Category.comp_id, mul_inv_cancel])
  rw [mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.NeatUnip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.FlatTwisting

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem wtOf_parWt_anti (w : Psi H → ℤ) (τ : E →+* ℂ) (i j : ℕ) (hij : i ≤ j) (hj : j < Dw.mult τ) :
    (wtOf Dw (parWt Dw w) 0).1 (τ, j) ≤ (wtOf Dw (parWt Dw w) 0).1 (τ, i) := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : j < Dw.p := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ j hp
    have e2 := wtOf_big (parWt Dw w) 0 ⟨τ, h⟩ i (by omega)
    exact (e1.trans e2.symm).le
  · have hq : j < Dw.q := by simpa [Datum.mult, h] using hj
    have e1 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ j hq
    have e2 := wtOf_small (parWt Dw w) 0 ⟨conjEmb τ, conj_mem h⟩ i (by omega)
    simp only [conjEmb_conjEmb] at e1 e2
    exact (e1.trans e2.symm).le

theorem wtOf_parWt_neg (w : Psi H → ℤ) : wtOf Dw (parWt Dw (-w)) 0 = -wtOf Dw (parWt Dw w) 0 := by
  have h := wtOf_add' (Dw := Dw) (parWt Dw (-w)) (parWt Dw w)
  have h0 : parWt Dw (-w) + parWt Dw w = 0 := by funext τ i; simp [parWt]
  rw [h0, wtOf_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mul_sig_mem_cuspOn (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c} {w : Psi H → ℤ} {δ : HeightOneSpectrum (𝓞 c.F) → ℝ}
    (s : ConstSec U x Z (parWt Dw w) δ) :
    ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s.sig ∈ cuspOn U Z (G + wtOf Dw (parWt Dw w) 0) :=
  GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ s.sig hK hU hpq (even_wtOf _ _) (wtOf_parWt_anti w) s.sig_mem
    s.sig_mem_suppOn fun σ hσ => ⟨s.cInf σ, by
      have e : goodOf c σ = σ := if_pos hσ
      have h : ∀ z ∈ framesOn (U (goodOf c σ)) Z,
          homN (U (goodOf c σ)) x (wtOf Dw (parWt Dw w) 0) s.sig z ≤ s.cInf σ := fun z hz => (s.homN_eq hz).le
      rw [e] at h
      exact h⟩

theorem exists_twSec_of_const {B : Finset ℕ} (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) (Z : Comp Xo c) (w : Psi H → ℤ)
    (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ) (hδ : (Function.support δ).Finite) :
    ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
      t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo := by
  refine ⟨TwSec.ofConst s hδ (mul_sig_mem_cuspOn hK hU hpq s) fun G hG f hf => ?_, rfl, rfl, rfl, rfl,
    intOff_of_unramPts E H Dw l Xo c r U x B hB Z _ δ s⟩
  have h := mul_sig_mem_cuspOn hK hU hpq (w := -w) (s.symm.copy rfl rfl) (G + wtOf Dw (parWt Dw w) 0)
    (Even.add hG (even_wtOf _ _)) f hf
  rw [wtOf_parWt_neg, add_neg_cancel_right] at h
  exact h

theorem finite_sum_flDefect (w : Psi H → ℤ) :
    (Function.support (∑ τ, (-w τ) • flDefect_vw Dw c τ)).Finite := by
  refine (Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := Dw) (c := c) τ).subset fun la hla => ?_
  by_contra hn
  simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
  exact hla (by simp [Finset.sum_apply, hn])

theorem finsum_sum_flDefect (w : Psi H → ℤ) :
    ∑ᶠ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
  have h1 : ∀ la, (∑ τ, (-w τ) • flDefect_vw Dw c τ) la * lw c.F la =
      ∑ τ, (-(w τ : ℝ)) * (flDefect_vw Dw c τ la * lw c.F la) := fun la => by
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]; push_cast; ring
  rw [finsum_congr h1, finsum_sum_comm _ _ fun τ _ =>
    (fin_mul (finite_flDefect_vw τ) (lw c.F)).subset (Function.support_mul_subset_right _ _),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← mul_finsum, sum_flDefect_vw]; ring

theorem twSec_of_flat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ) (B : Finset ℕ) (hK : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hpq : 1 ≤ Dw.p + Dw.q) (hB : UnramPts Xo c B) :
    (∀ (Z : Comp Xo c) (w : Psi H → ℤ) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z (parWt Dw w) δ),
      (Function.support δ).Finite → ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0),
        t.sig = s.sig ∧ t.cInf = s.cInf ∧ t.lo = δ + s.rho_vw ∧ t.hi = t.lo ∧ IntOff B t.lo) ∧
    (FlatExists U x → ∀ (Z : Comp Xo c) (w : Psi H → ℤ), HasPts U Z →
      ∃ t : TwSec U x Z (wtOf Dw (parWt Dw w) 0), IntOff B t.lo ∧
        t.degLo = (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) ∧
        (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * lrd E * (∑ τ, |(w τ : ℝ)|) ≤ t.degLo) := by
  refine ⟨exists_twSec_of_const hK hU hpq hB, fun hF Z w hp => ?_⟩
  have sF : ∀ τ, FlatSec U x Z τ := fun τ => (hF.nonempty Z τ).some
  have hδ := finite_sum_flDefect (Dw := Dw) (c := c) w
  obtain ⟨s, hdeg⟩ : ∃ s : ConstSec U x Z (parWt Dw w) (∑ τ, (-w τ) • flDefect_vw Dw c τ),
      s.deg = ∑ τ, (w τ : ℝ) * c1 U x τ :=
    ⟨(FlatSec.shift hp sF w).copy rfl (by congr; exact Subsingleton.elim _ _), (hF.deg_shift hp sF w).trans (by congr; exact Subsingleton.elim _ _)⟩
  obtain ⟨t, -, h2, h3, -, h5⟩ := exists_twSec_of_const hK hU hpq hB Z w _ s hδ
  have key := lineDeg_mul (r := 1) (fun _ => one_pos) s.cInf_pos hδ s.finite_rho
  rw [one_mul] at key
  have hd : t.degLo =
      (∑ τ, (w τ : ℝ) * c1 U x τ) - (Dw.q : ℝ) * (lrd E - Real.log H.d) * (∑ τ, (w τ : ℝ)) := by
    have h1 : lineDeg (1 : (c.F →+* ℂ) → ℝ) (∑ τ, (-w τ) • flDefect_vw Dw c τ) =
        -((Dw.q : ℝ) * (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ)) := by
      rw [lineDeg, finsum_sum_flDefect]; simp
    rw [TwSec.degLo, h2, h3, key, h1, ← hdeg, ConstSec.deg]; ring
  refine ⟨t, h5, hd, ?_⟩
  have hA := _root_.GlobalTheory.abs_lrd_sub_log_d_le_lrd E H
  have hs : (lrd E - Real.log H.d) * ∑ τ, (w τ : ℝ) ≤ lrd E * ∑ τ, |(w τ : ℝ)| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hA (abs_nonneg _)
  have := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) Dw.q)
  rw [hd, mul_assoc, mul_assoc]
  linarith

end GlobalTheory.FlatTwisting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLe
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwMulOne

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_eq_of_agree {Z : Comp Xo c} {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal} (hv : v ∈ valOn Z w)
    {f g : Rul Xo c}
    (h : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → evR Xo c g y = evR Xo c f y) :
    v g = v f := by
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  show nval T.V e (evR Xo c g y.1) = nval T.V e (evR Xo c f y.1)
  rw [h _ y.1 hy.2]

theorem exists_latW_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c)
    (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G,
    ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG Z t w v hv f hf
  obtain ⟨f', hres, hlat⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict E H Dw l Xo c r U hU Z G f
  have hf'lat := hlat hf
  obtain ⟨a, ha0, hva, hpos⟩ := GlobalTheory.RefSum.ScalApprox.exists_scal c.F t.lo t.finite_lo w
  obtain ⟨φ, hφ, -, hint, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ t G hG
  have hg := hint a ha0 hpos f' hf'lat (a • φ f') (by rw [Submodule.coe_smul])
  refine ⟨⟨(a • φ f' : cuspOn U Z (G + G₀)), cuspOn_le U Z (G + G₀) (a • φ f').2⟩, (mem_latOn U).1 hg, ?_⟩
  have hV := isVal_valOn hv
  obtain ⟨b, hb, -, -, hbhi⟩ := t.exists_val hv
  have e1 : v (f' : Rul Xo c) = v (f : Rul Xo c) := val_eq_of_agree hv (hres)
  show v ((a • φ f' : cuspOn U Z (G + G₀)) : Rul Xo c) ≤ _
  rw [Submodule.coe_smul, hV.smul _ _ ha0, hφ, hV.mul, e1, hb, hva]
  rw [← add_assoc, add_comm (((-(⌊t.lo w⌋ : ℝ) : ℝ)) : EReal) (v (f : Rul Xo c)), add_assoc, ← EReal.coe_add]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.TwMulOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFrameReadingNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory

theorem exists_rdU_ne_zero_of_mem_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, F ≠ 0 → ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U hU e F hF hF0
  by_contra hcon
  push_neg at hcon
  apply hF0
  funext p y
  show F p y = 0
  refine Formalism.L2.Pj.eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨k, x, u, hk⟩ :=
    GlobalTheory.test_value_eq_const_mul_reading_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange U hU e p y ψ
  have h := hk F hF
  rw [hcon k x.1 x.2, mul_zero] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem dualMap_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (Chart.dualMapR f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap, Chart.dualMapR]

theorem dualMap_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (dualMap g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isPullback_gen {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) A.A.hom G.hom (spMap (algebraMap V (FractionRing V))) := by
  haveI : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
  have sq : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK V)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w U.gen.inv⟩
  simpa using sq.paste_horiz (IsPullback.of_hasPullback G.hom (jK V))

theorem vecAt_genFibre : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G),
    (∃! yA, VecAt U.toUnifPre F y yA) ∧
    (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧
    ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  intro V _ _ _ _ _ D A G _ _ _ U F _ _ y
  have hφ := isPullback_gen U.toUnifPre
  have hT : IsPullback (fst (TFK (R := V) F) A.A).left (snd (TFK (R := V) F) A.A).left (TFK (R := V) F).hom A.A.hom :=
    IsPullback.of_hasPullback _ _
  have key : ∀ (v : epsR (FractionRing V) ⟶ A.A) yA,
      IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v →
      VecAt U.toUnifPre F y yA →
      yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
    intro v yA hv hy
    refine hφ.hom_ext ?_ ?_
    · rw [Category.assoc, hy.2, Category.assoc]
      unfold IsVecOver at hv
      rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
    · rw [Category.assoc, Over.w (snd _ _), ← Over.w (fst _ _), ← Category.assoc, hy.1, Category.assoc, Over.w v]
      show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
      rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  obtain ⟨v, hv, hvu⟩ := existsUnique_isVecOver hφ y
  refine ⟨?_, ⟨v, hv, hvu⟩, key⟩
  have w : (spMap (algebraMap F (DualNumber F)) ≫ (TFK (R := V) F).hom) =
      (spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left) ≫ A.A.hom := by
    rw [Category.assoc, Over.w v]
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap]
  have hy : VecAt U.toUnifPre F y (hT.lift _ _ w) := by
    refine ⟨hT.lift_fst _ _ w, ?_⟩
    rw [← Category.assoc, hT.lift_snd _ _ w, Category.assoc]
    unfold IsVecOver at hv
    rw [hv, ← Category.assoc, spMap_comp_spMap, dualMap_comp_dualMapR]
  refine ⟨hT.lift _ _ w, hy, fun yA h => ?_⟩
  exact hT.hom_ext ((h.1).trans (hT.lift_fst _ _ w).symm) ((key v yA hv h).trans (hT.lift_snd _ _ w).symm)

end GlobalTheory.MBLow
end
end

