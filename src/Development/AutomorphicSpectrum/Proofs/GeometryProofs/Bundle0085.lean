module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.Rt0NeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem rt0_conj_neg_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have hsq := H.sqrt_neg_disc_sq
  have hd : (H.d : ℝ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have him := congrArg Complex.im hsq
  have hre := congrArg Complex.re hsq
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.natCast_im,
    Complex.natCast_re] at him hre
  have h0 : H.rt0.re = 0 := by
    by_contra h
    have hi : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by nlinarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [hi] at hre
    have : (0 : ℝ) < H.d := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hd)
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

theorem rt0_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have hsq := H.sqrt_neg_disc_sq
  rw [h] at hsq
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  simp at hsq
  exact H.d_prime.ne_zero hsq

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj

theorem ev_eigProj : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (h : HL) (hp : HT.eigProj ρH σ (h : Vs × Module.Dual Ω Vs) ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    ev ⟨_, hp⟩ = HT.eigProj ρHC σC (ev h) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g ℓ ψ ρH ρHC HL ev σ σC h hp hev htie hst
  choose hc hψ using htie
  have hsum : (⟨_, hp⟩ : HL) = ∑ k, (⟨σ (HT.dualInt E k), hc _⟩ : R') •
      (⟨ρH (RingOfIntegers.basis E k) (h : Vs × Module.Dual Ω Vs), hst _ _ h.2⟩ : HL) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, hψ, hev.1 _ h]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalProj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializeHodgeLatticeEigenbasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem isAdapted_eval : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field C]
    (R' : Subring Ω) (g p q : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* C)
    (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
    (σ : E →+* Ω) (σC : E →+* C) (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
    (x₁ : Fin p → Fin g → R') (x₂ : Fin q → Fin g → R') (hu : ∀ i, u i ∈ HL),
    IsEval ℓ ψ ρH ρHC HL ev → (∀ e : E, ∃ h : σ e ∈ R', ψ ⟨σ e, h⟩ = σC e) → (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) →
    IsAdapted ρH σ b₁ b₂ u → (∀ i, b₁ i = comb ℓ (x₁ i)) → (∀ i, b₂ i = comb ℓ (x₂ i)) →
    IsAdapted ρHC σC (fun i k => ψ (x₁ i k)) (fun i k => ψ (x₂ i k)) (fun i => ev ⟨u i, hu i⟩) := by
  intro E _ _ Ω Vs C _ _ _ _ R' g p q ℓ ψ ρH ρHC HL ev σ σC b₁ b₂ u x₁ x₂ hu hE hσ hcl hA hb₁ hb₂
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CPoint.IsEval at hE
  unfold GlobalTheory.CompanionTheory.Ar.Flat.IsAdapted at hA ⊢
  obtain ⟨hE1, hE2, hE3⟩ := hE
  obtain ⟨hA1, hA2, hA3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show ev ⟨u i, hu i⟩ ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρHC σC
    have hui := hA1 i
    rw [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf] at hui ⊢
    intro a
    have h1 := hui a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    change ρH a (u i) = σ (a : E) • u i at h1
    show ρHC a (ev ⟨u i, hu i⟩) = σC (a : E) • ev ⟨u i, hu i⟩
    obtain ⟨hσa, hψ⟩ := hσ (a : E)
    have hmem : ρH a (u i) ∈ HL := hcl a (u i) (hu i)
    have e1 : ev ⟨ρH a (u i), hmem⟩ = ρHC a (ev ⟨u i, hu i⟩) := hE1 a ⟨u i, hu i⟩ hmem
    have e2 : (⟨ρH a (u i), hmem⟩ : HL) = (⟨σ a, hσa⟩ : R') • (⟨u i, hu i⟩ : HL) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Subring.smul_def]
      exact h1
    rw [← e1, e2, map_smulₛₗ, hψ]
  · intro i
    exact hE2 ⟨u (Fin.castAdd q i), hu _⟩ (x₁ i) ((hA2 i).trans (hb₁ i))
  · intro j
    obtain ⟨hj1, hj2⟩ := hA3 j
    constructor
    · have hc : (u (Fin.natAdd p j)).1 = comb ℓ (fun _ => (0 : R')) := by
        rw [hj1]
        simp [GlobalTheory.CompanionTheory.Ar.Flat.CPoint.comb]
      have h3 := hE2 ⟨u (Fin.natAdd p j), hu _⟩ (fun _ => 0) hc
      refine h3.trans ?_
      funext k
      simp
    · intro j'
      have hc : (u (Fin.natAdd p j)).2 (comb ℓ (x₂ j')) = ((if j = j' then 1 else 0 : R') : Ω) := by
        rw [← hb₂ j', hj2 j']
        split_ifs <;> simp
      have h3 := hE3 ⟨u (Fin.natAdd p j), hu _⟩ (x₂ j') (if j = j' then 1 else 0) hj1 hc
      refine h3.trans ?_
      split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SqMap
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrGauge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

section Values

variable {X Y F : Scheme.{0}} {L : LB X} {M : LB Y} {f : F ⟶ X} {g : F ⟶ Y}

def wv (w : LB.Iso (L.pull f) (M.pull g)) {Z : Scheme.{0}} (ψ : Z ⟶ F) (z : Z) (JL : (Z ⟶ X) → L.ι)
    (JM : (Z ⟶ Y) → M.ι) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z _ (w.s (fun _ => JM (ψ ≫ g), fun _ => JL (ψ ≫ f)))

def Tr (w : LB.Iso (L.pull f) (M.pull g)) {Y' : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y' ⟶ F))
    (φL : K → (Y' ⟶ X)) (φM : K → (Y' ⟶ Y)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φL ε))
    (b : LB.Gen (LB.LinComb M φM ε)) (u : Γ(Y', ⊤)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (JL : (Z ⟶ X) → L.ι) (JM : (Z ⟶ Y) → M.ι), Good L z JL → Good M z JM →
    val c r z JL * ∏ k, wv w (r ≫ φ k) z JL JM ^ ε k = gm r z ⊤ u * val b r z JM

end Values

section Series

variable {R : Type} [CommRing R] {d d' : ℕ}

def linQ (Qs : Fin d' → PS R 1 d) : Matrix (Fin d') (Fin d) R :=
  fun i l => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), l) 1) (Qs i)

def subQ (Qs : Fin d' → PS R 1 d) (f : PS R 2 d') : PS R 2 d :=
  MvPowerSeries.subst (fun p : Fin 2 × Fin d' => ev (n := 2) ![pt R d p.1] (Qs p.2)) f

def sub1 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 1 × Fin d') m →ₐ[R] Jet R (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (Qs p.2)

def sub2 (Qs : Fin d' → PS R 1 d) (m : ℕ) : Jet R (Fin 2 × Fin d') m →ₐ[R] Jet R (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d' => psIn d m ![p.1] (Qs p.2)

end Series

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [Field k] (x : Sp k ⟶ X)

abbrev GF : Over (Sp k) := (Over.pullback x).obj t.G

def toF {T : Over (Sp k)} (a : T.left ⟶ t.G.left) (h : a ≫ t.G.hom = T.hom ≫ x) : T ⟶ GF t x :=
  Over.homMk (pullback.lift a T.hom h) (pullback.lift_snd _ _ _)

def fibPt {A : Type} [CommRing A] [Algebra k A] (y : overAt x A ⟶ t.G) : overAt (𝟙 (Sp k)) A ⟶ GF t x :=
  toF t x y.left (by simpa using Over.w y)

def cubeF {A : Type} [CommRing A] [Algebra k A] (xs : Fin 2 → (overAt x A ⟶ t.G)) (I : ULift (Finset (Fin 2))) :
    Sp A ⟶ (GF t x).left :=
  (fibPt t x (psum t.G xs I.down)).left

def sqPr (p : GF t x ⊗ GF t x ⟶ GF t x) : Over.mk ((GF t x ⊗ GF t x).hom ≫ x) ⟶ t.G :=
  Over.homMk (p.left ≫ pullback.fst t.G.hom x) (by
    have h : p.left ≫ pullback.snd t.G.hom x = (GF t x ⊗ GF t x).hom := Over.w p
    show (p.left ≫ pullback.fst t.G.hom x) ≫ t.G.hom = (GF t x ⊗ GF t x).hom ≫ x
    rw [Category.assoc, pullback.condition, ← Category.assoc, h])

def sqMap : (GF t x ⊗ GF t x).left ⟶ (t.G ⊗ t.G).left :=
  (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _))).left

def sqPt (a : t.G ⊗ t.G ⟶ t.G) : GF t x ⊗ GF t x ⟶ GF t x :=
  toF t x (sqMap t x ≫ a.left) (Over.w (lift (sqPr t x (fst _ _)) (sqPr t x (snd _ _)) ≫ a))

abbrev AdTy (t : SAB H X) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb t.PP.L
    (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
      (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

def adF (a : 𝓞 E) : ULift (Finset (Fin 2)) ⊕ ULift (Finset (Fin 2)) →
    ((GF t x ⊗ GF t x).left ⟶ (GF t x).left) :=
  Sum.elim (fun I => (sqPt t x (psum t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I.down)).left)
    (fun I => (sqPt t x (psum t.G ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I.down)).left)

def ax0 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (1 : GF t x ⟶ GF t x) (𝟙 (GF t x))).left

def ax1 : (GF t x).left ⟶ (GF t x ⊗ GF t x).left := (lift (𝟙 (GF t x)) (1 : GF t x ⟶ GF t x)).left

def qq {t : SAB H X} {x : Sp k ⟶ X} (Q : AbQuot t x) : (GF t x ⊗ GF t x).left ⟶ (Q.tB.G ⊗ Q.tB.G).left :=
  (lift (fst (GF t x) (GF t x) ≫ Q.q) (snd (GF t x) (GF t x) ≫ Q.q)).left

end Fibre

section AdRel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def AdRel (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S)
    (e : ∀ m, FrTyG t x0 d x m) (a : 𝓞 E) (wL : AdTy t a) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧
    LB.Gen.Corr t.PP.L _ _ _ _
      (LB.mulGen t.PP.L _ _ _ _
        (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
        (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ u)
        (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))

end AdRel

end GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TiedActionComposeResidueMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap

theorem tied_map_comp : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs K C : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] [Field K] [Field C]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (R' : Subring Ω) (g : ℕ) (ℓ : Fin g → Vs) (ψ : R' →+* K) (j : K →+* C)
    (ρK : 𝓞 E →+* Module.End K (Fin g → K)) (ρC : 𝓞 E →+* Module.End C (Fin g → C)),
    (∀ a i, ρ a (ℓ i) ∈ Submodule.span R' (Set.range ℓ)) → Tied ℓ ψ ρ ρK → Tied ℓ (j.comp ψ) ρ ρC →
    ∀ (a : 𝓞 E) (x : Fin g → K), ρC a (fun i => j (x i)) = fun i => j (ρK a x i) := by
  intro E _ _ Ω Vs K C _ _ _ _ _ ρ R' g ℓ ψ j ρK ρC hρ hK hC a x
  have hex : ∀ i, ∃ c : Fin g → R', ρ a (ℓ i) = comb ℓ c := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R').1 (hρ a i)
    exact ⟨c, by rw [← hc]; rfl⟩
  choose c hc using hex
  have hs : ∀ i, comb ℓ (Pi.single i (1 : R') : Fin g → R') = ℓ i := by
    intro i
    unfold comb
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have h1 : ∀ i, ρK a (Pi.single i (1 : K)) = fun k => ψ (c i k) := by
    intro i
    have := hK a (Pi.single i 1) (c i) (by rw [hs, hc])
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h2 : ∀ i, ρC a (Pi.single i (1 : C)) = fun k => j (ψ (c i k)) := by
    intro i
    have := hC a (Pi.single i 1) (c i) (by rw [hs, hc])
    simp only [RingHom.comp_apply] at this
    rw [← this]
    congr 1
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hxK : x = ∑ i, x i • (Pi.single i (1 : K) : Fin g → K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hxC : (fun i => j (x i)) = ∑ i, j (x i) • (Pi.single i (1 : C) : Fin g → C) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hxC, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hxK, map_sum]
  ext k
  simp [Finset.sum_apply, h1, h2]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.TiedMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VerticalStatementHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

open ReciprocityTheory.ChartRestriction.G.AI.I2

theorem vertical_holds : VerticalStatement := GroundTheory.Heights₂.Heights.Inter.InductiveIntersectionFormula.proof

end GlobalTheory.CompanionTheory.Ar.Flat
end

