module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptHt (a : K → ℝ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) + ∑ σ : L →+* ℂ, φ fun p => σ (w p))

def lineHt (A : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  ptHt (fun k => (A.a k : ℝ)) (fun z => Real.log (A.h z)) L w

def GenUnit (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y), ∃ val : L, val ≠ 0 ∧ HasVal y a u z val

def VertBound (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (c : ℝ) : Prop :=
  u ≠ 0 ∧ ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ Real.log m ≤ q * c ∧ (m : Ω) * u ^ q ∈ chartLatNm y a q ∧
    (m : Ω) * u⁻¹ ^ q ∈ chartLatNm y (-a) q

def AmpleQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∃ (m l : ℕ) (s : Fin l → Ω), (∀ i, s i ∈ chartLatNm y (fun k => m * a k - 1) 1) ∧
    ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y),
      ∃ (i : Fin l) (val : L), val ≠ 0 ∧ HasVal y (fun k => m * a k - 1) (s i) z val

end Points

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def rootHt (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, M.ι k) → L) : ℝ :=
  ∑ j, M.coef lam s j * lineHt (M.line t j) L w

def joinOf (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) : (Σ k, joinIdx M.ι R.ι k) → M.Ω :=
  joinVec M.y fun p => i (R.y p)

def joinDeg (M R : RootModel Ψ N) (j : Option (Ψ × Fin N)) : M.K ⊕ R.K → ℤ :=
  Sum.elim (M.line 1 j).a (-(R.line 1 j).a)

structure Close (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c : ℝ) : Prop where
  kA : M.kA = R.kA
  unit : ∀ j, GenUnit (joinOf M R i) (joinDeg M R j) (u j)
  vert : ∀ j, VertBound (joinOf M R i) (joinDeg M R j) (u j) c

def ArchBetween (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Wt Ψ N)
    (s lo hi : ℝ) : Prop :=
  ∀ z ∈ ptsOver ℂ (mCoordIdeal (joinOf M R i)), ∀ val : Option (Ψ × Fin N) → ℂ,
    (∀ j, HasVal (joinOf M R i) (joinDeg M R j) (u j) z (val j)) →
      ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (joinInl M.ι R.ι p)) -
        Real.log ((R.line 1 j).h fun p => z (joinInr M.ι R.ι p)) - Real.log ‖val j‖) ∈ Set.Icc lo hi

def HasRef (T : RootTower Ψ N) (R : T.Comp → RootModel Ψ N) : Prop :=
  ∃ (C s₀ : ℝ), 0 < s₀ ∧ ∀ B : ℕ, 2 ≤ B → ∀ c, ∃ (i : (R c).Ω →+* (T.M B c).Ω) (u : Option (Ψ × Fin N) → (T.M B c).Ω),
    Close (T.M B c) (R c) i u (C * Real.log B) ∧ ∀ (mu : Wt Ψ N) (s : ℝ), Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ →
      ArchBetween (T.M B c) (R c) i u (scale s) mu s (-(C * Real.log (1 / s)) - C) C

def RefLower (R : RootModel Ψ N) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    -C ≤ rootHt R 1 0 1 L w ∧ ∀ mu : Wt Ψ N, Dominant mu → ‖mu‖ ≤ 2 →
      -(C * Real.log (2 + C + rootHt R 1 0 1 L w)) - C ≤ rootHt R 1 mu 0 L w

def FlatUnit (R : RootModel Ψ N) : Prop :=
  ∀ τ, ∃ (k : ℕ) (u : R.Ω) (c : ℝ), 0 < k ∧ GenUnit R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u ∧
    VertBound R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u c

def FibreInput {j k : ℕ} (R : RootModel Ψ (j + k)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : L →+* L')
      (E : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L') (A : FlagPair E Ψ j k), A.IsOrthFull ∧
      (∀ τ (i : Fin j), |lineHt (R.x 1 (τ, Fin.castAdd k i)) L w - (A.W τ).grDeg i| ≤ C) ∧
      (∀ τ (i : Fin k), |lineHt (R.x 1 (τ, Fin.natAdd j i)) L w + (A.S τ).grDeg i.rev| ≤ C) ∧
      E.slopeMax ≤ ((C * Real.log (2 + C + max (-E.normDegree ⊤) 0) + C : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar.Ht
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

abbrev FracBase {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a

def Reads (U : Set (Xo.XF c)) (τ : E →+* ℂ) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) : Prop :=
  ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c),
    under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U →
    ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
      (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
      ψ (s p z) = φ F y v w

def UnitRule (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.Rule Y) :
    Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) v w,
    GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.IsFrame Y U τ j x v w → IsUnit (sig R x v w)

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section Metric

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

structure LieMetric (M : LieModel G ξ Li) {K : Type} {J : K → Type} (y : (Σ k, J k) → Ω) where

  ip : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ
  herm : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V),
    ∃ core : InnerProductSpace.Core ℂ V, ∀ a b, core.inner a b = ip z (Mz.pt a) (Mz.pt b)
  conj : ∀ (z : Sp ℂ ⟶ X) (v w : epsAt z ⟶ G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G),
    v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left →
      ip _ v' w' = starRingEnd ℂ (ip z v w)
  cont : ∀ a b : Li, ∃ F : ((Σ k, J k) → ℂ) → ℂ,
    ContinuousOn F {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z a va ∧ M.ValAt z b vb} ∧
      ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w → M.ValAt z a va →
        M.ValAt z b vb → F w = ip z va vb

def LieMetric.Orth {M : LieModel G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y)
    {O : Type} [CommRing O] (act : OAct O G) : Prop :=
  ∀ (z : Sp ℂ ⟶ X) (τ τ' : O →+* ℂ) (v w : epsAt z ⟶ G), τ ≠ τ' → IsLieEigen act z τ v → IsLieEigen act z τ' w →
    h.ip z v w = 0

variable {L : Type} [Field L] [NumberField L]

def IsFibre (rel : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ → Prop) (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : Prop :=
  ∀ (σ : L →+* ℂ) (x x' : B.carrier) (v v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G),
    (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) → (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x').left) →
      rel _ v v' ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x'))

def IsSubFibre (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) (F : Submodule (𝓞 L) V) : Prop :=
  ∀ x, x ∈ F ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L)
    {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
      M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left)}

end Metric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure AbPart {S : Scheme.{0}} (t : SAB H S) {K : Type} [Field K] (z : Sp K ⟶ S) where

  tK : SAB H (Sp K)
  m : SABMap tK t z

  τ : TorusExtension tK.G

  tB : SAB H (Sp K)

  e : τ.B ≅ tB.G
  e_hom : letI := τ.grpB; IsMonHom e.hom
  act : ∀ a, tK.act.act a ≫ τ.q ≫ e.hom = τ.q ≫ e.hom ≫ tB.act.act a
  pp : LBIso tK.PP.L (tB.PP.L.pull (τ.q ≫ e.hom).left)

def IsPrincipal {K : Type} [Field K] (t : SAB H (Sp K)) : Prop :=
  IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L

def SlopeBoundSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK →
    ∀ (B : HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB →
      B.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitCompsOfIsTowerOf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOfTest

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem factor {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (ξ' : Spec (CommRingCat.of Ω') ⟶ X) (e : genPt ξ' = genPt ξ) :
    ∃ i : Ω →+* Ω', ξ' = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
  have key : ∀ (x x' : X) (_ : x' = x) (φ : X.presheaf.stalk x ⟶ CommRingCat.of Ω) [IsIso φ]
      (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of Ω'), ∃ i : Ω →+* Ω',
      Spec.map φ' ≫ X.fromSpecStalk x' = Spec.map (CommRingCat.ofHom i) ≫ Spec.map φ ≫ X.fromSpecStalk x := by
    intro x x' e φ _ φ'
    subst e
    refine ⟨(inv φ ≫ φ').hom, ?_⟩
    rw [CommRingCat.ofHom_hom, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h.bij
  obtain ⟨i, hi⟩ := @key _ _ e (Scheme.stalkClosedPointTo ξ) this (Scheme.stalkClosedPointTo ξ')
  refine ⟨i, ?_⟩
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ').symm.trans (hi.trans
    (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem spec_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

section
variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

end

end GlobalTheory.CompanionTheory.Ar.TowerOfTest
end
end

