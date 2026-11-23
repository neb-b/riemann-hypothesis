module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Conj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} [StarRing (𝓞 E)]
  {Ω : Type} [Field Ω]

def stdLat (A : Subring Ω) {d : ℕ} (T : ((Fin d → Ω) × (Fin d → Ω)) →ₗ[Ω] (Fin d → Ω) × (Fin d → Ω)) :
    Submodule A ((Fin d → Ω) × (Fin d → Ω)) :=
  Submodule.span A {y | ∃ y₀ : (Fin d → Ω) × (Fin d → Ω), (∀ i, y₀.1 i ∈ A ∧ y₀.2 i ∈ A) ∧ y = T y₀}

structure GermSys (t : SAB H X) (ξ : Spec (CommRingCat.of Ω) ⟶ X) {d : ℕ} (M : LieModel t.G ξ (Fin d → Ω)) where

  g₀ : GermAt t ξ d
  dir₀ : ∀ l, (M.pt (Pi.single l 1)).left = g₀.tg l
  act₀ : ∀ a v, M.pt ((rho g₀.B a).mulVec v) = M.pt v ≫ t.act.act a

  g : ∀ p : Cpt ξ, GermAt t (S := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) d

  BK : Cpt ξ → Germ.FB Ω d (𝓞 E)
  mapK : ∀ p, IsMapOf (genMap ξ p) (g p).B (BK p)

  φ : Cpt ξ → Germ.Pt Ω 1 d

  ψ : Cpt ξ → Germ.Pt Ω 1 d

  lam : Cpt ξ → Germ.PS Ω 2 d
  iso : ∀ p, IsIso g₀.B (BK p) (φ p) (ψ p) (lam p)
  dir : ∀ p l, (M.pt ((lin (φ p) 1).mulVec (Pi.single l 1))).left =
    Spec.map (CommRingCat.ofHom (dualMap (genMap ξ p))) ≫ (g p).tg l
  gen : ∀ (p q : Cpt ξ) (h : q.1 ⤳ p.1), ∃ (B' : Germ.FB (X.presheaf.stalk q.1) d (𝓞 E))
    (φ' ψ' : Germ.Pt (X.presheaf.stalk q.1) 1 d) (lam' : Germ.PS (X.presheaf.stalk q.1) 2 d),
    IsMapOf (X.presheaf.stalkSpecializes h).hom (g p).B B' ∧ IsIso (g q).B B' φ' ψ' lam' ∧
      transH (φ p) (ψ p) (lam p) = transH (φ q) (ψ q) (lam q) ∘ₗ
        transH (fun i => MvPowerSeries.map (genMap ξ q) (φ' i)) (fun i => MvPowerSeries.map (genMap ξ q) (ψ' i))
          (MvPowerSeries.map (genMap ξ q) lam')
  loc : ∀ p : Cpt ξ, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
    stdLat (regAt ξ q) (transH (φ p) (ψ p) (lam p)) = stdLat (regAt ξ q) (transH (φ q) (ψ q) (lam q))

def HFree {R : Type} [CommRing R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (r : ℕ) : Prop :=
  ∃ x : Fin r → (Fin d → R) × (Fin d → R),
    LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) ∧
    Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      rhoH B (RingOfIntegers.basis E q.2) (x q.1)) = ⊤

def HChar {R : Type} [CommRing R] [Nontrivial R] {d : ℕ} (B : Germ.FB R d (𝓞 E)) (r : ℕ) : Prop :=
  ∀ a : 𝓞 E, (rhoH B a).charpoly =
    ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom R)) ^ r

def GermSys.Gives {t : SAB H X} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {d : ℕ} {M : LieModel t.G ξ (Fin d → Ω)}
    (S : GermSys t ξ M) {ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)} {r : ℕ} (𝓗 : HodgeLat M.lat ρ H.bar r) : Prop :=
  (∀ a y, 𝓗.ρH a (y.1, dotProductBilin Ω Ω y.2) =
    ((rhoH S.g₀.B a y).1, dotProductBilin Ω Ω (rhoH S.g₀.B a y).2)) ∧
  ∀ (p : Cpt ξ) (y : (Fin d → Ω) × (Fin d → Ω)), (y.1, dotProductBilin Ω Ω y.2) ∈ 𝓗.HL p ↔
    y ∈ stdLat (regAt ξ p) (transH (S.φ p) (S.ψ p) (S.lam p))

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

structure CptOrigin (Y : Model Xo c β) (S₀ : Finset ℕ) (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) where

  𝔐 : HodgeCpt Y S₀ Dc.y

  deg : ℕ
  cover : 𝔐.IsCover deg

  bg : CMType H → CMType H ⊕ CMType H

  sm : CMType H → CMType H ⊕ CMType H
  side : (bg = Sum.inl ∧ sm = Sum.inr ∧ Dc.j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ Dc.j = D.q)
  N_eq : Dc.N = D.p + D.q

  i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li
  i_inj : ∀ τ, Function.Injective (i τ)
  i_range : ∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)
  F_eq : ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ)
  lat : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat
  bd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → (w ∈ Dc.Bd ↔ ¬ 𝔐.Interior z)
  metric : ∀ τ a (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → 𝔐.Interior z →
    InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w →
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => i τ ((Dc.h τ).b a k)) ((Dc.h τ).gram a w)
  S_disj : Disjoint Dc.S S₀
  R_ge : ∀ p ∈ Dc.S, 4 ≤ 𝔐.R p
  tors : ∀ p ∈ Dc.S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)
  ht_vb : ∀ p ∈ Dc.S, ∀ s, (𝔐.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre 𝔐.ξ r q} (labelRk D s)
    (𝔐.Vgen s)
  vert : ∀ p ∈ Dc.S, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord Dc.y) ch q →
    ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li)
      (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
      (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) →
      (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
          chartMono Dc.y ch (-Dc.vdeg p)))

section Ranks

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd)

theorem CptOrigin.rk_bg (τ : CMType H) : labelRk D (Or.bg τ) = Dc.j := by
  rcases Or.side with ⟨h, -, hj⟩ | ⟨h, -, hj⟩ <;> simp [h, hj]

theorem CptOrigin.rk_sm (τ : CMType H) : labelRk D (Or.sm τ) = Dc.N - Dc.j := by
  rcases Or.side with ⟨-, h, hj⟩ | ⟨-, h, hj⟩ <;> simp [h, hj, Or.N_eq]

theorem CptOrigin.bg_ne_sm (τ τ' : CMType H) : Or.bg τ ≠ Or.sm τ' := by
  rcases Or.side with ⟨h, h', -⟩ | ⟨h, h', -⟩ <;> simp [h, h']


include Or in
theorem CptOrigin.n_eq : Dc.n = Fintype.card (CMType H) * D.p * D.q := by
  rcases Or.side with ⟨-, -, hj⟩ | ⟨-, -, hj⟩ <;> simp [ComponentData.n, hj, Or.N_eq]
  ring

end Ranks

namespace Origin

section Period

variable {Ψ : Type} [Fintype Ψ] {V : Ψ → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)]
  {Dc : ComponentData II Ψ K J Ω V} {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

end Period

section Plane

open Line GaussianInt

variable (II) (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Plane

end Origin

section Comparison₂

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd) {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

variable {Or}

end Comparison₂

end GlobalTheory.CompanionTheory.Ar
end
end

