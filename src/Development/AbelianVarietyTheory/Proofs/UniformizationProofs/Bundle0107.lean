module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0100
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameVal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpaces
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.Weight

open GlobalTheory.TorusExt GlobalTheory.ClassWeight

abbrev SecA {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  SecMod (F := F) (fst (TFK (R := R) F) A.A).left (LPow A.A A.L (k : ℤ) (TFK (R := R) F))

theorem exists_expansion (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U =>
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
      ∃ S : ∀ α, SecA A F k →ₗ[F] CompMod D F k α,
        (∀ (v : SecA A F k) (s : Raw D F k), U.ExpF F k v.sec s ↔ s = fun α => (S α v).sec) ∧
        ∀ v, (∀ α, S α v = 0) → v = 0 := by
  intro V _ _ _ hV D A G _ _ U F _ _ k hk
  choose x hx using _root_.GlobalTheory.UU.ExpTotal.expF_total hL hL₂ V hV D A G U F k hk
  have uq := _root_.GlobalTheory.UU.ExpFUniq.main V hV D A G U F k
  have lin := ExpLin.expF_linear V hV D A G U F k
  let S₀ : ∀ α, SecA A F k → CompMod D F k α := fun α v => SecMod.mk _ (x v.sec α)
  have comb : ∀ (c : F) (v v' : SecA A F k) α, S₀ α (c • v + v') = c • S₀ α v + S₀ α v' := fun c v v' =>
    congrFun ((uq _ _ _ _ (hx (c • v + v').sec) (lin v.sec v'.sec (c • v + v').sec _ _
      (fun α => (c • S₀ α v + S₀ α v').sec) c (hx v.sec) (hx v'.sec) (fun _ => rfl) fun _ _ => rfl)).1 rfl)
  have z : ∀ α, S₀ α 0 = 0 := fun α => by
    have := comb 1 0 0 α
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  refine ⟨fun α =>
    { toFun := S₀ α
      map_add' := fun v v' => by simpa only [one_smul] using comb 1 v v' α
      map_smul' := fun c v => by simpa only [add_zero, z, RingHom.id_apply] using comb c v 0 α },
    fun v s => ⟨fun h => (uq _ _ _ _ h (hx v.sec)).1 rfl, fun h => h ▸ hx v.sec⟩, fun v h => ?_⟩
  exact (uq _ _ _ _ (hx v.sec) (hx (0 : SecA A F k).sec)).2 (funext fun α => (h α).trans (z α).symm)

theorem exists_rep (hL : Laws) (hL₂ : Laws2) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ (Φ : TorsPt A (TFK (R := R) F) N → (SecA A F N ≃ₗ[F] SecA A F N))
      (e : TorsPt A (TFK (R := R) F) N → TorsPt A (TFK (R := R) F) N → Fˣ),
      Module.finrank F (SecA A F N) = N ^ A.g ∧ Nat.card (TorsPt A (TFK (R := R) F) N) = N ^ (2 * A.g) ∧
      (∀ a, ∃ θ : ThetaGrp A.A A.L N (TFK (R := R) F), θ.pt = a.1 ∧ ∀ v, IsActOf A.A A.L N θ v.sec (Φ a v).sec) ∧
      (∀ a b, ∃ c : Fˣ, ∀ v, Φ (a * b) v = (c : F) • Φ a (Φ b v)) ∧
      (∀ a b v, Φ a (Φ b v) = (e a b : F) • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a = 1 := by
  obtain ⟨Φ, e, hd, h⟩ := exists_projective_rep hL hL₂ A (jFK (R := R) F) hN
  exact ⟨Φ, e, hd, (hL.mulN _ A N (Nat.pos_of_ne_zero fun e => hN (by rw [e, Nat.cast_zero]))).2.2.2.2 F
    (jFK (R := R) F) hN, h⟩

attribute [local instance] gtGroup

theorem exists_range {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (N : ℕ) {A : Type} [CommGroup A] (m : {g : GtPtF D F // GtTors D N g} → A)
    (minj : Function.Injective m) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ (H : Subgroup A) (a : TorChar D.X F N →* A), (∀ h, h ∈ H ↔ ∃ g, m g = h) ∧
      Nat.card H = Nat.card {g : GtPtF D F // GtTors D N g} ∧ Function.Injective a ∧
      ∀ τ, ∃ g, a τ = m g ∧ g.1 = torusPt D F (Additive.ofMul τ.1) := by
  let K := (nsmulAddMonoidHom N : GtPtF D F →+ GtPtF D F).ker
  let κ : K ≃ {g : GtPtF D F // GtTors D N g} := Equiv.subtypeEquivRight fun g => (GtCount.gtTors_iff N g).symm
  let ν : Multiplicative K →* A :=
    MonoidHom.mk' (fun g => m (κ g.toAdd)) fun g g' => madd _ _ _ ((isAdd_iff_eq _ _ _).2 rfl)
  have hν : Function.Injective ν := fun g g' h => κ.injective (minj h)
  let i : TorChar D.X F N →* Multiplicative K := MonoidHom.mk' (fun τ => Multiplicative.ofAdd
    ⟨torusPt D F (Additive.ofMul τ.1), show N • torusPt D F (Additive.ofMul τ.1) = 0 by
      rw [← map_nsmul, ← ofMul_pow, show τ.1 ^ N = 1 from τ.2, ofMul_one, map_zero]⟩)
    fun τ τ' => Subtype.ext (map_add (torusPt D F) (Additive.ofMul τ.1) (Additive.ofMul τ'.1))
  have iinj : Function.Injective i := fun τ τ' h =>
    Subtype.ext (Additive.ofMul.injective (torusPt_injective (congrArg Subtype.val h)))
  exact ⟨ν.range, ν.comp i, fun h => ⟨fun ⟨g, e⟩ => ⟨_, e⟩, fun ⟨g, e⟩ =>
      ⟨Multiplicative.ofAdd (κ.symm g), (congrArg m (κ.apply_symm_apply g)).trans e⟩⟩,
    (Nat.card_congr (MonoidHom.ofInjective hν).toEquiv).symm.trans (Nat.card_congr κ), hν.comp iinj,
    fun τ => ⟨κ (i τ).toAdd, rfl, rfl⟩⟩

theorem structure_of_acts (hL : Laws) (hL₂ : Laws2) {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] {I : Ideal V}
    {D : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
    [IsCommMonObj G] (U : PreU I D A G) (hg : A.g = D.P.g + D.rank) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] {N : ℕ} (hN : (N : F) ≠ 0) (S : ∀ α, SecA A F N →ₗ[F] CompMod D F N α)
    (hS : ∀ (v : SecA A F N) (s : Raw D F N), U.ExpF F N v.sec s ↔ s = fun α => (S α v).sec)
    (hS₀ : ∀ v, (∀ α, S α v = 0) → v = 0)
    (m : {g : GtPtF D F // GtTors D N g} → (TFK (R := V) F ⟶ A.A)) (minj : Function.Injective m)
    (mact : ∀ g, U.Acts F N 0 g.1 (m g)) (madd : ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') :
    ∃ Ψ : {g : GtPtF D F // GtTors D N g} → (SecA A F N ≃ₗ[F] SecA A F N), FiniteDimensional F (SecA A F N) ∧
      (∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank F (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule F (SecA A F N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  have hN0 : N ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hN1 : 0 < N := Nat.pos_of_ne_zero hN0
  obtain ⟨Φ, e, hd, cA, hθ, hm, hc, hn⟩ := exists_rep hL hL₂ A F hN
  have : Finite (TorsPt A (TFK (R := V) F) N) :=
    Nat.finite_of_card_ne_zero (cA.trans_ne (pow_ne_zero _ hN0))
  have fd : FiniteDimensional F (SecA A F N) :=
    Module.finite_of_finrank_pos ((pow_pos hN1 _).trans_eq hd.symm)
  obtain ⟨m', hm'⟩ : ∃ m' : {g : GtPtF D F // GtTors D N g} → TorsPt A (TFK (R := V) F) N,
    ∀ g, (m' g).1 = m g := ⟨fun g => ⟨m g, (mact g).1⟩, fun _ => rfl⟩
  have hΨ : ∀ g : {g : GtPtF D F // GtTors D N g}, ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.1.b) (DegPre.lineε N)), w.IsGen ∧
      ∀ v : SecA A F N, PhiRaw D F N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Φ (m' g) v)).sec := fun g => by
    obtain ⟨θ, h₁, h₂⟩ := hθ (m' g)
    obtain ⟨w, hw, h⟩ := (mact g).2 θ (h₁.trans (hm' g))
    exact ⟨w, hw, fun v => h _ _ _ _ ((hS v _).2 rfl) ((hS _ _).2 rfl) (h₂ v)⟩
  obtain ⟨H, a, hH, cH, ainj, ha⟩ := exists_range D F N m'
    (fun g g' h => minj ((hm' g).symm.trans ((congrArg Subtype.val h).trans (hm' g'))))
    fun g g' g'' h => Subtype.ext ((hm' g'').trans ((madd g g' g'' h).trans
      (congrArg₂ (· * ·) (hm' g) (hm' g')).symm))
  have cT : Nat.card (TorChar D.X F N) = N ^ D.rank := GtCount.card_torus_torsion D.X F N hN
  rw [(GtCount.card_gtTors hL hL₂ V D F N hN).1] at cH
  have k₁ : ∀ τ, ∃ c : Fˣ, ∀ v α, S α (Φ (a τ) v) = ((c * evalChar F N α τ : Fˣ) : F) • S α v :=
    fun τ => by
      obtain ⟨g, e₁, e₂⟩ := ha τ
      obtain ⟨w, hw, h⟩ := hΨ g
      obtain ⟨c, hc⟩ := phiRaw_torus hL.globalFns τ.1 e₂ g.2 hw
      rw [e₁]
      exact ⟨c, fun v => hc (fun α => S α v) (fun α => S α (Φ (m' g) v)) (h v)⟩
  have k₂ : ∀ h ∈ H, ∀ α v v' (c : F), S α v = c • S α v' → S α (Φ h v) = c • S α (Φ h v') := by
    intro x hx β v v' c e
    obtain ⟨g, rfl⟩ := (hH x).1 hx
    obtain ⟨w, hw, h⟩ := hΨ g
    exact phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Φ (m' g) v))
      (t := fun α => S α v') (t' := fun α => S α (Φ (m' g) v')) (h v) (h v') β c e
  refine ⟨fun g => Φ (m' g), fd, hΨ, fun α => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := classSub_structure hN e Φ (by rw [cA, Nat.cast_pow]; exact pow_ne_zero _ hN)
    (by rw [cA, hd, mul_comm, pow_mul]) hm hc hn S hS₀ a ainj k₁ H k₂ (by rw [cT, cH, cA, hg]; ring) α
  refine ⟨h₁, ?_, fun W hW hst => h₃ W hW fun x hx => ?_⟩
  · refine Nat.eq_of_mul_eq_mul_right (pow_pos hN1 D.rank) ?_
    rw [← cT, h₂, cT, ← pow_add, ← hg, hd]
  · obtain ⟨g, rfl⟩ := (hH x).1 hx
    exact hst g

theorem weight_structure (hL : Laws) (hL₂ : Laws2) : AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N →
    ∃ (S : ∀ α, SecA A (Kbar V) N →ₗ[Kbar V] CompMod D (Kbar V) N α)
      (Ψ : {g : GtPtF D (Kbar V) // GtTors D N g} → (SecA A (Kbar V) N ≃ₗ[Kbar V] SecA A (Kbar V) N)),
      FiniteDimensional (Kbar V) (SecA A (Kbar V) N) ∧
      (∀ (v : SecA A (Kbar V) N) (s : Raw D (Kbar V) N), U.ExpF (Kbar V) N v.sec s ↔ s = fun α => (S α v).sec) ∧
      (∀ v, (∀ α, S α v = 0) → v = 0) ∧
      (∀ g : {g : GtPtF D (Kbar V) // GtTors D N g},
        ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D (Kbar V) g.1.b) (DegPre.lineε N)), w.IsGen ∧
        ∀ v : SecA A (Kbar V) N, PhiRaw D (Kbar V) N 0 g.1 w (fun α => (S α v).sec) fun α => (S α (Ψ g v)).sec) ∧
      ∀ α, (∀ v, ∃ v' ∈ classSub S N α, ∀ mu, S (α + N • mu) v' = S (α + N • mu) v) ∧
        Module.finrank (Kbar V) (classSub S N α) = N ^ D.P.g ∧
        ∀ W : Submodule (Kbar V) (SecA A (Kbar V) N), W ≤ classSub S N α → (∀ g, ∀ v ∈ W, Ψ g v ∈ W) →
          W = ⊥ ∨ W = classSub S N α := by
  intro V _ _ _ hV D A G _ _ U N hN1
  have : IsNoetherianRing V := by have := hV.1; infer_instance
  have hN : (N : Kbar V) ≠ 0 := by
    have := hV.2.2
    have : CharZero (FractionRing V) := inferInstance
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨S, hS, hS₀⟩ := exists_expansion hL hL₂ V hV D A G U (Kbar V) N hN1
  obtain ⟨m, minj, mact, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action hL hL₂ V hV D A G U N hN1
  obtain ⟨Ψ, fd, h⟩ := structure_of_acts hL hL₂ U (PreU.dim_eq V hV D A G U) (Kbar V) hN S hS hS₀ m minj mact madd
  exact ⟨S, Ψ, fd, hS, hS₀, h⟩

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → (∀ (α : D.X) t s, U.ExpF (Kbar V) N t s → ∃ t' s', U.ExpF (Kbar V) N t' s' ∧ ∀ β, (∃ mu, β = α + N • mu) ∧ s' β = s β ∨ (¬ ∃ mu, β = α + N • mu) ∧ ∀ j, (s' β).f j = 0) ∧ (∀ α : D.X, ∃ mu, U.Supp (Kbar V) N (α + N • mu)) ∧ ∀ (α : D.X), U.Supp (Kbar V) N α → ∀ t s, U.ExpF (Kbar V) N t s → (∀ β, (¬ ∃ mu, β = α + N • mu) → ∀ j, (s β).f j = 0) → (∀ j, (s α).f j = 0) → ∀ j, t.f j = 0) := by
  intro hL hL₂ V _ _ _ hV D A G _ _ U N hN
  obtain ⟨S, Ψ, fd, hS, hS₀, hΨ, h⟩ := weight_structure hL hL₂ V hV D A G U N hN
  refine ⟨fun α t s hs => ?_, fun α => ?_, fun α ⟨t₀, s₀, h₀, j₀, hj₀⟩ t s hs hz hα => ?_⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain ⟨v', hv', e⟩ := (h α).1 (SecMod.mk _ t)
    refine ⟨v'.sec, _, (hS v' _).2 rfl, fun β => ?_⟩
    by_cases hβ : ∃ mu, β = α + N • mu
    · refine Or.inl ⟨hβ, ?_⟩
      obtain ⟨mu, rfl⟩ := hβ
      exact e mu
    · exact Or.inr ⟨hβ, (SecMod.eq_zero_iff_coord _).1 (hv' β hβ)⟩
  · have : Nontrivial (classSub S N α) :=
      Module.nontrivial_of_finrank_pos (R := Kbar V) ((pow_pos hN _).trans_eq (h α).2.1.symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : classSub S N α)
    obtain ⟨β, hβ⟩ := not_forall.1 fun e => hv (Subtype.ext (hS₀ v.1 e))
    obtain ⟨mu, rfl⟩ := not_not.1 fun e => hβ (v.2 β e)
    exact ⟨mu, v.1.sec, _, (hS v.1 _).2 rfl, not_forall.1 fun e => hβ ((SecMod.eq_zero_iff_coord _).2 e)⟩
  · obtain rfl := (hS (SecMod.mk _ t) s).1 hs
    obtain rfl := (hS (SecMod.mk _ t₀) s₀).1 h₀
    have st : ∀ g β v, S β v = 0 → S β (Ψ g v) = 0 := fun g β v e => by
      obtain ⟨w, hw, hp⟩ := hΨ g
      exact (phiRaw_smul hL.globalFns g.2 hw (s := fun α => S α v) (s' := fun α => S α (Ψ g v))
        (t := fun α => S α v) (t' := fun α => S α (Ψ g v)) (hp v) (hp v) β 0 (e.trans (zero_smul _ _).symm)).trans (zero_smul _ _)
    rcases (h α).2.2 (classSub S N α ⊓ LinearMap.ker (S α)) inf_le_left
      (fun g v hv => ⟨fun β hβ => st g β v (hv.1 β hβ), st g α v hv.2⟩) with e | e
    · have : SecMod.mk _ t ∈ classSub S N α ⊓ LinearMap.ker (S α) :=
        ⟨fun β hβ => (SecMod.eq_zero_iff_coord _).2 (hz β hβ), (SecMod.eq_zero_iff_coord _).2 hα⟩
      rw [e] at this
      exact (SecMod.eq_zero_iff_coord _).1 ((Submodule.mem_bot _).1 this)
    · obtain ⟨v', hv', e'⟩ := (h α).1 (SecMod.mk _ t₀)
      have e₁ : ∀ β, β = α + N • (0 : D.X) → S β v' = S β (SecMod.mk _ t₀) := fun β hβ => hβ ▸ e' 0
      have e₂ : S α v' = 0 := (e.symm ▸ hv' : v' ∈ classSub S N α ⊓ LinearMap.ker (S α)).2
      exact absurd ((SecMod.eq_zero_iff_coord _).1 ((e₁ α (by rw [nsmul_zero, add_zero])).symm.trans e₂) j₀) hj₀

end GlobalTheory.UU.Weight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfCubWeilOrthogonal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem mem_of_orthogonal_of_card {F : Type} [Field F] {M U : Type} [CommGroup M] [CommGroup U] (φ : U →* Fˣ)
    (hφ : Function.Injective φ) (N : ℕ) (w : M → M → U → Prop)
    (hex : ∀ x y, x ^ N = 1 → y ^ N = 1 → ∃! ζ, w x y ζ)
    (hmul : ∀ x x' y ζ ζ', w x y ζ → w x' y ζ' → w (x * x') y (ζ * ζ'))
    (hsymm : ∀ x y ζ, w x y ζ → w y x ζ⁻¹)
    (hfin : Nat.card {x : M // x ^ N = 1} ≠ 0)
    (hnd : ∀ x, x ^ N = 1 → (∀ y, y ^ N = 1 → w x y 1) → x = 1)
    (T H : Subgroup M) (hT : ∀ x ∈ T, x ^ N = 1) (hH : ∀ x ∈ H, x ^ N = 1)
    (hc : Nat.card T * Nat.card H = Nat.card {x : M // x ^ N = 1})
    (hTH : ∀ x ∈ T, ∀ y ∈ H, w x y 1) (x : M) (hx : x ^ N = 1) (hxH : ∀ y ∈ H, w x y 1) : x ∈ T := by
  let K : Subgroup M := (powMonoidHom N : M →* M).ker
  have hK : ∀ a, a ∈ K ↔ a ^ N = 1 := fun a => Iff.rfl
  have hcK : Nat.card K = Nat.card {x : M // x ^ N = 1} := rfl
  have : Finite K := Nat.finite_of_card_ne_zero (hcK ▸ hfin)
  have hex' : ∀ a b : K, ∃ ζ, w a b ζ := fun a b => (hex a b a.2 b.2).exists
  choose v hv using hex'
  have hu : ∀ (a b : K) ζ, w a b ζ → v a b = ζ := fun a b ζ h => (hex a b a.2 b.2).unique (hv a b) h
  have h1 : ∀ a a' b : K, v (a * a') b = v a b * v a' b :=
    fun a a' b => hu _ _ _ (hmul _ _ _ _ _ (hv a b) (hv a' b))
  have hs : ∀ a b : K, v b a = (v a b)⁻¹ := fun a b => hu _ _ _ (hsymm _ _ _ (hv a b))
  have hTK : T ≤ K := hT
  have hHK : H ≤ K := hH
  have key := (GlobalTheory.perfectPairing_orthogonal_of_card F K (fun a b => φ (v a b))
    (fun a a' b => by rw [h1, map_mul])
    (fun a b b' => by rw [hs (b * b') a, h1, mul_inv, ← hs, ← hs, map_mul])
    (fun a ha => Subtype.ext (hnd a a.2 fun y hy => by
      have h := hv a ⟨y, hy⟩
      rwa [hφ ((ha ⟨y, hy⟩).trans φ.map_one.symm)] at h))
    (T.subgroupOf K) (H.subgroupOf K)
    (fun t ht h hh => by rw [hu _ _ _ (hTH t ht h hh), map_one])
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hc, hcK])).1 ⟨x, hx⟩
  exact key.1 fun h hh => by rw [hu ⟨x, hx⟩ h _ (hxH h hh), map_one]

theorem mem_of_cubWeil_orthogonal : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ T H : Subgroup (TF (R := V) F ⟶ G), (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = N ^ (2 * A.g) → (∀ x ∈ T, ∀ y ∈ H, CubWeil s.P.c N x y 1) → ∀ x, x ^ N = 1 → (∀ y ∈ H, CubWeil s.P.c N x y 1) → x ∈ T := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N hN T H hT hH hc hTH x hx hxH
  obtain ⟨hcard, hnd⟩ := GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect hL V A G s F N hN
  let ε₀ : Γ(Spec (CommRingCat.of F), ⊤) ≃+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine mem_of_orthogonal_of_card (F := F) (M := TF (R := V) F ⟶ G) (U := Γ((TF (R := V) F).left, ⊤)ˣ)
    (Units.map ε₀.toMonoidHom) (Units.map_injective ε₀.injective) N (CubWeil s.P.c N)
    (fun _ _ hx hy => existsUnique_cubWeil _ hx hy) (fun _ _ _ _ _ h h' => h.mul_left h')
    (fun _ _ _ h => h.symm) ?_ hnd T H hT hH (hc.trans hcard.symm) hTH x hx hxH
  rw [hcard]
  exact pow_ne_zero _ (by omega)

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmallTorusPointKeepingRatiosIsZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

theorem le_of_sumV_sub {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {f g : Ix → F}
    (h : SumV v (fun i => f i - g i) 0) (i₀ i₁ : Ix) (q : ℚ) (hf : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (f i))
    (hg : ∀ i, i ≠ i₁ → (q : WithTop ℚ) ≤ v (g i)) : (q : WithTop ℚ) ≤ v (f i₀ - g i₁) := by
  classical
  obtain ⟨S, hS⟩ := h q
  have h₁ := hS (insert i₀ (insert i₁ S)) ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
  have m₀ : i₀ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_self _ _
  have m₁ : i₁ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h₂ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₀, f i) :=
    v.map_le_sum fun i hi => hf i (Finset.ne_of_mem_erase hi)
  have h₃ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₁, g i) :=
    v.map_le_sum fun i hi => hg i (Finset.ne_of_mem_erase hi)
  rw [Finset.sum_sub_distrib, ← Finset.add_sum_erase _ f m₀, ← Finset.add_sum_erase _ g m₁, zero_sub,
    v.map_neg] at h₁
  have := v.map_le_add (v.map_le_sub h₁ h₂) h₃
  convert this using 2
  ring

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  intro hL hT hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv k hk d o l ho hl hlQ H
  have hdb : d.b = 1 := SmallPoint.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv k hk d o l ho hl hlQ H
  have I := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have I' := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have K := GlobalTheory.UT.gt_onto_divisible_kernel hL V (maximalIdeal V) hA D F
  have hob : o.b = 1 := ((isZero_iff o).1 ho).1
  obtain ⟨l', hl', -⟩ := (I d).1
  have hll : ∀ χ, l χ = l' χ := by
    obtain ⟨w, hw⟩ := (coef_basic V D.toPre F 4 d).1
    obtain ⟨ω, hω, -⟩ := (I d).2.1 4 w hw
    have le : ∀ l₁ l₂, GtV hϖ hv d l₁ → GtV hϖ hv d l₂ → ∀ χ, l₁ χ ≤ l₂ χ := fun l₁ l₂ h₁ h₂ χ => by
      obtain ⟨s, hs, -, e⟩ := I' 4 le_rfl d w l₂ ω hw h₂ hω χ
      have := ((I d).2.2.2.2.2.2 4 (by omega) w s hw).2 l₁ ω 0 h₁ hω hs χ
      rw [e, WithTop.coe_le_coe] at this
      linarith
    exact fun χ => le_antisymm (le _ _ hl hl' χ) (le _ _ hl' hl χ)
  have hlow : ∀ m, -(Q m : ℚ) ≤ l' m := fun m => hll m ▸ (abs_le.1 (hlQ m)).1
  obtain ⟨t, ht, -⟩ := K.2.2.2.1 d hdb
  have hto : IsTor 1 o := ⟨hob, fun χ z J hJ => by
    rw [((isZero_iff o).1 ho).2 χ z J hJ, MonoidHom.one_apply, Units.val_one, Units.val_one, cst_eq, map_one]⟩
  have hadd : o.IsAdd d d := (K.2.2.2.2 1 t o d d hto ht).2 (by rwa [_root_.one_mul])
  have hQ0 : ∀ m, (0 : ℚ) ≤ Q m := fun m => (abs_nonneg _).trans (hlQ m)
  have A : ∀ (κ₀ : D.toPre.X) (n j : ℕ), 4 ≤ n → j = k * n →
      (((j : ℚ) - 1 - 2 * Q κ₀ : ℚ) : WithTop ℚ) ≤ v ((t (Multiplicative.ofAdd κ₀)).val - 1) := by
    intro κ₀ n j hn hj
    have hj4 : 4 ≤ j := hj ▸ le_trans hn (Nat.le_mul_of_pos_left _ hk)
    have hj1 : 1 ≤ j := by omega
    have hj0 : (0 : ℚ) < j := by exact_mod_cast hj1
    have hj1' : (1 : ℚ) ≤ j := by exact_mod_cast hj1
    obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F j o).2.1 hob
    obtain ⟨w', hw'⟩ := (coef_basic V D.toPre F j d).2.1 hdb
    obtain ⟨w, hw, Hw⟩ := H n j (by omega) hj w₁ hw₁
    obtain ⟨c, hc0, vc, ec⟩ := ((coef_basic V D.toPre F j d).2.2 w' hw'.1).2.2.1 w hw
    have et := ((coef_basic V D.toPre F j o).2.2 w₁ hw₁.1).2.2.2 t d d w' ht hadd
      (fun z J hJ => (hw'.2 z J hJ).trans (hw₁.2 z J hJ).symm)
    obtain ⟨ω, hcω⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)
    have hω : GenV hϖ hv w ω := by
      obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, e⟩ := (I d).2.2.1 j w' hw' hdb
      refine ⟨φ₀, hφ, t₀, ht₀, c * x, by rw [v.map_mul, hx, ← hcω]; simp, fun z J hJ => ?_⟩
      rw [vc z J hJ, e z J hJ, cst_eq, cst_eq, cst_eq, map_mul, _root_.mul_assoc]
    have hω₁ := (I o).2.2.1 j w₁ hw₁ hob
    obtain ⟨S₁, n₁, -, e₁⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ κ₀
    obtain ⟨S₂, n₂, z₂, e₂⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ 0
    rw [Pi.zero_apply, add_zero, add_zero] at e₁ e₂
    rw [QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at e₂
    have hQj : ∀ mu, (Q (j • mu) : ℚ) / j = j * Q mu := fun mu => by
      rw [Q_nsmul hϖ hQ]; push_cast; field_simp
    have hQs : ∀ mu, (Q κ₀ : ℚ) / j + j * Q mu - Q mu - Q κ₀ ≤ (Q (κ₀ + j • mu) : ℚ) / j := fun mu => by
      have h0 := hQ0 (mu + κ₀)
      have : (Q (κ₀ + j • mu) : ℚ) / j = Q κ₀ / j + j * Q mu + (Q (mu + κ₀) - Q mu - Q κ₀) := by
        rw [q_shift hϖ hQ, QForm.bOf]; push_cast; field_simp; ring
      linarith
    have bo : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j : ℚ) : WithTop ℚ) ≤ v (coef S o w₁ χ) := fun S hS χ => by
      have := ((I o).2.2.2.2.2.2 j hj1 w₁ S hw₁.1).2 0 0 0 (gtV_zero ho) hω₁ hS χ
      rwa [Pi.zero_apply, add_zero, add_zero, zero_add] at this
    have bd : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j + l' χ + ω : ℚ) : WithTop ℚ) ≤ v (coef S d w χ) := fun S hS χ => by
      have := ((I d).2.2.2.2.2.2 j hj1 w S hw).2 l' ω 0 hl' hω hS χ
      rwa [zero_add] at this
    have hQ1 : ∀ mu : D.toPre.X, mu ≠ 0 → (1 : ℚ) ≤ Q mu := fun mu h => by
      exact_mod_cast QForm.Q_pos hϖ D hQ h
    have z₂' : ∀ (g : GtPtF D.toPre F) (u : Frm D.toPre F j g.b) (χ), (¬ ∃ mu, χ = j • mu) → coef S₂ g u χ = 0 :=
      fun g u χ e => coef_zero S₂ g u (z₂ χ fun mu h => e ⟨mu, by rw [h, zero_add]⟩)
    have hne : ¬ SumV v (coef S₂ o w₁) 0 := fun h => by
      have := le_of_sumV h 0 1 fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          refine le_trans (WithTop.coe_le_coe.2 ?_) (bo S₂ n₂ _)
          have := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [hQj]
          nlinarith
        · rw [z₂' o w₁ χ e, v.map_zero]; exact le_top
      rw [e₂, WithTop.coe_le_coe] at this
      linarith
    have key := le_of_sumV_sub (Hw S₁ S₂ hne κ₀) κ₀ 0 (ω + (Q κ₀ : ℚ) / j + ((j : ℚ) - 1 - 2 * Q κ₀))
      (fun χ hχ => by
        by_cases e : ∃ mu, κ₀ - χ = j • mu
        · obtain ⟨mu, e⟩ := e
          obtain rfl : χ = κ₀ + j • (-mu) := by rw [smul_neg, ← e]; abel
          have h1 := hQ1 (-mu) fun e => hχ (by rw [e, smul_zero, add_zero])
          rw [v.map_mul, e]
          refine le_trans ?_ (add_le_add (bd S₁ n₁ _) (bo S₂ n₂ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, ← QForm.Q_neg hϖ D hQ mu, map_add (f := _), map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          have h3 := hlow κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow (-mu)) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' o w₁ _ e, MulZeroClass.mul_zero, v.map_zero]; exact le_top)
      (fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          have h1 := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [v.map_mul, sub_eq_add_neg κ₀, ← smul_neg]
          refine le_trans ?_ (add_le_add (bd S₂ n₂ _) (bo S₁ n₁ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          rw [QForm.Q_neg hϖ D hQ mu] at h2
          have h3 := hQ0 κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow mu) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' d w _ e, MulZeroClass.zero_mul, v.map_zero]; exact le_top)
    rw [sub_self, sub_zero, ec, ec, et, et, ofAdd_zero, map_one, Units.val_one,
      show c * ((t (Multiplicative.ofAdd κ₀)).val * coef S₁ o w₁ κ₀) * coef S₂ o w₁ 0 -
        c * (1 * coef S₂ o w₁ 0) * coef S₁ o w₁ κ₀ =
        c * coef S₁ o w₁ κ₀ * coef S₂ o w₁ 0 * ((t (Multiplicative.ofAdd κ₀)).val - 1) by ring,
      v.map_mul, v.map_mul, v.map_mul, ← hcω, e₁, e₂, ← WithTop.coe_add, ← WithTop.coe_add, add_zero,
      WithTop.coe_add (ω + (Q κ₀ : ℚ) / j)] at key
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 key
  have B : ∀ κ₀, (t (Multiplicative.ofAdd κ₀)).val = 1 := fun κ₀ => by
    by_contra hx
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 (sub_ne_zero.2 hx))
    obtain ⟨n, hn⟩ := exists_nat_gt (q + 1 + 2 * Q κ₀)
    have e := A κ₀ (n + 4) _ (by omega) rfl
    rw [← hq, WithTop.coe_le_coe] at e
    have : ((n + 4 : ℕ) : ℚ) ≤ ((k * (n + 4) : ℕ) : ℚ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hk
    push_cast at this e
    linarith
  refine (isZero_iff d).2 ⟨hdb, fun χ z J hJ => Units.ext ?_⟩
  rw [ht.2 χ z J hJ, B, cst_eq, map_one, Units.val_one]

end GlobalTheory.UT.SmallZero
end
end

