module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.RealTh

theorem exists_pow_eq (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    {k : ℕ} (hk : (k : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ k = 1) : ∃ y : Over.mk x ⟶ P.A, y ^ k = z := by
  have := P.isAb.comm
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have hk2 : ((k ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hk
  have c₁ := TorsionFieldExt.card_torsion hL P x hk
  have c₂ := TorsionFieldExt.card_torsion hL P x hk2
  let H₁ := (powMonoidHom k : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  let H₂ := (powMonoidHom (k ^ 2) : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  have e₁ : Nat.card H₁ = k ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₁, MonoidHom.mem_ker])).trans c₁
  have e₂ : Nat.card H₂ = (k ^ 2) ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₂, MonoidHom.mem_ker])).trans c₂
  have : Finite H₂ := Nat.finite_of_card_ne_zero (by rw [e₂]; positivity)
  have : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [e₁]; positivity)
  let ψ : H₂ →* (Over.mk x ⟶ P.A) := (powMonoidHom k).comp H₂.subtype
  have hker : Nat.card ψ.ker = k ^ (2 * P.g) := by
    rw [← e₁]
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1.1, ?_⟩) ⟨fun a b h => ?_, fun a => ?_⟩)
    · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)
    · apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : H₁ => (q : Over.mk x ⟶ P.A)) h
    · refine ⟨⟨⟨a.1, ?_⟩, ?_⟩, rfl⟩
      · have := a.2
        simp only [H₁, MonoidHom.mem_ker, powMonoidHom_apply] at this
        simp [H₂, MonoidHom.mem_ker, sq, pow_mul, this]
      · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 a.2)
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker, e₂, ← pow_mul, mul_comm 2, pow_mul,
    sq, mul_comm] at hmul
  have hrange : Nat.card ψ.range = Nat.card H₁ := by
    rw [e₁]
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) hmul).symm
  have hle : ψ.range ≤ H₁ := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H₂, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [ψ, H₁, MonoidHom.mem_ker, ← pow_mul, ← sq, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle hrange.ge
  have hzm : z ∈ ψ.range := heq ▸ (show z ∈ H₁ by simpa [H₁, MonoidHom.mem_ker] using hz)
  obtain ⟨y, hy⟩ := hzm
  exact ⟨y.1, hy⟩

end GlobalTheory.UMin.RealTh


open GlobalTheory.UMin.RealTh in
theorem GlobalTheory.UMin.thList_real : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i N pt c H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hkK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := S.unit.map (i.comp (algebraMap o S.R))
    rw [map_natCast] at this
    exact this.ne_zero
  let β : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  let u : Over.mk (spMap j ≫ spMap i ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp S.R)) := Over.homMk (spMap j) rfl
  have hkK' : ((S.r * S.N : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast j]; exact (map_ne_zero j).2 hkK
  have down : ∀ y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A, y ^ (S.r * S.N) = 1 → ∃ b, y = β ≫ ρ.pt b := by
    intro y hy
    obtain ⟨b, hb, -⟩ := ρ.pt_bij (AlgebraicClosure K) (spMap j ≫ spMap i ≫ 𝟙 _) (u ≫ y)
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
    refine ⟨b, TorsionFieldExt.comp_injective u _ ?_⟩
    refine hb.symm.trans (Over.OverMorphism.ext ?_)
    simp [u, β]
  constructor
  · intro x
    have h := H.2.1 x
    obtain ⟨b, hb⟩ := down (pt x ^ (S.r * S.N)) (by rw [← pow_mul, ← sq]; exact h.1)
    exact ⟨b, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt x) (c x) hb h⟩
  · intro b
    have tb : ρ.pt b ^ (S.r * S.N) = 1 := (ρ.fr_tors b).1
    obtain ⟨y, hy⟩ := exists_pow_eq hL ρ.P (spMap j ≫ spMap i ≫ 𝟙 _) hkK' (u ≫ β ≫ ρ.pt b)
      (by rw [← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    obtain ⟨a, ha⟩ := H.2.2 (AlgebraicClosure K) j y
      (by rw [sq, pow_mul, hy, ← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    have e1 : u ≫ pt a = y := Over.OverMorphism.ext ha.symm
    have e2 : pt a ^ (S.r * S.N) = β ≫ ρ.pt b :=
      TorsionFieldExt.comp_injective u _ (by
        show u ≫ _ = u ≫ _
        rw [MonObj.comp_pow, e1, hy])
    exact ⟨a, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt a) (c a) e2 (H.2.1 a)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFiniteOfPolarisedAVIsoAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

noncomputable section

namespace GlobalTheory.ThetaFiniteIso

theorem thetaPts_finite : ∀ (G N' : ℕ) (J : Type) (K : Type) [Field K] [IsAlgClosed K] (b : TBase K (N' ^ 2)) (Q : PolAV (Sp K)), Odd N' → 3 ≤ N' → ∃ V : Set (Ix G (N' ^ 2) → K), V.Finite ∧ ∀ t : TObj G (N' ^ 2) J b (𝟙 (Sp K)), (∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left)) → ∃ v ∈ V, t.HasTh (𝟙 _) v := by
  intro G N' J K _ _ b Q ho _
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ ho.pos.ne'⟩
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  let T₀ : Over (Sp K) := Over.mk (T.hom ≫ 𝟙 (Sp K))
  let fn : K → Γ(T.left, ⊤) := fun c => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c
  let Tor := {y : T₀ ⟶ Q.A // y ^ (N' ^ 2) = 1}
  have e : T₀ ≅ 𝟙_ (Over (Sp K)) :=
    (CartesianMonoidalCategory.isTerminalTensorUnit).uniqueUpToIso
      (IsTerminal.ofUniqueHom (fun Y => Over.homMk Y.hom (by simp [T₀, T]))
        (fun Y m => Over.OverMorphism.ext (by simpa [T₀, T] using Over.w m))) |>.symm
  haveI hTor : Finite Tor := by
    have := GlobalTheory.AbTorsionFinite.finite_torsion K Q.A Q.isAb (N' ^ 2) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ ho.pos.ne'))
    refine Finite.of_injective (fun y : Tor => (⟨e.inv ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩ :
      {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Q.A // x ^ (N' ^ 2) = 1})) ?_
    intro y y' h
    exact Subtype.ext ((cancel_epi e.inv).1 (congrArg Subtype.val h))
  let ch : (Ix G (N' ^ 2) → Tor) → (Ix G (N' ^ 2) → K) := fun l =>
    if h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) then h.choose else 0
  refine ⟨Set.range ch, Set.finite_range ch, fun t ⟨φ, hφ, hw⟩ => ?_⟩
  haveI := hφ
  let x : Ix G (N' ^ 2) → (T ⟶ t.pol.A) := fun a => (Over.homMk (𝟙 (Sp K)) (by simp [T]) : T ⟶ Out.baseOver (Sp K)) ≫ t.lab a
  have hk : ∀ a, x a ^ (N' ^ 2) = 1 := fun a => by
    exact (MonObj.comp_pow _ _ _).symm.trans ((congrArg (_ ≫ ·) (GlobalTheory.ThetaPtUp.lab_pow t a)).trans (MonObj.comp_one _))
  let x₀ : Ix G (N' ^ 2) → (T₀ ⟶ Q.A) := fun a => Over.homMk ((x a).left ≫ φ.hom.left) (by
    exact (Category.assoc _ _ _).trans ((congrArg ((x a).left ≫ ·) (Over.w φ.hom)).trans
      ((Over.w (x a)).trans (Category.comp_id _).symm)))
  have hx : ∀ a, (x₀ a).left = (x a).left ≫ φ.hom.left := fun a => rfl
  have hp : IsGrpPullback t.pol.A Q.A (𝟙 (Sp K)) φ.hom.left := isGrpPullback_of_iso φ
  have key : ∀ v : Ix G (N' ^ 2) → K, t.HasTh (𝟙 _) v ↔ IsThetaPt Q N' x₀ (fun a => fn (v a)) := fun v =>
    GlobalTheory.ThetaPtUp.isThetaPt_iff (P := t.pol) (P₀ := Q) (T := T) hp hw hx hk _
  let r : T₀ ⟶ T := Over.homMk (𝟙 (Sp K)) (by simp [T₀, T])
  have hk₀ : ∀ a, x₀ a ^ (N' ^ 2) = 1 := fun a => by
    have e₁ : x₀ a = r ≫ x a ≫ φ.hom := Over.OverMorphism.ext (Category.id_comp _).symm
    have h2 : (x a ≫ φ.hom) ^ (N' ^ 2) = 1 := by
      have := map_pow (IsMonHom.monoidHom φ.hom T) (x a) (N' ^ 2)
      have h1 : IsMonHom.monoidHom φ.hom T (x a ^ (N' ^ 2)) = 1 := by
        erw [hk a]; exact map_one _
      exact this.symm.trans h1
    rw [e₁, ← MonObj.comp_pow, h2, MonObj.comp_one]
  let l : Ix G (N' ^ 2) → Tor := fun a => ⟨x₀ a, hk₀ a⟩
  obtain ⟨v, hv⟩ := GlobalTheory.FamRep.exists_hasTh_field GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 ho t K (𝟙 _)
  have h : ∃ v : Ix G (N' ^ 2) → K, IsThetaPt Q N' (fun a => (l a).1) (fun a => fn (v a)) := ⟨v, (key v).1 hv⟩
  refine ⟨ch l, ⟨l, rfl⟩, (key _).2 ?_⟩
  simp only [ch, dif_pos h]
  exact h.choose_spec

end GlobalTheory.ThetaFiniteIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsIntegralUnitMemberUniformisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.PrimModel

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := by
  simp [spMap]

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem heq_pullS {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) {T : Over S}
    (f₁ : Over.mk x₁ ⟶ T) (f₂ : Over.mk x₂ ⟶ T) (hf : f₁.left = f₂.left)
    (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) :
    HEq (VVRank.pullS G _ f₁ s) (VVRank.pullS G _ f₂ s) := by
  subst h
  obtain rfl : f₁ = f₂ := Over.OverMorphism.ext hf
  rfl

theorem thList_of_eq (ρ : LB.Gen (L.pull (eSec G))) (m : ℕ) {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S}
    (h : x₁ = x₂) {θ₁ : SecAt G L x₁} {θ₂ : SecAt G L x₂} (hθ : HEq θ₁ θ₂) {N : ℕ}
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ θ₁ pt c) :
    ∃ pt₂ : Fin N → (Over.mk x₂ ⟶ G), (∀ a, (pt₂ a).left = (pt a).left) ∧ ThList G L ρ m x₂ θ₂ pt₂ c := by
  subst h
  cases hθ
  exact ⟨pt, fun _ => rfl, H⟩

theorem pt_of_eq {R : Type} [CommRing R] {x₁ x₂ : Sp R ⟶ S} (h : x₁ = x₂) (p : Over.mk x₁ ⟶ G) :
    ∃ p₂ : Over.mk x₂ ⟶ G, p₂.left = p.left ∧ ∀ n : ℕ, p ^ n = 1 → p₂ ^ n = 1 := by
  subst h
  exact ⟨p, rfl, fun _ h => h⟩

theorem thG_unique [IsCommMonObj G] (ρ : LB.Gen (L.pull (eSec G))) (hL : L.IsLB) (hρ : ρ.IsGen) {g m : ℕ}
    {K : Type} [Field K] {x : Sp K ⟶ S} (θ : SecAt G L x) (p : Over.mk x ⟶ G) {c c' : K} (hm : Odd m)
    (hm0 : (m : K) ≠ 0) (hP : PolFib G L g x) (h₁ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c))
    (h₂ : ThG G L ρ m θ p (GlobalTheory.ZH.fn c')) : c' = c := by
  have := (GlobalTheory.UMin.thG_smul_iff S G L ρ hL hρ g m K x θ θ p 1 c c' hm hm0 hP (by simp) h₁).1 h₂
  simpa using this
end

theorem isIntegralElem_of_sq {V F K Kb : Type} [CommRing V] [Field F] [Field K] [Field Kb] (φ : V →+* F) (i : V →+* K)
    (i' : K →+* Kb) (j : F →+* Kb) (hsq : i'.comp i = j.comp φ) {z : F} {w : K} (h : j z = i' w)
    (hz : φ.IsIntegralElem z) : i.IsIntegralElem w := by
  obtain ⟨p, hp, hp0⟩ := hz
  refine ⟨p, hp, i'.injective ?_⟩
  rw [Polynomial.hom_eval₂, ← h, hsq, ← Polynomial.hom_eval₂, hp0, map_zero, map_zero]

theorem polFib_unif {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] {D : DegData W (IsLocalRing.maximalIdeal W)}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (IsLocalRing.maximalIdeal W) D A G) (R : Type) [CommRing R] (y : Sp R ⟶ Sp (FractionRing W)) :
    PolFib G U.LG.L A.g (y ≫ jK W) := by
  have hα : IsGrpPullback A.A G (jK W) (U.gen.inv.left ≫ pullback.fst G.hom (jK W)) :=
    GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK W) G U.gen U.gen_hom
  have hA := A.isLB
  have hLG : U.LG.L.IsLB := RigLB.isLB _
  have hLα : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK W))) := by
    obtain ⟨w, hw⟩ := U.ext
    have hB : LBIso A.L ((A.L.pull U.gen.hom.left).pull U.gen.inv.left) := by
      have e : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
        rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
      have h1 := GlobalTheory.UMin.FibMove.lbIso_pull_comp hA U.gen.hom.left U.gen.inv.left
      rw [e] at h1
      exact LBIso.trans hA (pull_isLB hA _) (pull_isLB (pull_isLB hA _) _)
        (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) h1
    exact GlobalTheory.ThetaAffineGlue.lbIso_comp hA (pull_isLB hA _) hLG hB ⟨w, hw⟩
  exact (GlobalTheory.UMin.FibMove.polFib_move (Sp W) (Sp (FractionRing W)) G U.LG.L A.A A.L (jK W) _ hLG hA hα hLα A.g R
    y).1.mp (GlobalTheory.UMin.FibExist.polFib_of_point _ A R y)

theorem main : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W], IsAdicComplete (IsLocalRing.maximalIdeal W) W → ∀ (D : DegData W (IsLocalRing.maximalIdeal W)) (A : PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal W) D A G) (σ : SecAt G U.LG.L (𝟙 (Sp W))), NZ G U.LG.L (𝟙 (Sp W)) σ → ∀ (m N : ℕ), Odd m → 3 ≤ m → IsUnit (m : W) → ∀ (K : Type) [Field K] [IsAlgClosed K] (i : W →+* K) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp W)) ⟶ G)) (c : Fin N → K), Function.Injective i → ThList G U.LG.L U.LG.rig m (spMap i ≫ 𝟙 (Sp W)) (SecAt.pull G U.LG.L σ i) pt c → Prim i c := by
  intro W _ _ _ _ hc D A G _ _ hG U σ hσ m N hodd h3 hmu K _ _ i pt c hi hL
  have hV : GlobalTheory.LN.CDvr W := ⟨inferInstance, hc, inferInstance⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  let F := AlgebraicClosure (FractionRing W)
  obtain ⟨v, hv⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_valOver hϖ F
  choose Q hQ using ReciprocityTheory.ChartRestriction.G.DVR.QForm.exists_QVal hϖ D
  let g := A.g
  set x' : Sp F ⟶ Sp W := jFK (R := W) F ≫ jK W with hx'
  let ξ : Over.mk x' ⟶ Over.mk (𝟙 (Sp W)) := Over.homMk x' (Category.comp_id _)
  set θF : SecAt G U.LG.L x' := VVRank.pullS G _ ξ σ with hθF
  obtain ⟨hA, x0, c0, hx0, hv0⟩ := (GlobalTheory.Ex.OnModel.theta_on_model GlobalTheory.lawsAndExpansions W hc ϖ hϖ D Q hQ F v hv A G hG U
    σ hσ).2 m hodd hmu h3 ξ
  let φF : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W))
  have hPF : PolFib G U.LG.L g x' := polFib_unif U F (jFK (R := W) F)
  have hmF : (m : F) ≠ 0 := by
    have := hmu.map φF
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨ptF, cF, hLF⟩ := GlobalTheory.UMin.exists_thList (Sp W) G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen g m (m ^ (4 * g)) F x'
    θF hodd hmF rfl hPF
  let Kb := AlgebraicClosure K
  let i' : K →+* Kb := algebraMap K Kb
  have hii : Function.Injective (i'.comp i) := i'.injective.comp hi
  let e : FractionRing W →+* Kb := IsFractionRing.lift hii
  letI : Algebra (FractionRing W) Kb := e.toAlgebra
  let j : F →+* Kb := (IsAlgClosed.lift : F →ₐ[FractionRing W] Kb).toRingHom
  have hsq : i'.comp i = j.comp φF := by
    ext r
    change _ = (IsAlgClosed.lift : F →ₐ[FractionRing W] Kb) (algebraMap (FractionRing W) F _)
    rw [AlgHom.commutes]
    exact (IsFractionRing.lift_algebraMap hii r).symm
  have hy : spMap i' ≫ spMap i ≫ 𝟙 (Sp W) = spMap j ≫ x' := by
    rw [Category.comp_id]
    change _ = spMap j ≫ (spMap (algebraMap (FractionRing W) F) ≫ spMap (algebraMap W (FractionRing W)))
    rw [← Category.assoc, spMap_comp', spMap_comp', spMap_comp', hsq]
  have hPy : PolFib G U.LG.L g (spMap j ≫ x') := by
    have := polFib_unif U Kb (spMap j ≫ jFK (R := W) F)
    simpa only [hx', Category.assoc] using this
  have hmKb : (m : Kb) ≠ 0 := by
    have := hmu.map (i'.comp i)
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt1, hpt1, hL1⟩ := GlobalTheory.UMin.ThPull.thList_pull (Sp W) G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen m N K Kb i'
    (spMap i ≫ 𝟙 (Sp W)) (SecAt.pull G U.LG.L σ i) pt c hL
  have hθ : HEq (SecAt.pull G U.LG.L (SecAt.pull G U.LG.L σ i) i') (SecAt.pull G U.LG.L θF j) := by
    simp only [SecAt.pull, hθF, GlobalTheory.ThetaRuleCompare.pullS_comp]
    refine heq_pullS hy _ _ ?_ σ
    simp only [Over.comp_left, Over.homMk_left]
    change spMap i' ≫ spMap i = spMap j ≫ (spMap (algebraMap (FractionRing W) F) ≫ spMap (algebraMap W (FractionRing W)))
    rw [spMap_comp', spMap_comp', spMap_comp', hsq]
  obtain ⟨ptK, hptK, hLK⟩ := thList_of_eq U.LG.rig m hy hθ hL1
  obtain ⟨ptF', hptF', hLF'⟩ := GlobalTheory.UMin.ThPull.thList_pull (Sp W) G U.LG.L U.LG.rig U.LG.isLB U.LG.rigGen m (m ^ (4 * g))
    F Kb j x' θF ptF cF hLF
  have hint : ∀ b, φF.IsIntegralElem (cF b) := fun b =>
    _root_.GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg W hV ϖ hϖ F v hv (cF b) (hA (ptF b) (cF b) (hLF.2.1 b))
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hLF.2.2 Kb j (ptK a) (hLK.2.1 a).1
    have heq : ptK a = ptF' b := Over.OverMorphism.ext (hb.trans (hptF' b).symm)
    have h1 := hLK.2.1 a
    rw [heq] at h1
    have hab : j (cF b) = i' (c a) :=
      thG_unique U.LG.rig U.LG.isLB U.LG.rigGen _ (ptF' b) hodd hmKb hPy h1 (hLF'.2.1 b)
    exact isIntegralElem_of_sq φF i i' j hsq hab (hint b)
  · obtain ⟨x0', hx0'l, hx0't⟩ := pt_of_eq (show x' = spMap (RingHom.id F) ≫ x' by rw [spMap_id', Category.id_comp]) x0
    obtain ⟨b0, hb0⟩ := hLF.2.2 F (RingHom.id F) x0' (hx0't _ hx0.1)
    have hx0b : x0 = ptF b0 := Over.OverMorphism.ext (by rw [← hx0'l, hb0, spMap_id', Category.id_comp])
    subst hx0b
    have hc0b : cF b0 = c0 :=
      thG_unique U.LG.rig U.LG.isLB U.LG.rigGen θF (ptF b0) hodd hmF hPF hx0 (hLF.2.1 b0)
    obtain ⟨q, hql, hqt⟩ := pt_of_eq hy.symm (ptF' b0)
    obtain ⟨a0, ha0⟩ := hL.2.2 Kb i' q (hqt _ (hLF'.2.1 b0).1)
    have heq : ptK a0 = ptF' b0 := Over.OverMorphism.ext (by rw [hptK, hpt1, ← ha0, hql])
    have h1 := hLK.2.1 a0
    rw [heq] at h1
    have hab : j c0 = i' (c a0) := by
      rw [← hc0b]
      exact thG_unique U.LG.rig U.LG.isLB U.LG.rigGen _ (ptF' b0) hodd hmKb hPy h1 (hLF'.2.1 b0)
    have hc0 : c0 ≠ 0 := by
      rintro rfl
      simp at hv0
    have hca : c a0 ≠ 0 := by
      intro h
      rw [h, map_zero] at hab
      exact hc0 (j.injective (hab.trans (map_zero j).symm))
    refine ⟨a0, hca, isIntegralElem_of_sq φF i i' j hsq (z := c0⁻¹) (by rw [map_inv₀, map_inv₀, hab]) ?_⟩
    refine _root_.GlobalTheory.IntOverCdvr.isIntegralElem_of_val_nonneg W hV ϖ hϖ F v hv _ ?_
    have h01 : v c0 + v c0⁻¹ = 0 := by
      rw [← AddValuation.map_mul, mul_inv_cancel₀ hc0, AddValuation.map_one]
    rw [hv0, zero_add] at h01
    rw [h01]

end GlobalTheory.UMin.PrimModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsListedFiniteGaloisExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalTh

theorem thList_galois : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (pt : Fin N → (Over.mk (spMap (algebraMap Ω Ω') ≫ x) ⟶ G)) (c : Fin N → Ω'), FiniteDimensional Ω Ω' ∧ IsGalois Ω Ω' ∧ Module.finrank Ω Ω' ∣ N.factorial ∧ ThList G L ρ m (spMap (algebraMap Ω Ω') ≫ x) (SecAt.pull G L θ (algebraMap Ω Ω')) pt c ∧ ∀ τ : Ω' ≃ₐ[Ω] Ω', ∃ σ : Equiv.Perm (Fin N), ∀ a, τ (c a) = c (σ a) := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ hm hN hP
  classical
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  have hid : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  have fibBase : ∀ {R R' : Type} [CommRing R] [CommRing R'] (y : Sp R ⟶ S) (i : R →+* R'),
      PolFib G L g y → PolFib G L g (spMap i ≫ y) := fun y i h =>
    (GlobalTheory.UMin.FibMove.polFib_move S S G L G L (𝟙 S) (𝟙 G.left) hL hL hp hid g _ y).2 _ i h
  let K := AlgebraicClosure Ω
  let ι₀ : Ω →+* K := algebraMap Ω K
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap Ω K).injective
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have hPK : PolFib G L g (spMap ι₀ ≫ x) := fibBase x ι₀ hP
  obtain ⟨ptK, cK, hK⟩ := GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m N K (spMap ι₀ ≫ x) (SecAt.pull G L θ ι₀) hm hmK hN hPK
  obtain ⟨φ, hφ⟩ := GlobalTheory.UMin.GalConj.thList_conj S G L ρ hL hρ g m N Ω K x θ ptK cK hm hmK hPK hK
  obtain ⟨hfd, hgal, hdeg⟩ := GlobalTheory.fixedField_ker_toPerm_finite_isGalois_finrank_dvd Ω K N φ
  set Ω' := IntermediateField.fixedField φ.ker with hΩ'
  have hfix : ∀ a, ∀ τ ∈ φ.ker, spMap (τ : K →+* K) ≫ (ptK a).left = (ptK a).left := fun a τ hτ => by
    have h1 := (hφ τ a).1
    rwa [MonoidHom.mem_ker.1 hτ, Equiv.Perm.one_apply] at h1
  choose q hq using fun a => exists_descend φ.ker (ptK a).left (hfix a)
  let inc : Ω' →+* K := algebraMap Ω' K
  let j : Ω →+* Ω' := algebraMap Ω Ω'
  have hincj : inc.comp j = ι₀ := (IsScalarTower.algebraMap_eq Ω Ω' K).symm
  have hqo : ∀ a, q a ≫ G.hom = spMap j ≫ x := fun a => sp_cancel inc _ _ (by
    rw [← Category.assoc, hq a, Over.w (ptK a), ← Category.assoc, ← sp_comp, hincj]; rfl)
  let pt' : Fin N → (Over.mk (spMap j ≫ x) ⟶ G) := fun a => Over.homMk (q a) (hqo a)
  let u : Over.mk (spMap ι₀ ≫ x) ⟶ Over.mk (spMap j ≫ x) :=
    Over.homMk (spMap inc) (by
      show spMap inc ≫ spMap j ≫ x = spMap ι₀ ≫ x
      rw [← Category.assoc, ← sp_comp, hincj])
  have hu : ∀ a, u ≫ pt' a = ptK a := fun a => Over.OverMorphism.ext (by simp [u, pt', hq a])
  have hinj' : Function.Injective pt' := fun a b h => hK.1 (by rw [← hu a, ← hu b, h])
  have htor : ∀ a, pt' a ^ (m ^ 2) = 1 := fun a => by
    have e : u ≫ pt' a ^ (m ^ 2) = u ≫ 1 := by rw [MonObj.comp_pow, hu, (hK.2.1 a).1, MonObj.comp_one]
    have e2 := congrArg (fun f => f.left) e
    simp only [Over.comp_left] at e2
    exact Over.OverMorphism.ext (sp_cancel inc _ _ e2)
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  have hm' : (m : Ω') ≠ 0 := Nat.cast_ne_zero.2 hm0
  have hP' : PolFib G L g (spMap j ≫ x) := fibBase x j hP
  choose c' hc' using fun a => GlobalTheory.UMin.exists_thG_of_polFib_field S G L ρ hL hρ g m Ω' (spMap j ≫ x) (SecAt.pull G L θ j) (pt' a) hm hm' hP' (htor a)
  have hT : ThList G L ρ m (spMap j ≫ x) (SecAt.pull G L θ j) pt' c' := by
    refine ⟨hinj', hc', fun K'' _ _ i p hpm => ?_⟩
    have hm'' : (m : K'') ≠ 0 := by rw [← map_natCast i]; exact (map_ne_zero i).2 hm'
    obtain ⟨pt₂, c₂, h₂⟩ := GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m N K'' (spMap i ≫ spMap j ≫ x)
      (SecAt.pull G L (SecAt.pull G L θ j) i) hm hm'' hN (fibBase _ i hP')
    let w : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
    have hv : ∀ a, ∃ b, w ≫ pt' a = pt₂ b := fun a =>
      thList_exh h₂ _ (by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
    choose π hπ using hv
    have hπi : Function.Injective π := fun a b h => hinj' (Over.OverMorphism.ext (sp_cancel i _ _ (by
      have := congrArg (fun f => f.left) ((hπ a).trans ((congrArg pt₂ h).trans (hπ b).symm))
      simpa [w] using this)))
    obtain ⟨b, hb⟩ := thList_exh h₂ p hpm
    obtain ⟨a, rfl⟩ := (Finite.injective_iff_surjective.1 hπi) b
    refine ⟨a, ?_⟩
    rw [hb, ← hπ a]; rfl
  refine ⟨Ω', inferInstance, inferInstance, pt', c', hfd, hgal, hdeg, hT, fun τ => ?_⟩
  obtain ⟨pt'', -, h''⟩ := GlobalTheory.UMin.ThPull.thList_pull S G L ρ hL hρ m N Ω' K inc (spMap j ≫ x) (SecAt.pull G L θ j) pt' c' hT
  obtain ⟨pt₃, -, h₃⟩ := thList_comp m j inc ι₀ hincj x θ pt'' _ h''
  obtain ⟨φ', hφ'⟩ := GlobalTheory.UMin.GalConj.thList_conj S G L ρ hL hρ g m N Ω K x θ pt₃ _ hm hmK hPK h₃
  let τ' : K ≃ₐ[Ω] K := τ.liftNormal K
  refine ⟨φ' τ', fun b => ?_⟩
  apply inc.injective
  exact (AlgEquiv.liftNormal_commutes τ K (c' b)).symm.trans (hφ' τ' b).2

end GlobalTheory.UMin.GalTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  first | exact @GlobalTheory.ThetaPowConj.val_powGen_transport | exact GlobalTheory.ThetaPowConj.val_powGen_transport | (intros; apply GlobalTheory.ThetaPowConj.val_powGen_transport <;> assumption)
end

