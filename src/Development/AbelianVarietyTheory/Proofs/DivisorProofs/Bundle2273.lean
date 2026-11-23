module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelRootsFiniteExtCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FieldLevel

open GlobalTheory.TorsionGenerators

theorem pairing_prod {H U : Type} [CommGroup H] [CommGroup U] (e : H →* H →* U) (z : U) {g : ℕ}
    (x : Fin g ⊕ Fin g → H) (h₁ : ∀ i j, e (x (.inl i)) (x (.inl j)) = 1)
    (h₂ : ∀ i j, e (x (.inr i)) (x (.inr j)) = 1)
    (h₃ : ∀ i j, e (x (.inl i)) (x (.inr j)) = if i = j then z else 1)
    (h₄ : ∀ i j, e (x (.inr i)) (x (.inl j)) = if i = j then z⁻¹ else 1) (a b : Fin g ⊕ Fin g → ℤ) :
    e (∏ i, x i ^ a i) (∏ i, x i ^ b i) = z ^ omegaStd a b := by
  have hz : z ^ omegaStd a b = ∏ i, z ^ (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i)) :=
    (map_prod (zpowersHom U z) (fun i => Multiplicative.ofAdd
      (a (.inl i) * b (.inr i) - a (.inr i) * b (.inl i))) Finset.univ)
  have hi : ∀ (p : Prop) [Decidable p] (u : U) (m : ℤ), (if p then u else 1) ^ m = if p then u ^ m else 1 :=
    fun p _ u m => by split_ifs <;> simp
  have hp : ∀ (f : Fin g → H →* U) (t : H), (∏ i, f i) t = ∏ i, f i t :=
    fun f t => map_prod (MonoidHom.eval t) f Finset.univ
  rw [hz]
  simp only [map_prod, map_zpow, hp, MonoidHom.zpow_apply, Fintype.prod_sum_type,
    map_mul, MonoidHom.mul_apply, h₁, h₂, h₃, h₄, one_zpow, Finset.prod_const_one, _root_.one_mul, _root_.mul_one,
    hi, Finset.prod_ite_eq, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← zpow_mul, inv_zpow', ← zpow_add, zpow_sub, ← zpow_neg]
  congr 1
  ring

theorem stdSymp_mk {g p q : ℕ} (hp : p < 2 * g) (hq : q < 2 * g) : stdSymp g ⟨p, hp⟩ ⟨q, hq⟩ =
    if p < g ∧ q = p + g then 1 else if q < g ∧ p = q + g then -1 else 0 := rfl

theorem exists_points (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) [IsCommMonObj P.A] {g : ℕ}
    (hg : g = P.g) (M : ℕ) (hM : (M : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (hz : IsPrimitiveRoot ze M) :
    ∃ x : Fin g ⊕ Fin g → (baseOver (Sp K) ⟶ P.A), (∀ i, x i ^ M = 1) ∧
      ∀ a b : Fin g ⊕ Fin g → ℤ, Out.WeilIs P.A P.L M (∏ i, x i ^ a i) (∏ i, x i ^ b i) (ze ^ omegaStd a b) := by
  obtain ⟨x, hx, hw⟩ := ConstThetaLevel.exists_symplectic_points hL K P hg M hM ze hz
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P M (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom M).ker
  have hH : ∀ x : H, x.1 ^ M = 1 := fun x => x.2
  choose c hc hu using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hu _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hu _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  let κ : Fin g ⊕ Fin g → Fin (2 * g) := Sum.elim (fun i => ⟨i, by omega⟩) (fun i => ⟨i + g, by omega⟩)
  let y : Fin g ⊕ Fin g → H := fun i => ⟨x (κ i), hx _⟩
  have he : ∀ i j, e (y i) (y j) = ze ^ stdSymp g (κ i) (κ j) := fun i j => (hu (y i) (y j) _ (hw _ _)).symm
  refine ⟨fun i => (y i).1, fun i => hH _, fun a b => ?_⟩
  have E := pairing_prod e ze y (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) (fun i j => ?_) a b
  · have h := hc (∏ i, y i ^ a i) (∏ i, y i ^ b i)
    rw [show c (∏ i, y i ^ a i) (∏ i, y i ^ b i) = _ from E] at h
    change Out.WeilIs P.A P.L M (H.subtype (∏ i, y i ^ a i))
      (H.subtype (∏ i, y i ^ b i)) (ze ^ omegaStd a b) at h
    simpa only [map_prod, map_zpow, Subgroup.subtype_apply] using h
  all_goals
    have hi := i.2
    have hj := j.2
    rw [he]
    simp only [κ, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff]
    rw [stdSymp_mk]
    split_ifs <;> first | omega | (simp; done)

theorem exists_level_and_roots : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (K : Type) [Field K] [CharZero K] (j : R →+* K) (n : ℕ), 0 < n → ∀ (ζ : Kˣ), IsPrimitiveRoot ζ n → ∀ (r : ℕ) (c : Fin r → (𝟙_ (Over (Sp R)) ⟶ P.A)), ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (lev : (Fin P.g ⊕ Fin P.g → ℤ) → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)) (d : Fin r → (Over.mk (spMap ((algebraMap K L).comp j)) ⟶ P.A)), (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ n = 1) ∧ (∀ x y, Out.WeilIs P.A P.L n (lev x) (lev y) (unitOn (Units.map (algebraMap K L).toMonoidHom ζ ^ omegaStd x y))) ∧ ∀ i, d i ^ n = toUnit _ ≫ c i := by
  intro R _ P K _ _ j n hn ζ hζ r c
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have := P.isAb.smooth
  let Q := AlgebraicClosure K
  let t : R →+* Q := (algebraMap K Q).comp j
  have hnQ : (n : Q) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hz : IsPrimitiveRoot (Units.map (algebraMap K Q).toMonoidHom ζ) n :=
    hζ.map_of_injective (unitsMap_injective _)
  obtain ⟨P', φ', β, h, -, H⟩ := exists_fibre hL P t
  have := P'.isAb.comm
  obtain ⟨x, hx, hw⟩ := exists_points hL Q P' h.1.symm n hnQ _ (ZH.RealDimOne.isPrimitiveRoot_unitOn hz)
  have hroot : ∀ p : Over.mk (spMap t) ⟶ P.A, ∃ q, q ^ n = p := fun p => by
    obtain ⟨p, rfl⟩ := β.surjective p
    obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div hL.mulN P' p n hn
    exact ⟨β q, (map_pow β _ _).symm.trans (congrArg β hq)⟩
  choose d hd using fun i => hroot (toUnit _ ≫ c i)
  let z : (Fin P.g ⊕ Fin P.g) ⊕ Fin r → (Over.mk (spMap t) ⟶ P.A) := Sum.elim (fun i => β (x i)) d
  choose s hs hb using fun i => exists_finite_coordinates P.A.hom t (z i).left (Over.w _)
  let s' : Set Q := ⋃ i, s i
  have : Finite s' := (Set.finite_iUnion hs).to_subtype
  let L := IntermediateField.adjoin K s'
  have : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin fun y _ =>
    (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let io : L →+* Q := algebraMap L Q
  let j' : R →+* L := (algebraMap K L).comp j
  have hj : io.comp j' = t := rfl
  choose b hb' using fun i => hb i L io io.injective (fun c => ⟨j' c, rfl⟩) (fun y hy =>
    ⟨⟨y, IntermediateField.subset_adjoin K s' (Set.mem_iUnion.2 ⟨i, hy⟩)⟩, rfl⟩)
  have hbw : ∀ i, b i ≫ P.A.hom = spMap j' := fun i => by
    have := TorsionSeparable.epi_specMap io
    rw [← cancel_epi (spMap io), ← Category.assoc, hb', spMap_comp_spMap]
    exact Over.w (z i)
  let y : _ → (Over.mk (spMap j') ⟶ P.A) := fun i => Over.homMk (b i) (hbw i)
  have hy : ∀ i, extPt hj ≫ y i = z i := fun i => Over.OverMorphism.ext (hb' i)
  let F : (Over.mk (spMap j') ⟶ P.A) →* (Over.mk (spMap t) ⟶ P.A) :=
    MonoidHom.mk' (fun p => extPt hj ≫ p) fun p q => comp_mul _ _ _
  have hF : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, extPt hj ≫ (∏ i, y (.inl i) ^ a i) = β (∏ i, x i ^ a i) := fun a => by
    show F _ = _
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_zpow]
    exact congrArg (· ^ a i) (hy (.inl i))
  have hyM : ∀ i, y (.inl i) ^ n = 1 := fun i => by
    rw [← extPt_eq_one_iff hj, comp_pow, hy]
    exact (map_pow β _ _).symm.trans ((congrArg β (hx i)).trans (map_one β))
  have hT : ∀ a : Fin P.g ⊕ Fin P.g → ℤ, (∏ i, y (.inl i) ^ a i) ^ n = 1 := fun a => by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, _root_.mul_comm, zpow_mul, zpow_natCast, hyM, one_zpow]
  refine ⟨L, inferInstance, inferInstance, this, fun a => ∏ i, y (.inl i) ^ a i, fun i => y (.inr i),
    fun a a' => ?_, hT, fun a a' => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · obtain ⟨u, hu⟩ := exists_weilIs hL P j' (hT a) (hT a')
    have H₁ := weilIs_extPt hL P hj hu
    rw [hF, hF] at H₁
    have e := CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB H₁ (H _ _ _ _ (hw a a'))
    have hζ' : Units.map (algebraMap K Q).toMonoidHom ζ =
      Units.map io.toMonoidHom (Units.map (algebraMap K L).toMonoidHom ζ) := Units.ext rfl
    rw [← ZH.RealDimOne.unitOn_zpow, hζ', ← map_zpow] at e
    rwa [← unitsMap_injective io (unitOn_injective e)]
  · apply extPt_injective hj
    rw [comp_pow, hy, ← Category.assoc, comp_toUnit]
    exact hd i

end GlobalTheory.FieldLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrime
section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaRealAt

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def locAt (R : Subalgebra o Ω) (𝔭 : Ideal R) [𝔭.IsPrime] : Subalgebra o Ω where
  carrier := {z | ∃ a b : R, b ∉ 𝔭 ∧ z = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a₁, b₁, h₁, rfl⟩ ⟨a₂, b₂, h₂, rfl⟩
    exact ⟨a₁ * a₂, b₁ * b₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim h₁ h₂, by
      rw [div_mul_div_comm]; rfl⟩
  add_mem' := by
    rintro _ _ ⟨a₁, b₁, h₁, rfl⟩ ⟨a₂, b₂, h₂, rfl⟩
    have n₁ : (b₁ : Ω) ≠ 0 := fun e => h₁ (by rw [show b₁ = 0 from Subtype.ext e]; exact 𝔭.zero_mem)
    have n₂ : (b₂ : Ω) ≠ 0 := fun e => h₂ (by rw [show b₂ = 0 from Subtype.ext e]; exact 𝔭.zero_mem)
    exact ⟨a₁ * b₂ + b₁ * a₂, b₁ * b₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim h₁ h₂, by
      rw [div_add_div _ _ n₁ n₂]; rfl⟩
  algebraMap_mem' r := ⟨algebraMap o R r, 1, fun h => (‹𝔭.IsPrime›.ne_top) ((Ideal.eq_top_iff_one _).2 h), by
    rw [OneMemClass.coe_one, div_one]; rfl⟩

theorem exists_fg_at (R : Subalgebra o Ω) (hR : R.FG) (𝔭 : Ideal R) [h𝔭 : 𝔭.IsPrime] (V : (Sp R).Opens)
    (hx : (show Sp R from (⟨𝔭, h𝔭⟩ : PrimeSpectrum R)) ∈ V) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧ (∀ z ∈ R', ∃ a b : R, b ∉ 𝔭 ∧ z = (a : Ω) / (b : Ω)) ∧
      ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := (⟨𝔭, h𝔭⟩ : PrimeSpectrum R)) (u := (V : Set (Sp R))) hx V.isOpen
  have hf𝔭 : f ∉ 𝔭 := hxf
  have hf0 : (f : Ω) ≠ 0 := by
    intro h0
    have : f = 0 := Subtype.ext h0
    exact hf𝔭 (this ▸ 𝔭.zero_mem)
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)
  have h : R ≤ R' := le_sup_left
  have hinv : (f : Ω)⁻¹ ∈ R' :=
    (le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))
  have hloc : R' ≤ locAt R 𝔭 := by
    refine sup_le (fun z hz => ⟨⟨z, hz⟩, 1, fun h1 => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 h1), by
      rw [OneMemClass.coe_one, div_one]⟩) (Algebra.adjoin_le ?_)
    intro z hz
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨1, f, hf𝔭, by rw [OneMemClass.coe_one, one_div]⟩
  refine ⟨R', h, hR.sup (Subalgebra.fg_adjoin_finset _), fun z hz => hloc hz, ?_⟩
  have hu : IsUnit ((Subalgebra.inclusion h).toRingHom f) :=
    IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0))
  refine ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  apply hfV
  intro hm
  exact y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)

theorem exists_real_of_univBasis_eq (hL : Laws) [ArithBase o Ω] (R : Subalgebra o Ω) (fg : R.FG)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ) (hp : n.Prime)
    (ho : Odd n) (hk : 2 ≤ k) (hj : 1 ≤ j) (hu : IsUnit (n : o)) (hS : HypS P.A P.L)
    (lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)))
    (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))) (hth : UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th))
    (b : Fin (((n ^ k) ^ 2) ^ P.g) → SecM P.A P.L ((n ^ k) ^ 2 : ℕ) (baseOver (Sp R)))
    (hb : UnivBasis P ((n ^ k) ^ 2 : ℕ) b) {R₀ : Subalgebra o Ω} (h : R₀ ≤ R) (P₀ : PolAV (Sp R₀))
    (φ : P.A.left ⟶ P₀.A.left) (hg : P.g = P₀.g)
    (hφ : IsGrpPullback P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ) (hiso : LBIso P.L (P₀.L.pull φ))
    (x₀ : Fin (2 * P₀.g) → (baseOver (Sp R₀) ⟶ P₀.A))
    (hx₀ : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)), (i : ℕ) = i' →
      (lev.pt i').left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i).left) :
    ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R₀ ≤ S.R) (φ : ρ.P.A.left ⟶ P₀.A.left), S.R = R ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧
      S.r = n ^ j ∧ S.g = P₀.g ∧ IsGrpPullback ρ.P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧
      LBIso ρ.P.L (P₀.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P₀.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P₀.g →
      (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₁ ^ (S.r * S.N)).left ∧
      (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₂ ^ (S.r * S.N)).left := by
  haveI := isNoetherian_of_fg fg
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  have hn2 : 2 ≤ n := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn1
  have hr1 : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn1
  have hN2 : 2 ≤ (n ^ k) ^ 2 := by
    have : n ^ 1 ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    nlinarith
  have hM : n ^ j * (n ^ k) ^ 2 = n ^ (j + 2 * k) := by ring
  have hM1 : 1 ≤ n ^ j * (n ^ k) ^ 2 := hM ▸ Nat.one_le_pow _ _ hn1
  have hMo : Odd (n ^ j * (n ^ k) ^ 2) := hM ▸ ho.pow
  let f : o →+* Γ((baseOver (Sp R)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R)
  have hf : Function.Injective f := fn_injective.comp (algebraMap_injective R)
  haveI : Nontrivial Γ((baseOver (Sp R)).left, ⊤) := (fn_injective (R := R)).nontrivial
  have un : ∀ q e : ℕ, q = n ^ e → IsUnit (q : Γ(Sp R, ⊤)) := fun q e hq => by
    have := (hu.pow e).map f
    rw [map_pow, map_natCast] at this
    rw [hq, Nat.cast_pow]
    exact this
  have prim : IsPrimitiveRoot (ze : o) ((n ^ j * (n ^ k) ^ 2) ^ 2) := (prim_iff R ze _).1 lev.prim
  obtain ⟨pt, hadd, hbij, hweil, hdiv, hnorm⟩ := _root_.GlobalTheory.exists_torsionPoints_of_squareLevel hL _ P _ _ hM1 (un _ _ hM) lev
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  obtain ⟨rig, hrig⟩ := P.rigid
  have hfr : ∀ a, ∃ τ, IsTorsFrame P rig (n ^ j * (n ^ k) ^ 2) (pt a) τ := fun a => by
    obtain ⟨y, hy, e⟩ := hdiv a
    obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.exists_symLift_global hL _ P _ hMo.pow (un _ ((j + 2 * k) * 2) (by rw [hM, pow_mul])) _ y hy
    exact GlobalTheory.T.exists_isTorsFrame_of_symLift' hL _ P rig hrig _ hMo _ y _ hy e θ hθ
  choose fr hfr using hfr
  have tors : ∀ a, pt (n ^ j • a) ^ ((n ^ k) ^ 2) = 1 := fun a => by
    rw [← hsm, smul_smul, mul_comm ((n ^ k) ^ 2) (n ^ j), nsmul_self, h0]
  choose U hU using fun a => _root_.GlobalTheory.exists_symLift_global hL _ P _ ho.pow.pow (un _ (k * 2) (pow_mul _ _ _).symm) _ _ (tors a)
  obtain ⟨α, hα, hαn⟩ := GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P rig hrig (n ^ k) _ rfl (baseOver (Sp R))
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A (baseOver (Sp R)) (n ^ k)) (hm := lift_snd _ _)
    (b := 1) P.isLB hα th
  obtain ⟨u, u₁, u₂, u₃, u₄, u₅⟩ := exists_operators hL P rfl ho.pow (un _ _ hM) _ pt hadd hweil U hU hα hs₀
  have hspan := GlobalTheory.T.span_translates_multiplicationPullback_theta hL _ P (n ^ k) _ rfl hm1 (un _ _ rfl) th hth _ b hb α hα s₀ hs₀ _ U
    (fun a => SecM.toSec P.A (u a (SecM.ofSec P.A s₀))) (fun K _ _ x z hz => by
      obtain ⟨a, ha, uniq⟩ := hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])
      obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
      have e : (n ^ k) ^ 2 • a = 0 := (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans
        (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm
      obtain ⟨c, rfl⟩ := exists_nsmul_eq hM1 a e
      exact ⟨c, by rw [(hU c).pt_eq, ha]⟩) (fun a => (u₁ _ _ _).2 rfl)
  obtain ⟨bb, -⟩ := hb.exists_basis
  obtain ⟨J, _, ρ, s, i₀, hcard, hi₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅⟩ := _root_.GlobalTheory.ThetaReal.exists_monomial_matrices o _ _ f hf P.g (n ^ k) (n ^ j) _ rfl hm1 hr1
    ze _ (Nat.one_le_pow _ _ hM1) prim.pow_eq_one bb u (SecM.ofSec P.A s₀) u₂
    (fun a b => (u₃ a b).imp fun e he v => (he v).trans (congrArg (· • _) (map_pow f _ _).symm)) u₄ u₅ hspan
  choose v hv using fun a => ThetaPtExist.exists_isValueAt P.isLB th (pt a) (fr a) (hfr a).2.1
  choose w hw using fun a i => (hL.evVal _ P ((n ^ k) ^ 2) (pt a) (fr a) (hfr a).2.1 (SecM.toSec P.A (s i))).exists
  let ev : Γ((baseOver (Sp R)).left, ⊤) → R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have good : ∀ a, ∃ y, n • y = 0 ∧ a + y ∈ {a | (ev (v a) : Ω) ≠ 0} := fun a => by
    let K := AlgebraicClosure Ω
    let x : Sp K ⟶ Sp R := spMap ((algebraMap Ω K).comp R.val.toRingHom)
    have := ArithBase.char (o := o) (Ω := Ω)
    obtain ⟨y, hy, H⟩ := GlobalTheory.T.exists_good_torsion_translate_geometricPoint hL _ P K x n hn2 (Nat.cast_ne_zero.2 (by omega)) th hth
      ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a)
    obtain ⟨c, hc, -⟩ := hbij K x y (by rw [hM, show j + 2 * k = (j + 2 * k - 1) + 1 by omega, pow_succ', pow_mul, hy,
      one_pow])
    obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
    refine ⟨c, (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
      (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun e => ?_⟩
    refine H (pt (a + c)) (fr _) (v _) (by rw [hadd, MonObj.comp_mul, hc]) (hfr _).2.1 (hv _) ?_
    have e' : ev (v (a + c)) = 0 := Subtype.ext e
    exact (fn_hom _).symm.trans ((congrArg fn e').trans (map_zero _))
  obtain ⟨c₁, hc₁⟩ := hth.exists_basis
  let S : ThetaSys o Ω :=
    { g := P.g, N := (n ^ k) ^ 2, r := n ^ j, N_ge := hN2, r_pos := hr1, ζ := ze, prim := prim
      unit := by rw [hM, Nat.cast_pow]; exact hu.pow _
      J := J, ne := ⟨i₀⟩, ρ := ρ, ρ_one := ρ₁, ρ_mul := ρ₂, ρ_add := ρ₃
      th := fun a => ev (v a), ev := fun a i => ev (w a i), R := R, fg := fg, frac := frac
      th_mem := fun a => (ev (v a)).2, ev_mem := fun a i => (ev (w a i)).2
      supp := _root_.GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets _ n (j + 2 * k) _ hn1 (by omega) hM _ good
      th_ne := by
        obtain ⟨y, -, hy⟩ := good 0
        exact ⟨_, hy⟩ }
  let ρ' : S.Real :=
    { P := P, g_eq := rfl, hypS := hS, n := n, n_prime := hp, n_odd := ho, k := k, two_le := hk, N_eq := rfl
      r_eq := ⟨j, hj, rfl⟩, card := hcard, pt := pt, pt_add := hadd, pt_bij := hbij
      weil := fun a b c hc => by
        have e : unitOn c = unitOn (Units.map (algebraMap o R).toMonoidHom ze) ^
            (n ^ j * (n ^ k) ^ 2 * (eStd P.g _ a b).val) := Units.ext
          ((congrArg fn hc).trans ((map_pow f _ _).trans (Units.val_pow_eq_pow_val (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) _).symm))
        rw [e]
        exact hweil a b
      rig := rig, rig_gen := hrig, th₁ := th
      th₁_basis := fun σ => by
        have := existsUnique_of_basis c₁ σ
        simp only [hc₁] at this
        exact this
      fr := fr, fr_tors := hfr
      th_val := fun a => (fn_hom (v a)).symm ▸ hv a
      s := fun i => SecM.toSec P.A (s i)
      s_basis := existsUnique_of_basis s
      ev_val := fun i a => (congrArg (IsValueAt _ _ _ _ _ _) (fn_hom (w a i))).mpr (hw a i)
      i₀ := i₀, α := α, α_gen := hα, α_norm := hαn
      s_zero := by
        have e : SecM.toSec P.A (s i₀) = s₀ := by rw [hi₀]; rfl
        exact e ▸ hs₀
      U := U, U_sym := hU
      U_act := fun a i σ H => (sum_iff σ s _).2 (((u₁ _ _ _).1 H).symm.trans (ρ₄ a i))
      orbit := ρ₅ }
  refine ⟨S, ρ', h, φ, rfl, rfl, rfl, rfl, hg, hφ, hiso, fun i i₁ i₂ e₁ e₂ => ?_⟩
  obtain ⟨q₁, q₂⟩ := hnorm i ⟨i₁, by have := i₁.2; omega⟩ ⟨i₂, by have := i₂.2; omega⟩ e₁
    (e₂.trans (congrArg (_ + ·) hg.symm))
  have key : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)) (q : ℕ), (i : ℕ) = i' →
      (lev.pt i' ^ q).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i ^ q).left := fun i i' q e =>
    (ThetaPtMove.over_pow hφ (T := baseOver (Sp R)) (T₀ := baseOver (Sp R₀)) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hx₀ i i' e).symm q).symm
  exact ⟨(congrArg (fun z => z.left ≫ φ) q₁).trans (key _ _ _ rfl),
    (congrArg (fun z => z.left ≫ φ) q₂).trans (key _ _ _ rfl)⟩

end GlobalTheory.ThetaRealAt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ThetaRealAt.exists_thetaSys_real_at : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (𝔭 : Ideal R), 𝔭.IsPrime → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), (∀ x ∈ S.R, ∃ a b : R, b ∉ 𝔭 ∧ x = (a : Ω) / (b : Ω)) ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  intro o Ω _ _ _ _ R fg frac 𝔭 h𝔭 P n k j ze hp ho hk hj hu hS lev
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg fg
  let p : Sp R := (⟨𝔭, h𝔭⟩ : PrimeSpectrum R)
  obtain ⟨V₁, m₁, b₁, hb₁⟩ := GlobalTheory.ThetaReal.exists_univBasis hL₂.secBaseChangeAny P 1 le_rfl p
  obtain ⟨V₂, m₂, b₂, hb₂⟩ := GlobalTheory.ThetaReal.exists_univBasis hL₂.secBaseChangeAny P ((n ^ k) ^ 2)
    (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hp.pos)) p
  obtain ⟨R', h, fg', hloc, τ, hτ⟩ := GlobalTheory.ThetaRealAt.exists_fg_at R fg 𝔭 (V₁ ⊓ V₂) ⟨m₁, m₂⟩
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg fg'
  obtain ⟨P', φ, hg, hφ, hiso⟩ := exists_isPolFibre hL.polBaseChange (Subalgebra.inclusion h).toRingHom P
  have hiso' := LBIso.symm hiso
  have w : ∀ (V : (Sp R).Opens) (hV : V₁ ⊓ V₂ ≤ V), (τ ≫ (Sp R).homOfLE hV) ≫ (overRes (T := baseOver (Sp R)) V).hom =
      spMap (Subalgebra.inclusion h).toRingHom := fun V hV => by
    change (τ ≫ (Sp R).homOfLE hV) ≫ V.ι ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.assoc, Scheme.homOfLE_ι, hτ]
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₁ inf_le_left) b₁ hb₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₂ inf_le_right) b₂ hb₂
  obtain ⟨lev', hlev⟩ := _root_.GlobalTheory.exists_level_baseChange hL _ _ _ P P' φ hφ hiso' hg _ _
    (unitOn (Units.map (algebraMap o R').toMonoidHom ze))
    (congrArg (fun q => q.hom (algebraMap o R ze))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))).symm
    ((GlobalTheory.ThetaReal.prim_iff R' ze _).2 ((GlobalTheory.ThetaReal.prim_iff R ze _).1 lev.prim)) lev
  haveI hU : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let e := finCongr (congrArg (((n ^ k) ^ 2) ^ ·) hg)
  obtain ⟨S, ρ, h₀, φ₀, hSR, rest⟩ := GlobalTheory.ThetaRealAt.exists_real_of_univBasis_eq hL R' fg' (fun x => by
      obtain ⟨a, ha, b, hb, e⟩ := frac x
      exact ⟨a, h ha, b, h hb, e⟩) P' n k j ze hp ho hk hj hu
    (SymBaseChange.hypS_baseChange _ _ _ _ _ φ _ _ P.isLB P'.isLB hφ hiso' hS) lev' (SecM.toSec P'.A (c₁ hU.default))
    hc₁.unique (fun i => c₂ (e i)) (fun T _ u => by
      obtain ⟨c, hc⟩ := hc₂ T u
      exact ⟨c.reindex e.symm, fun i => by rw [Module.Basis.reindex_apply, hc, Equiv.symm_symm]⟩) h P φ hg hφ hiso' lev.pt hlev
  exact ⟨S, ρ, h₀, φ₀, fun x hx => hloc x (hSR ▸ hx), rest⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveApp
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU GlobalTheory.UU.PackageDescent

noncomputable section
namespace GlobalTheory.Mum.BijDescent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_descend_val_bij {L : LB X} (π : Y' ⟶ Y)
    (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → val t (r ≫ π) z J = val u r z J := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := fun j => (hπ _).2 _
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := by
    intro j
    obtain ⟨b, hb⟩ := (hπ (LB.wchart L φ j)).2 ((res (le j) (u.s j))⁻¹).val
    refine IsUnit.of_mul_eq_one b ((hπ _).1 ?_)
    rw [map_mul, map_one, ha j, hb]
    exact Units.mul_inv _
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y') (y : Z), π (r y) ∈ LB.wchart L φ j →
      gm (r ≫ π) y (LB.wchart L φ j) (hun j).unit =
      gm r y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j Z r y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    exact (gm_pull r π y _ hy _).symm.trans ((congrArg (gm r y _) e).trans (gm_res r y (le j) hy _))
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    ((hπ (LB.wchart L φ j ⊓ LB.wchart L φ j')).1 ?_), fun Z r z J hJ => ?_⟩
  · refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
    have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
    refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
    refine ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε (𝟙 Y' ≫ π) y j j' hy'.1 hy'.2).trans ?_)
      ((gm_res (𝟙 Y' ≫ π) y _ hy' _).trans (hv j' _ _ y hy'.2)))
    simp only [trF, Category.id_comp]
  · rw [val_of _ (r ≫ π) z J (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))

theorem exists_descend_bij {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)} (hw : PGen w)
    (hM : M.IsLB) (hL : L.IsLB) (π : Y' ⟶ Y) (hπ : ∀ V : Y.Opens, Function.Bijective (π.app V).hom)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} (hc : ∀ k, φ' k ≫ F = π ≫ φ k) {ε : K → ℤ}
    (a : LB.Gen (LB.LinComb L φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J →
        val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up hw hM hL a ha
  obtain ⟨u, hu, vu⟩ := exists_gen hM (φ' := fun k => π ≫ φ k) (ε' := ε)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (hc k)) t₁ ht₁
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I J), Good M z I → Good L z J → val u r z I =
      (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
    intro Z r z I J hI hJ
    rw [vu Z r z I hI, val_of t₁ r z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact v₁ Z r z _ _ (Set.mem_iInter.2 fun k => hI ((r ≫ φ' k) ≫ F)) (hJ.mem φ' r)
  obtain ⟨t, ht, vt⟩ := exists_gen_descend_val_bij π hπ φ ε u hu
  exact ⟨t, ht, fun Z r z I J hI hJ => (vt Z r z I hI).trans (key Z r z I J hI hJ)⟩

end GlobalTheory.Mum.BijDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKTorsionAbelianPartAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kTorsion_abelianPart_algClosed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} := by
  first | exact @GlobalTheory.AbTorsionFiniteF.finite_torsion_TF | exact GlobalTheory.AbTorsionFiniteF.finite_torsion_TF | (intros; apply GlobalTheory.AbTorsionFiniteF.finite_torsion_TF <;> assumption)
end

