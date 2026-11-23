module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def lat {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) (ρ : ℂ) :
    Submodule (𝓞 E) D.La where
  carrier := {a | ∀ j, ty j (H.rt : E) ≠ ρ → Pe a j = 0}
  add_mem' {a b} ha hb j hj := by simp [ha j hj, hb j hj]
  zero_mem' j _ := by simp
  smul_mem' s a ha j hj := by rw [hP.1, ha j hj, mul_zero]

def IsThetaUnif {P : Out.PolAV (Sp ℂ)} (u : HolUnif P.A P.L P.g) : Prop :=
  ∃ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ),
    u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧
      ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
    (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef

def IsQuadLattice {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (d : ℕ) (c : ℂ) : Prop :=
  ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z = fun _ => c * ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt d) / 2))

def IsHomFamily {D : Datum H} {R : Type} [CommRing R] (t : SAB H (Sp R)) (B : Over (Sp R)) [GrpObj B]
    (M : LB B.left) (v : epsR R ⟶ B) (L : Submodule (𝓞 E) D.La) (ρ : R) (S : Set L) (φ : L → (B ⟶ t.G)) : Prop :=
  (∀ a, IsMonHom (φ a)) ∧ (∀ a b, φ (a + b) = φ a * φ b) ∧
    (∀ (s : 𝓞 E) a, φ (s • a) = φ a ≫ t.act.act s) ∧
    (∀ a, IsLieComb ![ρ] ![v ≫ φ a] (v ≫ φ a ≫ t.act.act H.rt)) ∧
    ∀ a ∈ S, ∃ N : ℕ, 1 ≤ N ∧
      LBIso (lbPow (t.PP.L.pull (φ a).left) N) (lbPow M (N * (D.EF (H.w0 • (a : D.La)) a).natAbs))

def IsSpread {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) {Pe : (FU.Di i).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (FU.Di i) ty Pe) {k : IntermediateField ℚ ℂ} (hk : KA l ≤ k)
    (P₀ : Out.PolAV (Sp k)) (v₀ : epsR k ⟶ P₀.A)
    {PC : Out.PolAV (Sp ℂ)} (ψ : PC.A.left ⟶ P₀.A.left) (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ)
    (S : ∀ ε : ℤˣ, Set (lat hP (((ε : ℤ) : ℂ) * H.rt0)))
    (R : Type) [CommRing R] [Algebra k R] (j : R →ₐ[k] ℂ) : Prop :=
  ∃ (y : Sp R ⟶ Xo.X) (t : SAB H (Sp R)) (m : SABMap t Xo.univ.t y)
    (vR : epsR R ⟶ (Over.pullback (spMap (algebraMap k R))).obj P₀.A)
    (φ : ∀ ε : ℤˣ, lat hP (((ε : ℤ) : ℂ) * H.rt0) → ((Over.pullback (spMap (algebraMap k R))).obj P₀.A ⟶ t.G)),
    y ≫ Xo.s = spMap ((algebraMap k R).comp (IntermediateField.inclusion hk).toRingHom) ∧
    spMap j.toRingHom ≫ y = FU.u i Pe ∧
    IsTangent vR ∧
    vR.left ≫ pullback.fst P₀.A.hom (spMap (algebraMap k R)) = spMap (Chart.dualMapR (algebraMap k R)) ≫ v₀.left ∧
    ∀ ε : ℤˣ,
      IsHomFamily t ((Over.pullback (spMap (algebraMap k R))).obj P₀.A)
        (P₀.L.pull (pullback.fst P₀.A.hom (spMap (algebraMap k R)))) vR (lat hP (((ε : ℤ) : ℂ) * H.rt0))
        (((ε : ℤ) : R) * algebraMap k R (IntermediateField.inclusion hk (baseKA l).ρ)) (S ε) (φ ε) ∧
      ∀ (a : lat hP (((ε : ℤ) : ℂ) * H.rt0)) (z : ℂ) (x : Sp ℂ ⟶ pullback P₀.A.hom (spMap (algebraMap k R))),
        x ≫ pullback.fst _ _ = (u₀.ex fun _ => c * z).left ≫ ψ → x ≫ pullback.snd _ _ = spMap j.toRingHom →
        x ≫ (φ ε a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left

end PureType


open PureType in
def CMPoint : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe)
    (k : IntermediateField ℚ ℂ) (hk : KA l ≤ k), FiniteDimensional ℚ k →
    ∀ (P₀ : Out.PolAV (Sp k)) (v₀ : epsR k ⟶ P₀.A), P₀.g = 1 → IsTangent v₀ →
    ∀ (PC : Out.PolAV (Sp ℂ)) (ψ : PC.A.left ⟶ P₀.A.left) (u₀ : HolUnif PC.A PC.L PC.g) (c : ℂ),
      PC.g = 1 → IsGrpPullback PC.A P₀.A (spMap (algebraMap k ℂ)) ψ → LBIso PC.L (P₀.L.pull ψ) →
      IsThetaUnif u₀ → c ≠ 0 → IsQuadLattice u₀.Λ H.d c →
    ∀ (S : ∀ ε : ℤˣ, Set (lat hP (((ε : ℤ) : ℂ) * H.rt0))), (∀ ε, (S ε).Finite) →
    ∀ R₀ : Subalgebra k ℂ, R₀.FG →
    ∃ R : Subalgebra k ℂ, R.FG ∧ R₀ ≤ R ∧ IsSpread FU i hP hk P₀ v₀ ψ u₀ c S R R.val

namespace PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Linear

variable {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)

theorem period_rt_smul {ρ : ℂ} {a : D.La} (ha : a ∈ lat hP ρ) : Pe (H.rt • a) = ρ • Pe a := by
  funext j
  rw [hP.1, Pi.smul_apply, smul_eq_mul]
  by_cases h : ty j (H.rt : E) = ρ
  · rw [h]
  · rw [ha j h, mul_zero, mul_zero]

theorem period_w0_smul {ρ : ℂ} {a : D.La} (ha : a ∈ lat hP ρ) : Pe (H.w0 • a) = ((1 + ρ) / 2) • Pe a := by
  have h : (2 : ℂ) • Pe (H.w0 • a) = (1 + ρ) • Pe a := by
    have e : H.w0 • a + H.w0 • a = a + H.rt • a := by
      rw [← two_smul (𝓞 E), ← mul_smul, H.two_weight_eq_one_add_root, add_smul, one_smul]
    rw [two_smul, ← map_add (f := _), e, map_add (f := _), period_rt_smul hP ha, add_smul, one_smul]
  rw [div_eq_inv_mul, mul_smul, ← h, smul_smul]
  norm_num

theorem disjoint_lat {ρ ρ' : ℂ} (h : ρ ≠ ρ') : Disjoint (lat hP ρ) (lat hP ρ') := by
  rw [Submodule.disjoint_def]
  intro a ha ha'
  apply hP.2.1
  rw [map_zero]
  funext j
  by_cases hj : ty j (H.rt : E) = ρ
  · exact ha' j (hj ▸ h)
  · exact ha j hj


include hP in
theorem eq_zero_of_line {a : D.La} (h : ∀ z : ℂ, z • Pe a ∈ Pe.range) : a = 0 := by
  have := hP.2.2.1
  have hc : Continuous fun z : ℂ => (⟨z • Pe a, h z⟩ : Pe.range) := by fun_prop
  have e := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := 1) (y := 0))
  apply hP.2.1
  simpa using e

end Linear

theorem exists_tangent_over {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} {G' : Over (Sp R')}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {v : epsR R ⟶ G}
    (hv : IsTangent v) : ∃ v' : epsR R' ⟶ G', IsTangent v' ∧ v'.left ≫ φ = spMap (Chart.dualMapR f) ≫ v.left := by
  have w : (spMap (Chart.dualMapR f) ≫ v.left) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
    rw [Category.assoc, Over.w v]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have he : η[G'].left ≫ φ = spMap f ≫ η[G].left := by
    have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over (Sp R')))))
    have e₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp
  refine ⟨Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ w), ?_, h.1.lift_fst _ _ w⟩
  apply h.1.hom_ext
  · show (_ ≫ h.1.lift _ _ w) ≫ φ = _
    rw [Category.assoc, h.1.lift_fst, he, ← hv, ← Category.assoc, ← Category.assoc]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · show (_ ≫ h.1.lift _ _ w) ≫ G'.hom = _
    rw [Category.assoc, h.1.lift_snd, Over.w η[G']]
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1

theorem exists_isThetaUnif (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) :
    ∃ u : HolUnif P.A P.L P.g, IsThetaUnif u := by
  obtain ⟨rig, hr⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, h₁, -, h₂, h₃, -, h₄, h₅, h₆, -⟩ := hT P rig hr
  exact ⟨u, Hm, χ, Ef, h₁, h₂, h₃, h₄, h₅, h₆⟩

theorem exists_baseChange (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ ∧
      LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, hg, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem finiteDimensional_base (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

end PureType

end GlobalTheory
