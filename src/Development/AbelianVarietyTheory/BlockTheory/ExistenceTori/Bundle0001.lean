module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

variable {R : Type} [CommRing R] [IsDomain R]

def genVal {M : LB (TK R).left} (t : LB.Gen M) (j : M.ι) (h : ⊤ ≤ M.U j) : (FractionRing R)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom (res h (t.s j))

def IsIntChart (D : DegPre R) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (i : D.P.L.ι) :
    Prop :=
  ⊤ ≤ x.left ⁻¹ᵁ D.P.L.U i

def IsPsiCoord (D : DegPre R) (χ : D.X) (x : (FractionRing R)ˣ) : Prop :=
  ∃ (j : PUnit → D.P.L.ι) (h : ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ)
      (fun _ => -1)).U j), IsIntChart D (D.c χ) (j PUnit.unit) ∧ x = genVal (D.psi χ) j h

def IsTauCoord (D : DegPre R) (a b : D.X) (x : (FractionRing R)ˣ) : Prop :=
  ∃ (j : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → D.P.L.ι) (h : ⊤ ≤ _),
    IsIntChart D (D.c (a + b)) (j (.inl (.inl (.inl PUnit.unit)))) ∧
    IsIntChart D (D.c a) (j (.inl (.inl (.inr PUnit.unit)))) ∧
    IsIntChart D (D.c b) (j (.inl (.inr PUnit.unit))) ∧
    IsIntChart D η[D.P.A] (j (.inr PUnit.unit)) ∧ x = genVal (D.tau a b) j h

lemma xK_eq (D : DegPre R) (χ : D.X) : D.xK χ = jK R ≫ (D.c χ).left := rfl

theorem exists_isPsiCoord [IsLocalRing R] (D : DegPre R) (χ : D.X) : ∃ x, IsPsiCoord D χ x := by
  have hc : (D.c χ).left (closedPoint R) ∈ ⨆ i, D.P.L.U i := by
    rw [D.P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
  have ht : IsIntChart D (D.c χ) i :=
    ((closedPoint_mem_iff (R := R) ((D.c χ).left ⁻¹ᵁ D.P.L.U i)).1 hi).ge
  refine ⟨_, fun _ => i, ?_, ht, rfl⟩
  intro y _
  exact Set.mem_iInter.2 fun _ => ht (Set.mem_univ (jK R y))

lemma res_res {X : Scheme.{0}} {U V W : X.Opens} (h : U ≤ V) (h' : V ≤ W) (s : Γ(X, W)ˣ) :
    res h (res h' s) = res (h.trans h') s := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

lemma pull_val {X : Scheme.{0}} {S T : CommRingCat.{0}} (φ : S ⟶ T) (c : Spec S ⟶ X)
    (U : X.Opens) (g : Γ(X, U)ˣ) (h : ⊤ ≤ c ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map φ ≫ c) ⁻¹ᵁ U) :
    Units.map (Scheme.ΓSpecIso T).hom.hom.toMonoidHom (res h' (pullU (Spec.map φ ≫ c) U g)) =
      Units.map φ.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso S).hom.hom.toMonoidHom (res h (pullU c U g))) := by
  ext
  change ((Spec.map φ ≫ c).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso T).hom).hom g.val =
    (c.appLE U ⊤ h ≫ (Scheme.ΓSpecIso S).hom ≫ φ).hom g.val
  rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  rfl

theorem IsPsiCoord.unique {D : DegPre R} {χ : D.X} {x x' : (FractionRing R)ˣ}
    (hx : IsPsiCoord D χ x) (hx' : IsPsiCoord D χ x') :
    ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * x' := by
  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨j', h', hj', rfl⟩ := hx'
  have key := congrArg (res (le_inf h h')) (D.psi_gen χ j j')
  rw [map_mul, res_res, res_res] at key
  have hjj : ⊤ ≤ (D.c χ).left ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) :=
    le_inf hj hj'
  have hK : ⊤ ≤ (jK R ≫ (D.c χ).left) ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) :=
    fun y _ => hjj (Set.mem_univ (jK R y))
  refine ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom
    (res hjj (pullU (D.c χ).left _ (D.P.L.g _ _))))⁻¹, ?_⟩
  have hg : res (le_inf h h') ((LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ))
      (fun _ => -1)).g j j') = (res hK (pullU (jK R ≫ (D.c χ).left) _ (D.P.L.g _ _)))⁻¹ := by
    simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_neg, zpow_one]
    refine (MonoidHom.map_inv _ _).trans (congrArg Inv.inv ?_)
    exact res_res _ _ _
  unfold genVal
  rw [key, map_mul, hg]
  congr 1
  refine (MonoidHom.map_inv _ _).trans (Eq.trans (congrArg Inv.inv ?_) (MonoidHom.map_inv _ _).symm)
  exact pull_val (CommRingCat.ofHom (algebraMap R (FractionRing R))) (D.c χ).left _ _ hjj hK

def psiCoord [IsLocalRing R] (D : DegPre R) (χ : D.X) : (FractionRing R)ˣ :=
  (exists_isPsiCoord D χ).choose

theorem psiCoord_spec [IsLocalRing R] (D : DegPre R) (χ : D.X) : IsPsiCoord D χ (psiCoord D χ) :=
  (exists_isPsiCoord D χ).choose_spec

structure LatticeVal (R : Type) [CommRing R] [IsDomain R] (Γ : Type) [AddCommGroup Γ] where
  toFun : (FractionRing R)ˣ → Γ
  map_mul : ∀ x y, toFun (x * y) = toFun x + toFun y
  map_unit : ∀ u : Rˣ, toFun (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 0

section General

variable [IsLocalRing R] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal R Γ)

end General

section DVR

variable (R) [IsDiscreteValuationRing R]

lemma valuation_ne_zero (x : (FractionRing R)ˣ) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) x.val ≠ 0 :=
  (Valuation.ne_zero_iff _).2 x.ne_zero

def ord_vw : LatticeVal R ℤ where
  toFun x := - WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R) x.val)
  map_mul x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (valuation_ne_zero R x) (valuation_ne_zero R y),
      neg_add]
  map_unit u := by
    have : (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
        (algebraMap R (FractionRing R) u) = 1 := by
      erw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (mem_maximalIdeal _).1 h u.isUnit
    change - WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
        (algebraMap R (FractionRing R) u)) = 0
    rw [this]; simp

end DVR

def toUnitK (r : R) (hr : r ≠ 0) : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R (FractionRing R) r)
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)

structure IsOverPrime (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ) : Prop where
  prime : p.Prime
  ne_zero : (p : R) ≠ 0
  mem : (p : R) ∈ maximalIdeal R

section DVR

variable [IsDiscreteValuationRing R]

theorem ord_vw_uniformiser {ϖ : R} (h0 : ϖ ≠ 0) (h : maximalIdeal R = Ideal.span {ϖ}) :
    (ord_vw R).toFun (toUnitK ϖ h0) = 1 := by
  change - WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
        (algebraMap R (FractionRing R) ϖ)) = 1
  erw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ h0 h]
  simp

def ramIdx {p : ℕ} (hp : IsOverPrime R p) : ℤ := (ord_vw R).toFun (toUnitK (p : R) hp.ne_zero)

end DVR

section Normed

variable [IsLocalRing R] {F : Type} [NormedField F]

variable {φ : FractionRing R →+* F}


end Normed

theorem isOverPrime_padicInt (p : ℕ) [hp : Fact p.Prime] : IsOverPrime ℤ_[p] p := by
  refine ⟨hp.out, Nat.cast_ne_zero.2 hp.out.ne_zero, ?_⟩
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.mem_span_singleton_self _

end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetChartLaws
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

abbrev algO (x : Sp S ⟶ X₀) (B : Type) [CommRing B] [Algebra S B] : Over X₀ :=
  Over.mk (spMap (algebraMap S B) ≫ x)

def algMap (x : Sp S ⟶ X₀) {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B']
    (f : B →ₐ[S] B') : algO x B' ⟶ algO x B :=
  Over.homMk (spMap (f : B →+* B')) (by
    change spMap (f : B →+* B') ≫ spMap (algebraMap S B) ≫ x = spMap (algebraMap S B') ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

def jetVec {σ : Type} (c : σ → S) : Jet S σ 1 →ₐ[S] DualNumber S :=
  liftJet (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S))
          (MvPolynomial.X i : MvPolynomial σ S)) ≤ Ideal.span {(DualNumber.eps : DualNumber S)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [MvPolynomial.aeval_X, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine (Ideal.pow_right_mono h1 _).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

abbrev JetPts (G : Over X₀) (x : Sp S ⟶ X₀) (d : ℕ) : Type :=
  ∀ m : ℕ, algO x (Jet S (Fin d) m) ⟶ G

section Group

variable (G : Over X₀) [GrpObj G] (x : Sp S ⟶ X₀) {d : ℕ}

def IsFormalParam (j : JetPts G x d) : Prop :=
  (∀ m, algMap x (jetTrunc : Jet S (Fin d) (m + 1) →ₐ[S] Jet S (Fin d) m) ≫ j (m + 1) = j m) ∧
  (∀ m, algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1) ∧
  ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (I : Ideal B), I ^ (m + 1) = ⊥ →
    ∀ g : algO x B ⟶ G, algMap x (Ideal.Quotient.mkₐ S I) ≫ g = 1 →
      ∃! f : Jet S (Fin d) m →ₐ[S] B, algMap x f ≫ j m = g



omit [GrpObj G] in
def TanIs (j : JetPts G x d) (v : Sp (DualNumber S) ⟶ G.left) (c : Fin d → S) : Prop :=
  v = (algMap x (jetVec c) ≫ j 1).left

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem jetVec_X {σ : Type} (c : σ → S) (i : σ) :
    jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) = c i • (DualNumber.eps : DualNumber S) := by
  have h : jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      MvPolynomial.aeval (R := S) (fun i => c i • (DualNumber.eps : DualNumber S)) (MvPolynomial.X i) := rfl
  rw [h, MvPolynomial.aeval_X]

end GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
end
end

