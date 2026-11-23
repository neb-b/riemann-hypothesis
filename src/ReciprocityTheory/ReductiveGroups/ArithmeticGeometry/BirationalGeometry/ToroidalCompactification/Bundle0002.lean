module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def eigLat {O : Type} (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)] (χ : O → R) : Submodule R (Fin n → R) :=
  ⨅ a, LinearMap.ker (tmap hx (act a) - χ a • LinearMap.id)

def dualMapR {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp


end ReciprocityTheory.ChartRestriction.G.Chart
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory IsLocalRing NumberField

def ExtVStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (maximalIdeal V) V →
    ∀ (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V))), IsProper tK.G.hom →
    ∀ (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
      (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))),
      ∃ ψ : SABMap t t' (𝟙 (Sp V)), m.φ ≫ ψ.φ = m'.φ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsTor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Semi.TorusPts

open TorusInj

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem charUnit_appTop {Z : Scheme.{0}} (τ : Z ⟶ (splitTorus S X).left) (χ : X) :
    τ.appTop.hom (charUnit S X χ).val =
      (τ ≫ tFst X).appTop.hom ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  rw [charUnit_val, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 2
  first
  | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; simp only [Scheme.Hom.preimage_top])
  | (simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top])
  | (ext1; simp [Scheme.Hom.appLE, Scheme.Hom.appTop])

theorem ringHom_ext_ZU {A : Type} [CommRing A] {f g : AddMonoidAlgebra ZU.{0} X →+* A}
    (h : ∀ χ, f (AddMonoidAlgebra.single χ 1) = g (AddMonoidAlgebra.single χ 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  have e : (AddMonoidAlgebra.single 0 b : AddMonoidAlgebra ZU.{0} X) = ((b.down : ℤ) : AddMonoidAlgebra ZU.{0} X) := by
    rw [AddMonoidAlgebra.intCast_def]
    congr 1
  rw [e, map_intCast, map_intCast]

theorem torusPt_ext {Z : Over S} {τ₁ τ₂ : Z ⟶ splitTorus S X}
    (h : ∀ χ, τ₁.left.appTop.hom (charUnit S X χ).val = τ₂.left.appTop.hom (charUnit S X χ).val) :
    τ₁ = τ₂ := by
  have key : ∀ f g : Z.left ⟶ Spec (torusRing ZU X),
      (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f.appTop = (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ g.appTop →
        f = g := by
    intro f g hfg
    have hh : ∀ f' : Z.left ⟶ Spec (torusRing ZU X), (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ f'.appTop =
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop := by
      intro f'
      have h0 := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop
      have hf : f' = ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))
          ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm f').unop.op :=
        ((ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).apply_symm_apply f').symm
      conv_lhs => rw [hf]
      exact h0
    have hψ := (hh f).symm.trans (hfg.trans (hh g))
    exact (ΓSpec.adjunction.homEquiv Z.left (Opposite.op (torusRing ZU X))).symm.injective
      (congrArg Quiver.Hom.op hψ)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply key
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro χ
    have e1 := charUnit_appTop τ₁.left χ
    have e2 := charUnit_appTop τ₂.left χ
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    erw [← e1, ← e2]
    exact h χ
  · exact (Over.w τ₁).trans (Over.w τ₂).symm

end ReciprocityTheory.ChartRestriction.G.Semi.TorusPts
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Semi

section Lie

variable {R : Type} [CommRing R]

abbrev epsR (R : Type) [CommRing R] : Over (Sp R) := Over.mk (spMap (algebraMap R (DualNumber R)))

def epsScaleR (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom

def IsTangent {G : Over (Sp R)} [GrpObj G] (v : epsR R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = η[G].left

def IsLieComb {G : Over (Sp R)} [GrpObj G] {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) : Prop :=
  ∃ u : Fin n → (epsR R ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

def IsLieBasis {G : Over (Sp R)} [GrpObj G] {n : ℕ} (v : Fin n → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsTangent (v i)) ∧ ∀ w, IsTangent w → ∃! c : Fin n → R, IsLieComb c v w

end Lie

def constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) : Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)

structure KeyIn (R : Type) [CommRing R] where
  P : Out.PolAV (Sp R)
  g_pos : 1 ≤ P.g
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  th : P.L.Sec
  th_ne : ∀ s : Sp R, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th
  v : Fin P.g → (epsR R ⟶ P.A)
  basis : IsLieBasis v

def KeyPB {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R') : Prop :=
  ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

section Complex

variable {X : Scheme.{0}}

def valAt (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)

open Classical in
def valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ x ⁻¹ᵁ U then valAt x U h f else 0

structure HolUnif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) where
  ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  ex_onto : Function.Surjective ex
  Λ : Submodule ℤ (Fin g → ℂ)
  ker : ∀ z, ex z = 1 ↔ z ∈ Λ
  discrete : DiscreteTopology Λ
  full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤
  hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}
  fr : L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i}
  fr_ne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → fr i z ≠ 0
  fr_compat : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j) →
    fr i z = valAt' (ex z).left (L.U i ⊓ L.U j) (L.g i j).val * fr j z

namespace HolUnif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

def IsFn (s : L.Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → valAt' (u.ex z).left (L.U i) (s.f i) = θ z * u.fr i z

def IsRig (rig : LB.Gen (L.pull (eSec A))) : Prop :=
  ∀ j : (L.pull (eSec A)).ι, ⊤ ≤ (L.pull (eSec A)).U j →
    u.fr (j PUnit.unit) 0 = valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U j) (rig.s j).val

def IsDiff (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) (f : Γ(A.left, U)),
    TrivSqZeroExt.snd (show DualNumber ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.left.appLE U ⊤ h).hom f)) =
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w

def IsAH (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) ∧ (∀ l, ‖χ l‖ = 1) ∧
    ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)

end HolUnif

def thetaChar {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (z : Fin g → ℂ) : ℂ :=
  ∑' n : Fin g → ℤ, Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))

end Complex

def KeyFormula : Prop :=
  ∃ κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ,

    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ 8 * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ 4 * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧

    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧

    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (κ k xk : k) = r u) ∧

    (∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
      τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
      u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
      (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1) ∧

    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ‖(κ ℂ x : ℂ)‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

def KA (l : Level H) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {H.rt0, zeta l.A}

def baseKA (l : Level H) : Base l (KA l) where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := ⟨H.rt0, IntermediateField.subset_adjoin _ _ (by simp)⟩
  ρ_sq := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  ζ := ⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩
  ζ_prim := IsPrimitiveRoot.of_map_of_injective (f := (KA l).val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective

def Datum.dim (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * D.p * D.q

def constPt {k : Type} [Field k] {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) : Sp (DualNumber k) ⟶ X :=
  spMap (algebraMap k (DualNumber k)) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x

structure Moduli (D : Datum H) (l : Level H) where
  X : Scheme.{0}
  s : X ⟶ Sp (KA l)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D l (baseKA l) s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ o : Obj D l (baseKA l) s',
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : Obj D l (baseKA l) (x ≫ s)),
    Nonempty (ObjMap o univ x) → Nonempty (ObjMap o univ (constPt x)) → x = constPt x

structure Coeff (l : Level H) where
  F : IntermediateField ℚ ℂ
  fin : FiniteDimensional ℚ F
  conj : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F
  zeta_mem : zeta l.M' ∈ F
  le : KA l ≤ F

variable {D : Datum H} {l : Level H}

abbrev Moduli.XF (Xo : Moduli D l) (c : Coeff l) : Scheme.{0} :=
  pullback Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)

structure Model (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O] (β : O →+* c.F) where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  jQ : Xo.XF c ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = pullback.snd _ _
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  t : SAB H X
  oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  m0 : ObjMap oF Xo.univ (pullback.fst _ _)
  m : SABMap oF.t t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ

namespace Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

def j : Xo.XF c ⟶ Y.X := Y.jQ ≫ pullback.fst _ _

def Descends : Prop :=
  ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (GK : Over XK) (_ : GrpObj GK) (jK : Xo.X ⟶ XK)
    (φK : Xo.univ.t.G.left ⟶ GK.left) (e : pullback Y.s (spMap β) ⟶ XK)
    (GQ : Over (pullback Y.s (spMap β))) (_ : GrpObj GQ) (φ₁ : GQ.left ⟶ Y.t.G.left) (φ₂ : GQ.left ⟶ GK.left)
    (ψ : Y.oF.t.G.left ⟶ GQ.left),
    IsOpenImmersion jK ∧ jK ≫ sK = Xo.s ∧ IsGrpPullback Xo.univ.t.G GK jK φK ∧
    IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧
    Y.jQ ≫ e = pullback.fst _ _ ≫ jK ∧
    IsGrpPullback GQ Y.t.G (pullback.fst _ _) φ₁ ∧ IsGrpPullback GQ GK e φ₂ ∧
    ψ ≫ φ₁ = Y.m.φ ∧ ψ ≫ GQ.hom = Y.oF.t.G.hom ≫ Y.jQ ∧ ψ ≫ φ₂ = Y.m0.toSABMap.φ ≫ φK

def LevelActs : Prop :=
  ∀ (r : Xo.XF c ≅ Xo.XF c) (ν : SABMap Y.oF.t Y.oF.t r.hom) (gM gA : D.La →ₗ[𝓞 E] D.La),
    r.hom ≫ pullback.snd _ _ = pullback.snd _ _ →
    (∀ a, (Y.oF.eta (gM a)).left ≫ ν.φ = r.hom ≫ (Y.oF.eta a).left) →
    (∀ a, (Y.oF.etaA (gA a)).left ≫ ν.φ = r.hom ≫ (Y.oF.etaA a).left) →
    ∃ (ρ : Y.X ≅ Y.X) (mu : SABMap Y.t Y.t ρ.hom),
      ρ.hom ≫ Y.s = Y.s ∧ Y.j ≫ ρ.hom = r.hom ≫ Y.j ∧ Y.m.φ ≫ mu.φ = ν.φ ≫ Y.m.φ

def Extends (U : Y.X.Opens) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Prop :=
  ∃ σ' : U.toScheme ⟶ Y.t.G.left, σ' ≫ Y.t.G.hom = U.ι ∧
    ∀ j' : Xo.XF c ⟶ U.toScheme, j' ≫ U.ι = Y.j → j' ≫ σ' = σ.left ≫ Y.m.φ

end Model

def PushInvertible {X : Scheme.{0}} (G : Over X) (L : LB G.left) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
    (∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Γ(X, W), ∀ i,
      s i = (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom a *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ i)) ∧
    ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)

def IsTransition {l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {c : Coeff l} {c₂ : Coeff l₂}
    {O O₂ : Type} [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c₂.F}
    (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (b : O →+* O₂) (π : Y₂.X ⟶ Y.X) : Prop :=
  ∃ (π' : Y₂.X ⟶ pullback Y.s (spMap b)) (mu : SABMap Y₂.t Y.t π) (r : Xo₂.XF c₂ ⟶ Xo.XF c),
    π' ≫ pullback.fst _ _ = π ∧ π' ≫ pullback.snd _ _ = Y₂.s ∧ IsFinite π' ∧ Y₂.j ≫ π = r ≫ Y.j ∧
    (∀ a, (Y₂.oF.eta a ^ (l₂.M / l.M)).left ≫ Y₂.m.φ ≫ mu.φ = r ≫ (Y.oF.eta a).left ≫ Y.m.φ) ∧
    (∀ a, (Y₂.oF.etaA a ^ (l₂.A / l.A)).left ≫ Y₂.m.φ ≫ mu.φ = r ≫ (Y.oF.etaA a).left ≫ Y.m.φ)

def Dominates {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F}
    {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O') : Prop :=
  ∃ (f : pullback Y.s (spMap b) ⟶ Y'.X) (t : SAB H (pullback Y.s (spMap b)))
    (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t Y'.t f),
    f ≫ Y'.s = pullback.snd _ _ ∧
    (∀ a : Xo.XF c ⟶ pullback Y.s (spMap b), a ≫ pullback.fst _ _ = Y.j → a ≫ f = Y'.j) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y'.m.φ

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

