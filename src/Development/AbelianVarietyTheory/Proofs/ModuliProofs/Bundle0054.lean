module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0050

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem existsUnique_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    (hf : ∀ i j (T : Scheme.{0}) (x : T ⟶ Z i) (y : T ⟶ Z j), x ≫ ψ i = y ≫ ψ j → x ≫ f i = y ≫ f j) :
    ∃! F : X ⟶ Y, ∀ i, ψ i ≫ F = f i := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers I Z ψ (fun x => by simpa using hc x) hψ
  refine ⟨C.glueMorphisms f fun i j => hf i j _ _ _ pullback.condition, fun i => C.ι_glueMorphisms _ _ i,
    fun F hF => C.hom_ext _ _ fun i => (hF i).trans (C.ι_glueMorphisms f _ i).symm⟩

theorem hom_ext {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) {F F' : X ⟶ Y}
    (h : ∀ i, ψ i ≫ F = ψ i ≫ F') : F = F' :=
  (existsUnique_hom ψ hψ hc (fun i => ψ i ≫ F') fun _ _ _ _ _ e => by
    rw [← Category.assoc, e, Category.assoc]).unique h fun _ => rfl

theorem exists_hom {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    {B : I → I → Scheme.{0}} {a : ∀ i j, B i j ⟶ Z i} {b : ∀ i j, B i j ⟶ Z j}
    (hB : ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) (hf : ∀ i j, a i j ≫ f i = b i j ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, ψ i ≫ F = f i :=
  (existsUnique_hom ψ hψ hc f fun i j _ x y e => by
    rw [← (hB i j).lift_fst x y e, Category.assoc, hf, ← Category.assoc, (hB i j).lift_snd]).exists

variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens}

theorem exists_mem (hU : iSup U = ⊤) (s : S) : ∃ i, s ∈ U i :=
  TopologicalSpace.Opens.mem_iSup.1 (show s ∈ iSup U by rw [hU]; trivial)

theorem isOpenImmersion {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) : IsOpenImmersion ψ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

theorem mem_range {X Z : Scheme.{0}} {V : S.Opens} {p : X ⟶ S} {q : Z ⟶ V.toScheme} {ψ : Z ⟶ X}
    (h : IsPullback ψ q p V.ι) (x : X) : x ∈ Set.range ψ ↔ p x ∈ V := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact (q z).2
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h x ⟨p x, hx⟩ rfl
    exact ⟨z, hz⟩

theorem covers (hU : iSup U = ⊤) {X : Scheme.{0}} {Z : I → Scheme.{0}} {p : X ⟶ S} {q : ∀ i, Z i ⟶ (U i).toScheme}
    {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι) (x : X) : ∃ i, x ∈ Set.range (ψ i) :=
  (exists_mem hU (p x)).imp fun i hi => (mem_range (h i) x).2 hi

theorem over_ext (hU : iSup U = ⊤) {T A : Over S} {f g : T ⟶ A}
    (h : ∀ i (T' : Over (U i).toScheme) (r : Over.mk (T'.hom ≫ (U i).ι) ⟶ T), r ≫ f = r ≫ g) : f = g := by
  ext1
  refine hom_ext (fun i => (T.hom ⁻¹ᵁ U i).ι) (fun _ => inferInstance)
    (covers hU fun i => (isPullback_morphismRestrict T.hom (U i)).flip) fun i => ?_
  exact congrArg (fun z => z.left) (h i (Over.mk (T.hom ∣_ U i))
    (Over.homMk (T.hom ⁻¹ᵁ U i).ι (morphismRestrict_ι _ _).symm))

theorem exists_lift {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} (x₀ : Over.mk (T.hom ≫ f) ⟶ A) :
    ∃ x : T ⟶ G, x₀.left = x.left ≫ ψ :=
  ⟨Over.homMk (h.lift x₀.left T.hom (Over.w x₀)) (h.lift_snd _ _ _), (h.lift_fst _ _ _).symm⟩

theorem lift_ext {S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {G : Over S'} {ψ : G.left ⟶ A.left}
    (h : IsPullback ψ G.hom A.hom f) {T : Over S'} {x y : T ⟶ G} (e : x.left ≫ ψ = y.left ≫ ψ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueUniformisingVectorVerticalTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.VertFamily

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)

private theorem valAt'_add' {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f + f') = valAt' y W f + valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (W : X.Opens) (f f' : Γ(X, W)) :
    valAt' y W (f * f') = valAt' y W f * valAt' y W f' := by
  unfold valAt' valAt
  split_ifs <;> simp

private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {W W' : X.Opens} (hle : W' ≤ W)
    (h : ⊤ ≤ y ⁻¹ᵁ W') (f : Γ(X, W)) : valAt' y W' (resG X hle f) = valAt' y W f := by
  have hW : ⊤ ≤ y ⁻¹ᵁ W := fun x hx => hle (h hx)
  unfold valAt' valAt
  rw [dite_eq_left h, dite_eq_left hW]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

private theorem valAt'_constFn_top {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : y ≫ p = 𝟙 _) (a : ℂ) :
    valAt' y ⊤ (constFn p ⊤ a) = a := by
  have hq : ∀ (q : Sp ℂ ⟶ Sp ℂ) (e : ⊤ ≤ q ⁻¹ᵁ ⊤), q = 𝟙 _ →
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((q.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a := by
    rintro q e rfl
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    show (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op (⊤ : (Sp ℂ).Opens)))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) = a
    simp
  have e0 : ⊤ ≤ y ⁻¹ᵁ (⊤ : X.Opens) := fun _ _ => trivial
  unfold valAt' valAt constFn
  rw [dite_eq_left e0]
  refine Eq.trans ?_ (hq (y ≫ p) (fun _ _ => trivial) hp)
  congr 1
  rw [← CommRingCat.comp_apply]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE y p ⊤ ⊤ ⊤ _ e0)

theorem ex_over (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 _ := by
  exact (Over.w (u.ex z)).trans (by simp)

theorem differentiableAt_val (z : Fin g → ℂ) (O : A.left.Opens) (f : Γ(A.left, O)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O) :
    DifferentiableAt ℂ (fun z' => valAt' (u.ex z').left O f) z := by
  obtain ⟨hO, hD⟩ := u.hol O f
  exact hD.differentiableAt (hO.mem_nhds h)

theorem ptDer_fderiv (z w : Fin g → ℂ) :
    PtDer (u.ex z).left (fun O f => fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w) := by
  constructor
  · intro O h f f'
    have e : (fun z' => valAt' (u.ex z').left O (f + f')) =
        (fun z' => valAt' (u.ex z').left O f) + fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_add' _ _ _ _
    rw [e, fderiv_add (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    rfl
  · intro O h f f'
    have e : (fun z' => valAt' (u.ex z').left O (f * f')) =
        (fun z' => valAt' (u.ex z').left O f) * fun z' => valAt' (u.ex z').left O f' := by
      funext z'
      exact valAt'_mul_of_top_le_preimage_open _ _ _ _
    rw [e, fderiv_mul (differentiableAt_val u z O f h) (differentiableAt_val u z O f' h)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  · intro O O' hle h f
    have hev : (fun z' => valAt' (u.ex z').left O' (resG A.left hle f)) =ᶠ[nhds z]
        fun z' => valAt' (u.ex z').left O f := by
      filter_upwards [(u.hol O' (resG A.left hle f)).1.mem_nhds h] with z' hz'
      exact valAt'_resG _ hle hz' f
    rw [hev.fderiv_eq]

theorem fderiv_constFn (z w : Fin g → ℂ) (a : ℂ) :
    fderiv ℂ (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) z w = 0 := by
  have e : (fun z' => valAt' (u.ex z').left ⊤ (constFn A.hom ⊤ a)) = fun _ => a := by
    funext z'
    exact valAt'_constFn_top _ _ (ex_over u z') a
  rw [e]
  simp

theorem fn_eq {X : Scheme.{0}} (m : A.left ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    fn u m W f = fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  funext z'
  unfold fn valAt' valAt
  by_cases h : ⊤ ≤ ((u.ex z').left ≫ m) ⁻¹ᵁ W
  · rw [dite_eq_left h, dite_eq_left (show ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]
    congr 1
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (u.ex z').left ⁻¹ᵁ (m ⁻¹ᵁ W) from h)]

theorem existsUnique_vector : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z δ, PtDer ((u.ex z).left ≫ m) δ → (∀ r, δ ⊤ (constFn p ⊤ r) = 0) → ∃! w, ∀ W f, z ∈ dom u m W → δ W f = fderiv ℂ (fn u m W f) z w := by
  intro P₀ u Hm χ hG R _ x₀ X p m _ hpb z δ hδ hc
  obtain ⟨hex, huniq⟩ := _root_.GlobalTheory.KS.ptDer_of_fibre P₀.A R x₀ X p m hpb (u.ex z).left (ex_over u z)
  obtain ⟨δ₀, hδ₀, hc₀, hδδ₀⟩ := hex δ hδ hc
  obtain ⟨w, hw, hwu⟩ := _root_.GlobalTheory.KS.TangentAt.tangent_at_point P₀ u Hm χ hG z δ₀ hδ₀ hc₀
  refine ⟨w, fun W f hz => ?_, fun w' hw' => hwu w' fun O f hO => ?_⟩
  · rw [hδδ₀ W f hz, hw (m ⁻¹ᵁ W) ((m.app W).hom f) hz, fn_eq]
  · have hD := ptDer_fderiv u z w'
    have hpt : PtDer (u.ex z).left
        (fun O f => δ₀ O f - fderiv ℂ (fun z' => valAt' (u.ex z').left O f) z w') := by
      refine ⟨fun V hV f f' => ?_, fun V hV f f' => ?_, fun V V' hle hV f => ?_⟩
      · have h1 := hδ₀.add V hV f f'
        have h2 := hD.add V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.mul V hV f f'
        have h2 := hD.mul V hV f f'
        linear_combination h1 - h2
      · have h1 := hδ₀.res V V' hle hV f
        have h2 := hD.res V V' hle hV f
        linear_combination h1 - h2
    have key := huniq _ hpt (fun a => by
        have h1 := hc₀ a
        have h2 := fderiv_constFn u z w' a
        linear_combination h1 - h2)
      (fun V f hV => by
        have h1 := hδδ₀ V f hV
        have h2 := hw' V f hV
        rw [fn_eq] at h2
        linear_combination h2 - h1) O f hO
    exact sub_eq_zero.mp key

end GlobalTheory.KS.VertFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousComponentMulMemSpanDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory


open MvPolynomial in
theorem homogeneousComponent_mul_mem_span_degree {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) {d₀ d e : ℕ}
    (h₀ : d₀ ≤ d) (he : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀})
    (a : MvPolynomial σ K) :
    homogeneousComponent e (a * F) ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  induction hF using Submodule.span_induction generalizing a with
  | mem G hG =>
    obtain ⟨hGI, hG⟩ := hG
    induction a using MvPolynomial.induction_on' with
    | monomial m c =>
      have hm : (monomial m c * G).IsHomogeneous (m.degree + d₀) :=
        (isHomogeneous_monomial c rfl).mul hG
      rw [homogeneousComponent_of_mem hm]
      split_ifs with h
      · obtain ⟨m₂, hle, hdeg⟩ := Finsupp.exists_le_degree_eq m (d - d₀) (by omega)
        obtain ⟨m₁, rfl⟩ := exists_add_of_le hle
        have : (monomial (m₂ + m₁) c : MvPolynomial σ K) * G = monomial m₁ c * (monomial m₂ 1 * G) := by
          rw [← _root_.mul_assoc, monomial_mul, _root_.mul_one, add_comm]
        rw [this]
        refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨I.mul_mem_left _ hGI, ?_⟩)
        have h2 := (isHomogeneous_monomial (1 : K) hdeg).mul hG
        rwa [Nat.sub_add_cancel h₀] at h2
      · exact Ideal.zero_mem _
    | add a b ha hb => rw [add_mul, map_add (f := _)]; exact Ideal.add_mem _ ha hb
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _)]; exact Ideal.add_mem _ (hx a) (hy a)
  | smul r x _ hx => rw [smul_eq_mul, ← _root_.mul_assoc]; exact hx _

theorem cutBy_of_regular_of_zeroEstimate : ∀ (K σ Hh : Type) [Field K] (I : Ideal (MvPolynomial σ K)) (Q : Polynomial ℚ) (d₀ d : ℕ) (p : Hh → σ → K), d₀ ≤ d → (∀ e ≥ d₀, (dimDeg I e : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀}) → (∀ F ∈ I, ∀ h, MvPolynomial.eval (p h) F = 0) → (∀ F : MvPolynomial σ K, F.IsHomogeneous d → (∀ h, MvPolynomial.eval (p h) F = 0) → F ∈ I) → CutBy I Q d p := by
  intro K σ Hh _ I Q d₀ d p h₀ hreg hvan hzero e he
  have hV : vanIdeal d p = Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    unfold vanIdeal
    congr 1
    ext F
    exact ⟨fun h => ⟨hzero F h.1 h.2, h.1⟩, fun h => ⟨h.2, hvan F h.1⟩⟩
  refine ⟨(hreg e (h₀.trans he)).1, fun F hF => ⟨fun hI => ?_, fun h => ?_⟩⟩
  · have h := homogeneousComponent_mul_mem_span_degree I h₀ he ((hreg e (h₀.trans he)).2 F hI hF) 1
    rw [_root_.one_mul, MvPolynomial.homogeneousComponent_of_mem hF, if_pos rfl] at h
    rwa [hV]
  · rw [hV] at h
    exact (Ideal.span_le.2 fun G (hG : G ∈ {G : MvPolynomial σ K | G ∈ I ∧ G.IsHomogeneous d}) => hG.1) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantTowerAlgebraMapInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem mem_smul_ker_of_flat_quotient {B T C : Type} [CommRing B] [AddCommGroup T] [Module B T]
    [AddCommGroup C] [Module B C] [Module.Flat B C] (φ : T →ₗ[B] C) (hφ : Function.Surjective φ)
    (q : Ideal B) (x : LinearMap.ker φ) (hx : (x : T) ∈ q • (⊤ : Submodule B T)) :
    x ∈ q • (⊤ : Submodule B (LinearMap.ker φ)) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat φ hφ (LinearMap.ker φ).subtype
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map φ) (B ⧸ q)
  have h0 : ∀ (M : Type) [AddCommGroup M] [Module B M] (y : M),
      ((1 : B ⧸ q) ⊗ₜ[B] y = 0 ↔ y ∈ q • (⊤ : Submodule B M)) := by
    intro M _ _ y
    rw [← Submodule.Quotient.mk_eq_zero, ← TensorProduct.quotTensorEquivQuotSMul_symm_mk,
      LinearEquiv.map_eq_zero_iff]
  rw [← h0]
  apply hinj
  rw [LinearMap.lTensor_tmul, map_zero, h0]
  exact hx

theorem ideal_eq_bot_of_forall_prime_smul_mem {B T : Type} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal T) (hJ : J.FG)
    (h : ∀ q : Ideal B, q.IsPrime → ∀ x ∈ J, ∃ s : B, s ∉ q ∧
      s • x ∈ q • (J.restrictScalars B)) : J = ⊥ := by
  by_cases hJt : Submodule.annihilator J = ⊤
  · exact Submodule.annihilator_eq_top_iff.1 hJt
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJt
  have hle : J ≤ n • J := by
    intro x hxJ
    obtain ⟨s, hs, hx⟩ := h (n.comap (algebraMap B T)) (Ideal.comap_isPrime _ _) x hxJ
    have hx' : s • x ∈ n • J := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr c hc
        rw [← algebraMap_smul T r c]
        exact Submodule.smul_mem_smul hr hc
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    obtain ⟨t, m, hm, e⟩ := hn.exists_inv (x := algebraMap B T s) hs
    have e' : x = t • (s • x) + m • x := by
      rw [← algebraMap_smul T s x, ← mul_smul, ← add_smul, e, one_smul]
    rw [e']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx') (Submodule.smul_mem_smul hm hxJ)
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n J hJ hle
  have hrJ : r ∈ n := hJn (Submodule.mem_annihilator.2 hrM)
  exfalso
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one]
  have := n.sub_mem hrJ hr
  rwa [sub_sub_cancel] at this

theorem isPushout_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R] [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R] [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C] [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ] [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) → Function.Injective (algebraMap R C) → (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) → IsNoetherianRing R → Module.Finite A B → Module.Finite R C → Module.Flat B C → (∀ q : Ideal B, q.IsPrime → (Nat.card (q.inertia Γ) : B) ∉ q) → (∀ q : Ideal B, q.IsPrime → ∀ g ∈ q.inertia Γ, ∀ c : C, g • c - c ∈ q.map (algebraMap B C)) → Algebra.IsPushout A B R C := by
  intro Γ _ _ A B R C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hAB hRC heq hnoeth hfAB hfRC hflat hcard hI
  classical
  haveI := Fintype.ofFinite Γ
  haveI : SMulCommClass A Γ B := SMulCommClass.symm _ _ _
  let φ : B ⊗[A] R →ₐ[B] C := Algebra.TensorProduct.lift (Algebra.ofId B C)
    (IsScalarTower.toAlgHom A R C) (fun _ _ => Commute.all _ _)
  have hφ : ∀ (b : B) (r : R), φ (b ⊗ₜ r) = algebraMap B C b * algebraMap R C r := by
    intro b r
    simp [φ, Algebra.ofId_apply]
  have hsurj : Function.Surjective φ := by
    have := span_range_algebraMap_eq_top_of_tame Γ A B R C hAB hRC heq hfRC hcard hI
    have h2 : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← this, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact ⟨1 ⊗ₜ r, by simp [hφ]⟩
    exact LinearMap.range_eq_top.1 h2
  have hR : ∀ (g : Γ) (r : R), g • algebraMap R C r = algebraMap R C r := by
    intro g r
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hequi : ∀ (g : Γ) (x : B ⊗[A] R), φ (g • x) = g • φ x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b r => rw [TensorProduct.smul_tmul', hφ, hφ, smul_mul', heq, hR]
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), smul_add, hx, hy]
  have hsl : ∀ (g : Γ) (b : B) (x : B ⊗[A] R), g • (b • x) = (g • b) • (g • x) := by
    intro g b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r => simp only [TensorProduct.smul_tmul', smul_eq_mul, smul_mul']
    | add x y hx hy => simp only [smul_add, hx, hy]
  have htr : ∀ x : B ⊗[A] R, ∃ r : R, ∑ g : Γ, g • x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c r =>
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := Γ) (∑ g : Γ, g • c) (by
        intro k
        rw [Finset.smul_sum]
        simp only [← mul_smul]
        exact Equiv.sum_comp (Equiv.mulLeft k) (fun g => g • c))
      refine ⟨a • r, ?_⟩
      simp only [TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, ← ha, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp only [smul_add, Finset.sum_add_distrib, hr, hs, TensorProduct.tmul_add]⟩
  have hinv : ∀ x : B ⊗[A] R, φ x = 0 → (∀ g : Γ, g • x = x) → x = 0 := by
    intro x hx hg
    obtain ⟨b, hb⟩ := exists_finsum_smul_eq_one_of_tame Γ B hcard
    rw [finsum_eq_sum_of_fintype] at hb
    obtain ⟨r, hr⟩ := htr (b • x)
    simp only [hsl, hg] at hr
    rw [← Finset.sum_smul, hb, one_smul] at hr
    rw [hr, hφ, map_one, _root_.one_mul, map_eq_zero_iff _ hRC] at hx
    rw [hr, hx, TensorProduct.tmul_zero]
  have hinert : ∀ q : Ideal B, ∀ g ∈ q.inertia Γ, ∀ x : B ⊗[A] R,
      g • x - x ∈ q • (⊤ : Submodule B (B ⊗[A] R)) := by
    intro q g hg x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      have : g • (c ⊗ₜ[A] r) - c ⊗ₜ[A] r = (g • c - c) • ((1 : B) ⊗ₜ[A] r) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, TensorProduct.sub_tmul]
      rw [this]
      exact Submodule.smul_mem_smul (hg c) Submodule.mem_top
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hx hy
  let K : Submodule B (B ⊗[A] R) := LinearMap.ker φ.toLinearMap
  have hK : ∀ x, x ∈ K ↔ φ x = 0 := fun x => Iff.rfl
  letI : SMul Γ K := ⟨fun g x => ⟨g • (x : B ⊗[A] R), by
    rw [hK, hequi, (hK _).1 x.2, smul_zero]⟩⟩
  letI : DistribMulAction Γ K :=
    Function.Injective.distribMulAction K.subtype.toAddMonoidHom K.injective_subtype
      (fun _ _ => rfl)
  haveI : IsNoetherianRing (B ⊗[A] R) := by
    haveI : IsNoetherianRing (R ⊗[A] B) := Algebra.FiniteType.isNoetherianRing R _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hker : RingHom.ker φ = ⊥ := by
    refine ideal_eq_bot_of_forall_prime_smul_mem (B := B) _ (IsNoetherian.noetherian _) ?_
    intro q hq x hx
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem_span_invariants_sup Γ B K
      (fun g b y => Subtype.ext (hsl g b y)) q hq (hcard q hq)
      (fun g hg y => mem_smul_ker_of_flat_quotient φ.toLinearMap hsurj q _ (hinert q g hg y))
      ⟨x, hx⟩
    refine ⟨s, hs, ?_⟩
    have hbot : Submodule.span B {y : K | ∀ g : Γ, g • y = y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      intro y hy
      exact Subtype.ext (hinv y y.2 fun g => congrArg Subtype.val (hy g))
    rw [hbot, bot_sup_eq, Submodule.mem_smul_top_iff] at hsx
    exact hsx
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  exact ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective φ.toLinearMap ⟨hinj, hsurj⟩)
    (fun r => (hφ 1 r).trans (by simp))⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SharpRelations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS

noncomputable section
namespace GlobalTheory.SharpRel

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y := by
  have hl : x.left ≫ φ = y.left ≫ φ := congrArg CommaMorphism.left e
  ext1
  exact h.1.hom_ext hl (by rw [Over.w x, Over.w y])

theorem push_comp (h : IsGrpPullback A' A f φ) {p : A ⟶ A} {p' : A' ⟶ A'}
    (e : p'.left ≫ φ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h T (x ≫ p') = pushHom h T x ≫ p := by
  ext1
  change (x ≫ p').left ≫ φ = (x.left ≫ φ) ≫ p.left
  rw [Over.comp_left, Category.assoc, Category.assoc, e]

end

end GlobalTheory.SharpRel
end
end

