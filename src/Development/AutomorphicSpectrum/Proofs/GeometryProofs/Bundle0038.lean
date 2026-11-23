module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
section
namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]

def latOn (D : HTChart A K c p R N (Module.Dual K Li)) (V : Submodule K Li) (t : K) (B : Subring K) : Set Li :=
  {e | e ∈ V ∧ ∀ w ∈ D.om', t * w e ∈ B}

def IsLocIn (A : Type) {K : Type} [CommRing A] [Field K] [Algebra A K] (B : Subring K) : Prop :=
  (∀ a : A, algebraMap A K a ∈ B) ∧
    ∀ b ∈ B, ∃ u a : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ algebraMap A K u * b = algebraMap A K a

end
end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem exists_extend_lin {A K V W : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
    (M : Submodule A V) (g : M →ₗ[A] W) : ∃ G : V →ₗ[K] W, ∀ z : M, G z = g z := by
  classical
  obtain ⟨b, hbM, -, hsp, hli⟩ := exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)
  let bb := Basis.extend hli
  let f : V → W := fun x => if h : x ∈ M then g ⟨x, h⟩ else 0
  let G : V →ₗ[K] W := bb.constr K fun i => f i.1
  have hGb : ∀ x ∈ b, G x = f x := fun x hx => by
    have hx' : x ∈ hli.extend (Set.subset_univ b) := hli.subset_extend _ hx
    have := bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩
    simpa [bb, G, Basis.extend_apply_self] using this
  have hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro h
      rw [hGb x hx]
      simp [f, h]
    | zero =>
      intro h
      have : (⟨0, h⟩ : M) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have h2 : y ∈ M := Submodule.span_le.2 hbM hy
      have : (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩ := rfl
      rw [map_add (f := _), ihx h1, ihy h2, this, map_add (f := _)]
    | smul a x hx ih =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have : (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩ := rfl
      rw [this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]
  have hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b := by
    intro v hv
    have hinj := IsFractionRing.injective A K
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨a', ha', hy⟩ := hy
      refine ⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul r x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) r
      have hv0 : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)
      refine ⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩
      have : (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x := by
        rw [← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ hx
  refine ⟨G, fun z => ?_⟩
  obtain ⟨a, ha, haz⟩ := hden z (hsp z.2)
  have h1 := hG _ haz (M.smul_mem a z.2)
  have h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z := rfl
  rw [h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)] at h1
  exact smul_right_injective W ha h1

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
  (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li)

theorem eigProj_dual (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w = w ∘ₗ eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ := by
  ext v
  simp [eigProj, LinearMap.sum_apply, hact]

theorem eigProj_apply (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w e = w e := by
  rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
  congr 1
  have h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e := fun a => by
    rw [LatBasic.mem_eigSp.1 he]
    simp [hc]
  have h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e := by
    apply LatBasic.eigProj_of_mem
    rw [LatBasic.mem_eigSp]
    exact fun a => h1 a
  exact h2

theorem exists_vec [IsDomain A] [IsFractionRing A K] (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (g : Module.Dual A (D.omHT σ)) :
    ∃ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), ∀ z : D.omHT σ,
      (z : Module.Dual K Li) e = algebraMap A K (g z) := by
  let U : Submodule K (Module.Dual K Li) := Submodule.span K (D.om : Set _)
  haveI : Module.Finite K U := by
    obtain ⟨S, hS⟩ := D.om_lat.fg
    have : U = Submodule.span K (S : Set _) := by
      dsimp [U]
      rw [← hS, Submodule.span_span_of_tower]
    rw [this]
    exact Module.Finite.span_of_finite K S.finite_toSet
  let T := U.map (eigProj D.ρΩ σ)
  haveI : Module.Finite K T := Module.Finite.iff_fg.mpr (Submodule.FG.map (eigProj D.ρΩ σ) (Module.Finite.iff_fg.mp (show Module.Finite K U from inferInstance)))
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)
  let B : Li →ₗ[K] Module.Dual K T := T.subtype.dualMap.comp (Module.Dual.eval K Li)
  have hB : Function.Injective B.flip := by
    intro x y h
    apply Subtype.ext
    ext v
    exact LinearMap.congr_fun h v
  obtain ⟨v, hv⟩ := (LinearMap.flip_injective_iff₂.mp hB) (G.comp T.subtype)
  have hv' : ∀ w ∈ T, w v = G w := by
    intro w hw
    exact LinearMap.congr_fun hv ⟨w, hw⟩
  have hom : D.om' ≤ D.om := by
    rw [HTChart.om', sup_le_iff]
    constructor
    · exact Submodule.span_le.mpr (Set.range_subset_iff.mpr D.h_mem)
    · rintro _ ⟨x, hx, rfl⟩
      exact D.om.smul_mem _ hx
  refine ⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩
  · have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
    rw [LatBasic.mem_eigSp] at h ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  · intro z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li) := hz
    have he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
      rw [LatBasic.mem_eigSp] at h ⊢
      intro a
      have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
        apply RingOfIntegers.ext
        simp [hc]
      have := h (RingOfIntegers.mapRingEquiv c a)
      simpa [hinv] using this
    rw [← hz', eigProj_apply D ρ hc hact σ he w]
    have h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v := by
      rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
    have hzT : (z : Module.Dual K Li) ∈ T := by
      rw [← hz']
      exact ⟨w, Submodule.subset_span (hom hw), rfl⟩
    rw [h2, hz', hv' _ hzT, hG z]
    rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueLatOfChartBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TieVB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq t) = secVal ξ U h t := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)
  exact congrArg (fun f => f.hom t) e2

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · intro hs
    have hu := hs.map (genMap ξ q)
    refine ⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := hs
    refine ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩
    have : genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right this
  · rintro ⟨h0, -, ⟨s', hs'⟩⟩
    have : s * s' = 1 := hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])
    exact IsUnit.of_mul_eq_one _ this

theorem mem_basicOpen_iff (hg : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (t : Γ(X, U)) : q.1 ∈ X.basicOpen t ↔ unitAt ξ q (secVal ξ U h t) := by
  rw [Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]

theorem unitAt_mul {p : Cpt ξ} {s t : Ω} (hs : unitAt ξ p s) (ht : unitAt ξ p t) : unitAt ξ p (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp [one_mem]⟩

theorem regAt_genPt (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  unfold genMap
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.id_comp]
  rfl

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

theorem exists_chart (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (h : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q) ∧
      (∀ q : X, q ∈ U → genPt ξ ⤳ q) ∧
      Function.Injective (secVal ξ U h) ∧
      ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ a ∈ (secVal ξ U h).range := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have h : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h2, _⟩ := (hmem q).1 hq
    exact h2
  have hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩
  obtain ⟨hinj, hran⟩ := _root_.GlobalTheory.CompanionTheory.Ar.regAt_sections X Ω ξ hT.gen U h hsp
  refine ⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩
  rw [hT.ring c hc a]
  refine Iff.trans ?_ (hran a).symm
  exact forall_congr' fun q => (by rw [hUq q])

theorem exists_point (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (P : Ideal (chartRing o x c)) (hP : P.IsPrime) :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ ∀ s : chartRing o x c, s ∈ P ↔ ¬ unitAt ξ p s := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  let φ : Γ(X, U) →+* chartRing o x c :=
    (secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨P.comap φ, inferInstance⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let q : Cpt ξ := ⟨_, hsp _ hyU⟩
  refine ⟨q, (hUq q).1 hyU, fun s => ?_⟩
  obtain ⟨t, ht⟩ := (hran s).1 s.2
  have hst : s = φ t := Subtype.ext ht.symm
  have key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ := by
    show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have h2 := mem_basicOpen_iff hT.gen U h q hyU t
  have h3 : (s : Ω) = secVal ξ U h t := ht.symm
  rw [h3, ← h2, key, hst, Ideal.mem_comap, not_not]

theorem exists_den (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) : ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s * a ∈ chartRing o x c :=
  (_root_.GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ o κ x hT c p hp a).1 ha

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_den_span (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) (M : AddSubgroup E)
    (hM : ∀ a ∈ chartRing o x c, ∀ e ∈ M, a • e ∈ M) {e : E}
    (he : e ∈ Submodule.span (regAt ξ p) (M : Set E)) :
    ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s • e ∈ M := by
  induction he using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩
  | zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htM⟩ := hv
    refine ⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩
    have h1 : (s * t) • (u + v) = t • s • u + s • t • v := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [h1]
    exact add_mem (hM t ht _ hsM) (hM s hs _ htM)
  | smul r u _ hu =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htr⟩ := exists_den hT hp r.2
    refine ⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩
    have h1 : (t * s) • r • u = (t * (r : Ω)) • s • u := by
      rw [Subring.smul_def, smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hM _ htr _ hsM

end Chart

section Bundle

variable {κ : Type} {x : κ → Ω} {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

end Bundle

end GlobalTheory.CompanionTheory.Ar.TieVB

namespace GlobalTheory.CompanionTheory.Ar

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstant
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem notMem_mCoordIdeal_of_aeval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {h : MRing ι} (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hh
  apply h0
  have e := UnitChart.aeval_scaled y (fun _ => 1) h
  simp only [mul_one] at e
  rw [e, show mConeMap y h = 0 from hh, map_zero]

theorem exists_flatHerm_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  intro K _ ι _ Ω _ F _ _ y φ α hO
  obtain ⟨hy, hR⟩ := hO
  choose c hc using id hy
  obtain ⟨m, G, hG, e⟩ := UnitChart.chart_form hc (hR c hc (α : 𝓞 F))
  have hα : ((α : 𝓞 F) : F) ≠ 0 := by
    simp
  have hφα : φ ((α : 𝓞 F) : F) ≠ 0 := (map_ne_zero φ).2 hα
  have hprod : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hg0 : aeval y (UnitChart.cMon c m) ≠ 0 := by rwa [UnitChart.aeval_cMon]
  have hG0 : aeval y G ≠ 0 := by rw [← e]; exact mul_ne_zero hφα hprod
  have e' : aeval y G = φ ((α : 𝓞 F) : F) * aeval y (UnitChart.cMon c m) := by
    rw [UnitChart.aeval_cMon, e]
  have hq : aeval y G / aeval y (UnitChart.cMon c m) = φ ((α : 𝓞 F) : F) := by
    rw [e', mul_div_cancel_right₀ _ hg0]
  have hinv : φ (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = (φ ((α : 𝓞 F) : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((α : 𝓞 F) : F) = 1 := by
      have h1 : ((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (α : 𝓞 F) = 1 := α.inv_mul
      have h2 := congrArg (algebraMap (𝓞 F) F) h1
      rw [map_mul, map_one] at h2
      exact h2
    rw [this, map_one]
  have hfn := notMem_mCoordIdeal_of_aeval_ne_zero hG0
  have hgn := notMem_mCoordIdeal_of_aeval_ne_zero hg0
  refine ⟨{ M := 1
            M_pos := one_pos
            f := G
            g := UnitChart.cMon c m
            df := m
            dg := m
            hf := hG
            hg := UnitChart.homog_cMon c m
            deg := fun k => by simp [constLine, HermLine.ofWeight]
            f_ne := hfn
            g_ne := hgn
            unit := ?_
            κ := fun σ => ‖σ ((α : 𝓞 F) : F)‖
            κ_pos := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hα)
            κ_conj := fun σ => by simp [ComplexEmbedding.conjugate_coe_eq]
            norm := ?_ }, rfl, fun _ => rfl⟩
  · rw [isUnitSec_iff_chart K ι Ω y G _ m m hy hG (UnitChart.homog_cMon c m) hfn hgn]
    intro c' hc'
    simp only [sub_self, neg_zero, zpow_zero, Finset.prod_const_one, mul_one, hq]
    exact ⟨hR c' hc' _, hinv ▸ hR c' hc' _⟩
  · intro σ z hz
    rw [hz.2 _ m G _ hG (UnitChart.homog_cMon c m) e', norm_mul]
    simp [constLine, HermLine.ofWeight]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameOpenNeighbourhood
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem frame_spread_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsCohOn T → p ∈ T → L.IsFrameAt b p → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q ∈ T, q.1 ∈ U → L.IsFrameAt b q :=
  PositivityTheory.HtPt.Mc.frame_spread

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_via_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E), CoordTie ℤ ξ x → L.IsVB r V → IsTwistGen ξ x L m φ → LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V → ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | exact GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_ratio_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | exact GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart.exists_eq_div_adjoin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChangeStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_field_change : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | exact GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericFieldStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBoundStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_projection_bound : ∀ (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li), IsExtOver i ι → Submodule.span Ω (Set.range ι) = ⊤ → ∀ (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ) (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω) (m : Ω₀), Submodule.span W L = Submodule.span W (ι '' L₀) → (∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) → (∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j)) → (∀ j, m • b₀ j ∈ L₀) → (∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0) → (∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) → (∀ j, κ • b j ∈ L) → (∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) → (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧ ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Frames.two_frames | exact GlobalTheory.CompanionTheory.Ar.Frames.two_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Frames.two_frames <;> assumption)
end

