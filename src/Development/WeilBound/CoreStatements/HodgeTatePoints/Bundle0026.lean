module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfMul

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GiResAlg
section
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Gi

variable {R : Type} [CommRing R] {T T' : Type} [CommGroup T] [CommGroup T']

theorem pow_pull [Finite T] {B : Subalgebra R (T → R)} (hB : IsHopfOrder B) {f : T → R} (hf : f ∈ B) (k : ℕ) :
    (fun t => f (t ^ k)) ∈ B := by
  induction k generalizing f with
  | zero =>
    have e : (fun t : T => f (t ^ 0)) = algebraMap R (T → R) (f 1) := by
      funext t
      simp
    rw [e]
    exact B.algebraMap_mem _
  | succ k ih =>
    let L : (T × T → R) →ₗ[R] (T → R) :=
      { toFun := fun g t => g (t ^ k, t)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hmem : ∀ g ∈ prodSpan B, L g ∈ B := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact B.mul_mem (ih ha) hb
      | zero =>
        rw [map_zero]
        exact B.zero_mem
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact B.add_mem hx hy
      | smul r x _ hx =>
        rw [map_smul]
        exact B.smul_mem hx r
    have e : (fun t : T => f (t ^ (k + 1))) = L (fun z : T × T => f (z.1 * z.2)) := by
      funext t
      simp [L, pow_succ]
    rw [e]
    exact hmem _ (hB.comul f hf)

def IsLoc (H : Subgroup T) (B : Subalgebra R (T → R)) : Prop :=
  ∀ f : T → R, (∀ t, ∃ b ∈ B, ∀ h ∈ H, b h = f (t * h)) → f ∈ B

theorem isLoc_of_ind {H : Subgroup T} {B : Subalgebra R (T → R)}
    (h : B = indOrder H.subtype (resOrder H.subtype B)) : IsLoc H B := by
  intro f hf
  rw [h]
  change ∀ t : T, (fun x : H => f (t * H.subtype x)) ∈ resOrder H.subtype B
  intro t
  obtain ⟨b, hb, hbf⟩ := hf t
  refine Subalgebra.mem_map.2 ⟨b, hb, ?_⟩
  funext x
  simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun, hbf x x.2]


open Classical in
def cosetInd (R : Type) [CommRing R] (H : Subgroup T) (c : T ⧸ H) : T → R :=
  fun t => if (t : T ⧸ H) = c then 1 else 0

theorem cosetInd_mul (H : Subgroup T) (c : T ⧸ H) (t : T) {h : T} (hh : h ∈ H) :
    cosetInd R H c (t * h) = cosetInd R H c t := by
  have e : ((t * h : T) : T ⧸ H) = (t : T ⧸ H) := QuotientGroup.mk_mul_of_mem t hh
  unfold cosetInd
  rw [e]

theorem cosetInd_mem {H : Subgroup T} {B : Subalgebra R (T → R)} (hl : IsLoc H B) (c : T ⧸ H) :
    cosetInd R H c ∈ B := by
  apply hl
  intro t
  refine ⟨algebraMap R (T → R) (cosetInd R H c t), B.algebraMap_mem _, fun h hh => ?_⟩
  simp [cosetInd_mul H c t hh]

theorem sum_cosetInd (H : Subgroup T) [Fintype (T ⧸ H)] (F : T ⧸ H → T → R) (t : T) :
    (∑ c, cosetInd R H c * F c) t = F t t := by
  simp [cosetInd, Finset.sum_apply]

variable [Finite T'] {H : Subgroup T} {H' : Subgroup T'} {B : Subalgebra R (T → R)} {B' : Subalgebra R (T' → R)}
  (ι : T →* T')

private theorem translate_mem_of_isHopfOrder' {U : Type} [CommGroup U] {A : Subalgebra R (U → R)} (hA : IsHopfOrder A)
    {f : U → R} (hf : f ∈ A) (u : U) : (fun x => f (u * x)) ∈ A := by
  let L : (U × U → R) →ₗ[R] (U → R) :=
    { toFun := fun g x => g (u, x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem : ∀ g ∈ prodSpan A, L g ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      convert A.smul_mem hb (a u) using 1
    | zero =>
      rw [map_zero]
      exact A.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact A.add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul]
      exact A.smul_mem hx r
  exact hmem _ (hA.comul f hf)

theorem res_iff_abs (hB : IsHopfOrder B) (hB' : IsHopfOrder B') (hl : IsLoc H B) (hl' : IsLoc H' B')
    (hH : ∀ t, ι t ∈ H' → t ∈ H)
    (ha : ∀ f ∈ B', ∃ g ∈ B, ∀ h ∈ H, g h = f (ι h)) (hb : ∀ g ∈ B, ∃ f ∈ B', ∀ h ∈ H, g h = f (ι h))
    (g : T → R) : g ∈ B ↔ ∃ f ∈ B', ∀ t, g t = f (ι t) := by
  classical
  constructor
  · intro hg
    haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _
    have hex : ∀ t : T, ∃ f ∈ B', ∀ h ∈ H, g (t * h) = f (ι h) :=
      fun t => hb _ (translate_mem_of_isHopfOrder' hB hg t)
    choose fr hfr hfrH using hex
    let rep : T' ⧸ H' → T := fun c =>
      if hc : ∃ t : T, (ι t : T' ⧸ H') = c then hc.choose else 1
    have hrep : ∀ t0 : T, ((ι (rep (ι t0 : T' ⧸ H')) : T') : T' ⧸ H') = (ι t0 : T' ⧸ H') := by
      intro t0
      have hc : ∃ t : T, (ι t : T' ⧸ H') = (ι t0 : T' ⧸ H') := ⟨t0, rfl⟩
      simp only [rep, dif_pos hc]
      exact hc.choose_spec
    let F : T' ⧸ H' → T' → R := fun c s => fr (rep c) ((ι (rep c))⁻¹ * s)
    refine ⟨∑ c, cosetInd R H' c * F c, ?_, ?_⟩
    · refine Subalgebra.sum_mem _ (fun c _ => Subalgebra.mul_mem _ (cosetInd_mem hl' c) ?_)
      exact translate_mem_of_isHopfOrder' hB' (hfr (rep c)) _
    · intro t0
      rw [sum_cosetInd]
      set r := rep (ι t0 : T' ⧸ H') with hr
      have hmem' : (ι r)⁻¹ * ι t0 ∈ H' := QuotientGroup.eq.mp (hrep t0)
      have hmem : r⁻¹ * t0 ∈ H := hH _ (by simpa [map_mul, map_inv] using hmem')
      have := hfrH r _ hmem
      simp only [mul_inv_cancel_left] at this
      simp only [F, ← hr]
      rw [this, map_mul, map_inv]
  · rintro ⟨f, hf, hgf⟩
    apply hl
    intro t
    obtain ⟨g', hg', hg'H⟩ := ha _ (translate_mem_of_isHopfOrder' hB' hf (ι t))
    refine ⟨g', hg', fun h hh => ?_⟩
    rw [hg'H h hh, hgf, map_mul]

abbrev torsJ (B' : Subalgebra R (T' → R)) (N : ℕ) : Ideal B' :=
  Ideal.span {g : B' | ∃ h ∈ B', ∀ t, g.1 t = h (t ^ N) - h 1}

private theorem translate_mem_torsJ_of_pow_eq_one {N : ℕ} (hB' : IsHopfOrder B') {v : T'} (hv : v ^ N = 1) (j : B')
    (hj : j ∈ torsJ B' N) :
    (⟨fun x => j.1 (v * x), translate_mem_of_isHopfOrder' hB' j.2 v⟩ : B') ∈ torsJ B' N := by
  let τ : B' →+* B' :=
    { toFun := fun g => ⟨fun x => g.1 (v * x), translate_mem_of_isHopfOrder' hB' g.2 v⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hle : torsJ B' N ≤ Ideal.comap τ (torsJ B' N) := by
    refine Ideal.span_le.2 ?_
    rintro g ⟨h, hh, hg⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨h, hh, fun x => ?_⟩
    show g.1 (v * x) = h (x ^ N) - h 1
    rw [hg, mul_pow, hv, one_mul]
  exact hle hj

theorem ker_abs {N : ℕ} (hB' : IsHopfOrder B') (hl' : IsLoc H' B') (hN : ∀ t, ι t ^ N = 1)
    (hdiv : ∀ s : T', s ^ N ∈ H' → ∃ t, (ι t : T' ⧸ H') = s)
    (hc : ∀ f ∈ B', (∀ t, f (ι t) = 0) → ∃ j ∈ torsJ B' N, ∀ h ∈ H', j.1 h = f h)
    (f : B') (hf : ∀ t, f.1 (ι t) = 0) : f ∈ torsJ B' N := by
  classical
  haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _
  have hE : ∀ c : T' ⧸ H', cosetInd R H' c ∈ B' := fun c => cosetInd_mem hl' c
  have hdecomp : f = ∑ c, (⟨cosetInd R H' c, hE c⟩ : B') * f := by
    apply Subtype.ext
    funext x
    have key := sum_cosetInd (R := R) H' (fun _ => f.1) x
    simp only [Finset.sum_apply, Pi.mul_apply] at key
    simp [Finset.sum_apply, key]
  rw [hdecomp]
  refine Ideal.sum_mem _ (fun c _ => ?_)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  by_cases hs : s ^ N ∈ H'
  · obtain ⟨t, ht⟩ := hdiv s hs
    have hfu : (fun x => f.1 (ι t * x)) ∈ B' := translate_mem_of_isHopfOrder' hB' f.2 (ι t)
    obtain ⟨j, hj, hjH⟩ := hc _ hfu (fun t' => by
      show f.1 (ι t * ι t') = 0
      rw [← map_mul]
      exact hf _)
    have hv : (ι t)⁻¹ ^ N = 1 := by rw [inv_pow, hN, inv_one]
    have hτ := translate_mem_torsJ_of_pow_eq_one hB' hv j hj
    have heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f =
        (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') *
          ⟨fun x => j.1 ((ι t)⁻¹ * x), translate_mem_of_isHopfOrder' hB' j.2 (ι t)⁻¹⟩ := by
      apply Subtype.ext
      funext x
      show cosetInd R H' (s : T' ⧸ H') x * f.1 x = cosetInd R H' (s : T' ⧸ H') x * j.1 ((ι t)⁻¹ * x)
      by_cases hx : (x : T' ⧸ H') = s
      · have hmem : (ι t)⁻¹ * x ∈ H' := QuotientGroup.eq.mp (ht.trans hx.symm)
        simp only [hjH _ hmem, mul_inv_cancel_left]
      · simp [cosetInd, hx]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hτ
  · let h0 : T' → R := cosetInd R H' ((s : T' ⧸ H') ^ N)
    have hG : (fun x => h0 (x ^ N) - h0 1) ∈ B' := by
      have h1 := pow_pull hB' (hE ((s : T' ⧸ H') ^ N)) N
      exact Subalgebra.sub_mem _ h1 (B'.algebraMap_mem (h0 1))
    let G : B' := ⟨fun x => h0 (x ^ N) - h0 1, hG⟩
    have hGJ : G ∈ torsJ B' N := Ideal.subset_span ⟨h0, hE _, fun x => rfl⟩
    have heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f =
        ((⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f) * G := by
      apply Subtype.ext
      funext x
      show cosetInd R H' (s : T' ⧸ H') x * f.1 x =
        cosetInd R H' (s : T' ⧸ H') x * f.1 x * (h0 (x ^ N) - h0 1)
      by_cases hx : (x : T' ⧸ H') = s
      · have e1 : h0 (x ^ N) = 1 := by
          simp [h0, cosetInd, QuotientGroup.mk_pow, hx]
        have e2 : h0 1 = 0 := by
          simp only [h0, cosetInd]
          rw [if_neg]
          intro h1
          apply hs
          rw [← QuotientGroup.mk_pow] at h1
          have := QuotientGroup.eq.mp h1
          simpa using this
        rw [e1, e2, sub_zero, mul_one]
      · simp [cosetInd, hx]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hGJ

end PositivityTheory.HtPt.Gi
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfLin
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Htat.QuotientDualMap

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt v ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (v.appTop.hom s) := by
  rfl

theorem valAt_spec_comp {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (φ : B →+* C)
    (v : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ v) ⊤ le_top s = φ (valAt v ⊤ le_top s) := by
  rw [valAt_top, valAt_top, Scheme.Hom.comp_appTop]
  exact congrArg (fun f => f.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_mul [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (y z : Over.mk q ⟶ Γ.G) :
    valAt (B := B) (y * z).left ⊤ le_top s =
      valAt (B := B) y.left ⊤ le_top s * valAt (B := B) z.left ⊤ le_top s := by
  have h := (PositivityTheory.HtPt.Htat.ht_char_mul R T Γ χ s hs (Over.mk q)).1 y z
  rw [valAt_top, valAt_top, valAt_top, ← map_mul]
  exact congrArg _ h

theorem valAt_one [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {B : Type} [CommRing B]
    (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) :
    valAt (B := B) (1 : Over.mk q ⟶ Γ.G).left ⊤ le_top s = 1 := by
  have h := (PositivityTheory.HtPt.Htat.ht_char_mul R T Γ χ s hs (Over.mk q)).2
  rw [valAt_top]
  refine (congrArg _ h).trans ?_
  exact map_one _

theorem tors_one {Γ : QFGroup R T} {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (h : Γ.IsTorsionAlong G x N i)
    (Y : Over (Spec (CommRingCat.of R))) :
    (1 : Y ⟶ Γ.G).left ≫ i = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk ((1 : Y ⟶ Γ.G).left ≫ i) (by
    show ((1 : Y ⟶ Γ.G).left ≫ i) ≫ G.hom = Y.hom ≫ x
    rw [Category.assoc, h.isOver, ← Category.assoc, Over.w])
  have h1 := h.mul Y 1 1 y₀ y₀ rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : y₀ * y₀ = y₀ * 1 := by
    rw [_root_.mul_one]
    exact Over.OverMorphism.ext h1
  have h3 : y₀ = 1 := mul_left_cancel h2
  exact congrArg (fun f => f.left) h3

section Tangent

variable {A : Type} [CommRing A] (π : R →+* A)

abbrev qMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp π))

abbrev dMap : Spec (CommRingCat.of (DualNumber A)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (dualMap π))

theorem dMap_over : dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = qMap π := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul (c : R) :
    (epsMul (π c)).comp (dualMap π) = (dualMap π).comp (epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem epsMul_algebraMap (c : A) : (epsMul c).comp (algebraMap A (DualNumber A)) = algebraMap A (DualNumber A) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_dualMap : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp (dualMap π) =
    π.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem fst_q : ((TrivSqZeroExt.fstHom A A A).toRingHom).comp ((algebraMap A (DualNumber A)).comp π) = π := by
  refine RingHom.ext fun a => ?_
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

def IsTan (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (M : LieModel G x L) (e : L)
    (v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left) : Prop :=
  v ≫ Γ.G.hom = qMap π ∧ v ≫ i = dMap π ≫ (M.pt e).left

variable {π} {N : ℕ} {Γ : QFGroup R T} {i : Γ.G.left ⟶ G.left} {M : LieModel G x L}

theorem fst_valAt [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e : L}
    {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v) :
    (valAt v ⊤ le_top s).fst = 1 := by
  let r : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom π)
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)
  have hpq : p ≫ qMap π = r := by
    simp only [p, r, qMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fst_q]
  let y : Over.mk r ⟶ Γ.G := Over.homMk (p ≫ v) (by
    show (p ≫ v) ≫ Γ.G.hom = r
    rw [Category.assoc, hv.1, hpq])
  have hy : y = 1 := by
    apply h.inj (Over.mk r)
    rw [tors_one h]
    have hp : p ≫ dMap π = r ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
      simp only [p, r, dMap]
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fst_dualMap]
    let w : Over.mk (r ≫ x) ⟶ Over.mk x := Over.homMk r rfl
    have h1 : (w ≫ (1 : Over.mk x ⟶ G)).left = r ≫ (1 : Over.mk x ⟶ G).left := rfl
    rw [comp_one] at h1
    show (p ≫ v) ≫ i = (1 : Over.mk (r ≫ x) ⟶ G).left
    rw [h1, Category.assoc, hv.2, ← Category.assoc, hp, Category.assoc]
    exact congrArg (r ≫ ·) (M.tan e)
  have h2 : valAt (p ≫ v) ⊤ le_top s = 1 := by
    have h3 := valAt_one Γ χ s hs r
    rw [← hy] at h3
    exact h3
  have h4 := valAt_spec_comp (TrivSqZeroExt.fstHom A A A).toRingHom v s
  exact h4.symm.trans h2

theorem isTan_add [Finite T] (h : Γ.IsTorsionAlong G x N i) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) {e e' : L}
    {v v' : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left} (hv : IsTan π Γ i M e v)
    (hv' : IsTan π Γ i M e' v') :
    ∃ w, IsTan π Γ i M (e + e') w ∧ valAt w ⊤ le_top s = valAt v ⊤ le_top s * valAt v' ⊤ le_top s := by
  let y : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v hv.1
  let z : Over.mk (qMap π) ⟶ Γ.G := Over.homMk v' hv'.1
  let ρ : Over.mk (qMap π ≫ x) ⟶ epsAt x := Over.homMk (dMap π) (by
    show dMap π ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x = qMap π ≫ x
    rw [← Category.assoc, dMap_over])
  have hm := h.mul (Over.mk (qMap π)) y z (ρ ≫ M.pt e) (ρ ≫ M.pt e') hv.2.symm hv'.2.symm
  rw [← comp_mul, ← M.add] at hm
  exact ⟨(y * z).left, ⟨Over.w (y * z), hm.symm⟩, valAt_mul Γ χ s hs (qMap π) y z⟩

theorem isTan_smul (c : R) {e : L} {v : Spec (CommRingCat.of (DualNumber A)) ⟶ Γ.G.left}
    (hv : IsTan π Γ i M e v) :
    IsTan π Γ i M (c • e) (Spec.map (CommRingCat.ofHom (epsMul (π c))) ≫ v) := by
  constructor
  · rw [Category.assoc, hv.1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, epsMul_algebraMap]
  · rw [Category.assoc, hv.2, M.smul, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_epsMul]

end Tangent

theorem snd_epsMul {A : Type} [CommRing A] (c : A) (a : DualNumber A) :
    (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem char_on_tangent_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ s hs
  have hex : ∀ e : L, ∃ v, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e v ∧
      ∀ w, IsTan (Ideal.Quotient.mk (Ideal.span {(N : R)})) Γ i M e w → w = v :=
    fun e => _root_.GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion R T Γ S G x N i h L M e
  choose v hv hu using hex
  have hfst : ∀ e, (valAt (v e) ⊤ le_top s).fst = 1 := fun e => fst_valAt h χ s hs (hv e)
  refine ⟨{ toFun := fun e => (valAt (v e) ⊤ le_top s).snd, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro e e'
    obtain ⟨w, hw, hval⟩ := isTan_add h χ s hs (hv e) (hv e')
    rw [← hu _ w hw, hval, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [add_comm]
  · intro c e
    have h1 := hu _ _ (isTan_smul c (hv e))
    rw [← h1, valAt_spec_comp, snd_epsMul]
    simp [Algebra.smul_def]
  · intro e w hw
    rw [hu e w hw]
    ext
    · simp [hfst]
    · simp

end PositivityTheory.HtPt.Htat.QuotientDualMap

theorem PositivityTheory.HtPt.Htat.ht_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∃ l : L →ₗ[R] (R ⧸ Ideal.span {(N : R)}), ∀ (e : L) (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left → valAt v ⊤ le_top s = TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (l e) :=
  @PositivityTheory.HtPt.Htat.QuotientDualMap.char_on_tangent_linear
end
end

