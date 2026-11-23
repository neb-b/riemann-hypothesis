module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountWt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLC_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℤ)
    (h : ∀ j, IsLocallyConstant (f j)) : IsLocallyConstant (fun t => ∑ j ∈ s, f j t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

private theorem key {T Z S : Scheme.{0}} {p : Z ⟶ S} {π : T ⟶ S} {ι : Type} [Fintype ι] [IsFinite p]
    (hFib : FibFin) (σ : ι → (T ⟶ Z)) (m : ι → ℤ) (w : Wt Z) (hC : Counts p π σ m w) (A : Sq p)
    (φ : A.V → ℤ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] {U1 : Scheme.{0}} (f : U1 ⟶ T) (g : U1 ⟶ A.U)
    (hfg : f ≫ π = g ≫ A.u) (τ : ι → (U1 ⟶ A.V)) (hτv : ∀ j, τ j ≫ A.v = f ≫ σ j)
    (hτr : ∀ j, τ j ≫ A.r = g) (x1 : gp Ω ⟶ U1) :
    ∑ j, m j * φ (τ j (pt x1)) = ∑ᶠ z ∈ fib A.r (x1 ≫ g), w Ω (z ≫ A.v) * φ (pt z) := by
  classical
  haveI : IsFinite A.r := A.finite
  have hfin := hFib A.r Ω (x1 ≫ g)
  have hmem : ∀ j, x1 ≫ τ j ∈ fib A.r (x1 ≫ g) := fun j => by
    show (x1 ≫ τ j) ≫ A.r = x1 ≫ g
    rw [Category.assoc, hτr]
  have hiff : ∀ z ∈ fib A.r (x1 ≫ g), ∀ j, (x1 ≫ f) ≫ σ j = z ≫ A.v ↔ x1 ≫ τ j = z := by
    intro z hz j
    have hz' : z ≫ A.r = x1 ≫ g := hz
    constructor
    · intro h
      apply A.pb.hom_ext
      · rw [Category.assoc, hτv, ← Category.assoc, h]
      · rw [Category.assoc, hτr, hz']
    · intro h
      rw [← h, Category.assoc, Category.assoc, hτv]
  have hw : ∀ z ∈ fib A.r (x1 ≫ g),
      w Ω (z ≫ A.v) = ∑ j, if x1 ≫ τ j = z then m j else 0 := by
    intro z hz
    have hz' : z ≫ A.r = x1 ≫ g := hz
    have hsq : (z ≫ A.v) ≫ p = (x1 ≫ f) ≫ π := by
      rw [Category.assoc, A.pb.w, ← Category.assoc, hz', Category.assoc, ← hfg, Category.assoc]
    rw [hC Ω (x1 ≫ f) (z ≫ A.v) hsq, finsum_mem_def, finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : x1 ≫ τ j = z
    · rw [Set.indicator_of_mem
        (show j ∈ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from (hiff z hz j).mpr h) m, if_pos h]
    · rw [Set.indicator_of_notMem
        (show j ∉ {j | (x1 ≫ f) ≫ σ j = z ≫ A.v} from fun h' => h ((hiff z hz j).mp h')) m,
        if_neg h]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Finset.sum_congr rfl
    (g := fun z => (∑ j, if x1 ≫ τ j = z then m j else 0) * φ (pt z))
    (fun z hz => by rw [hw z (hfin.mem_toFinset.mp hz)])]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (hfin.mem_toFinset.mpr (hmem j)), pt_comp]

theorem UpperTheory.Gal.TranscendenceTraces.countWt_of :
    PtEx → PtLift → FibFin → CountWt := by
  intro hPE hPL hFib T Z S p π _ _ _ ι _ σ m w hσ hC
  classical
  haveI := Fintype.ofFinite ι
  intro A φ hφ
  let f : pullback π A.u ⟶ T := pullback.fst π A.u
  let g : pullback π A.u ⟶ A.U := pullback.snd π A.u
  have hfg : f ≫ π = g ≫ A.u := pullback.condition
  have hpb1 : IsPullback f g π A.u := IsPullback.of_hasPullback π A.u
  haveI : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) hpb1 inferInstance
  haveI : IsIntegralHom g :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) hpb1 inferInstance
  let τ : ι → (pullback π A.u ⟶ A.V) := fun j =>
    A.pb.lift (f ≫ σ j) g (by rw [Category.assoc, hσ j, hfg])
  have hτv : ∀ j, τ j ≫ A.v = f ≫ σ j := fun j => A.pb.lift_fst _ _ _
  have hτr : ∀ j, τ j ≫ A.r = g := fun j => A.pb.lift_snd _ _ _
  let χ : ↥(pullback π A.u) → ℤ := fun t => ∑ j, m j * φ (τ j t)
  have hχ : IsLocallyConstant χ :=
    isLC_sum Finset.univ (fun j t => m j * φ (τ j t))
      (fun j => (hφ.comp_continuous (τ j).continuous).comp (fun a => m j * a))
  have hconst : ∀ t1 t2, g t1 = g t2 → χ t1 = χ t2 := by
    intro t1 t2 h
    obtain ⟨Ω, hF, hA, x1, hx1⟩ := hPE _ t1
    letI := hF
    haveI := hA
    obtain ⟨z, hz, hzt⟩ := hPL g Ω (x1 ≫ g) t2 (by rw [pt_comp, hx1, h])
    have k1 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr x1
    have k2 := key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
    rw [hz] at k2
    show ∑ j, m j * φ (τ j t1) = ∑ j, m j * φ (τ j t2)
    rw [← hx1, ← hzt, k1, k2]
  have hsurj : Function.Surjective g := g.surjective
  let ψ : A.U → ℤ := fun s => χ (Function.surjInv hsurj s)
  have hψg : ∀ t, ψ (g t) = χ t := fun t => hconst _ _ (Function.surjInv_eq hsurj _)
  refine ⟨ψ, ?_, ?_⟩
  · have hq : Topology.IsQuotientMap g := g.isClosedMap.isQuotientMap g.continuous hsurj
    intro s
    rw [← hq.isOpen_preimage]
    have hpre : g ⁻¹' (ψ ⁻¹' s) = χ ⁻¹' s := by
      ext t
      simp only [Set.mem_preimage, hψg]
    rw [hpre]
    exact hχ s
  · intro Ω _ _ x
    obtain ⟨t, ht⟩ := hsurj (pt x)
    obtain ⟨z, hz, _⟩ := hPL g Ω x t ht
    rw [← hz, pt_comp, hψg]
    exact key hFib σ m w hC A φ Ω f g hfg τ hτv hτr z
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCycComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

open Classical in
private lemma cyc_eq_sum {S Y : Scheme.{0}} (c : Corr S Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y) (AF : Finset (gp Ω ⟶ c.Z)) (hAF : ∀ s, s ∈ AF ↔ s ≫ c.p = x) :
    c.cyc Ω x y = ∑ s ∈ AF with s ≫ c.f = y, c.w Ω s := by
  have hs : {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y} = ↑(AF.filter (fun s => s ≫ c.f = y)) := by
    ext z
    simp [hAF]
  show (∑ᶠ (z : gp Ω ⟶ c.Z) (_ : z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}), c.w Ω z) = _
  rw [hs, finsum_mem_coe_finset]

theorem UpperTheory.Gal.TranscendenceTraces.cycComp_of :
    FibFin → CycComp := by
  classical
  intro hF S Y X c d e a b pb hp hf hw Ω _ _ x y
  haveI := c.fin
  haveI := d.fin
  haveI := e.fin
  let A := (hF c.p Ω x).toFinset
  have hAm : ∀ s, s ∈ A ↔ s ≫ c.p = x := fun s => by simp [A, fib]
  let B : (gp Ω ⟶ Y) → Finset (gp Ω ⟶ d.Z) := fun t => (hF d.p Ω t).toFinset
  have hBm : ∀ t u, u ∈ B t ↔ u ≫ d.p = t := fun t u => by simp [B, fib]
  let E := (hF e.p Ω x).toFinset
  have hEm : ∀ z, z ∈ E ↔ z ≫ e.p = x := fun z => by simp [E, fib]
  have hR : (∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) =
      ∑ s ∈ A, c.w Ω s * d.cyc Ω (s ≫ c.f) y := by
    rw [finsum_eq_sum_of_support_subset (s := A.image (· ≫ c.f))]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image (· ≫ c.f)) (g := (· ≫ c.f))
          (fun s hs => Finset.mem_image_of_mem _ hs)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.1 hs).2]
    · intro t ht
      rw [Function.mem_support] at ht
      by_contra hn
      apply ht
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_eq_zero, zero_mul]
      intro s hs
      exact absurd (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨s, (Finset.mem_filter.1 hs).1, (Finset.mem_filter.1 hs).2⟩)) hn
  have hmaps : ∀ z ∈ E.filter (fun z => z ≫ e.f = y), z ≫ b ∈ A := by
    intro z hz
    rw [hAm, Category.assoc, ← hp]
    exact (hEm z).1 (Finset.mem_filter.1 hz).1
  rw [hR, cyc_eq_sum e Ω x y E hEm, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [cyc_eq_sum d Ω (s ≫ c.f) y (B (s ≫ c.f)) (hBm _), Finset.mul_sum]
  refine Finset.sum_bij' (fun z _ => z ≫ a)
    (fun u hu => pb.lift u s ((hBm _ u).1 (Finset.mem_filter.1 hu).1)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, hEm, hBm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pb.w, ← Category.assoc, hz.2]
    · rw [Category.assoc, ← hf, hz.1.2]
  · intro u hu
    have hu' := Finset.mem_filter.1 hu
    simp only [Finset.mem_filter, hEm]
    refine ⟨⟨?_, ?_⟩, pb.lift_snd _ _ _⟩
    · rw [hp, ← Category.assoc, pb.lift_snd]
      exact (hAm s).1 hs
    · rw [hf, ← Category.assoc, pb.lift_fst]
      exact hu'.2
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    apply pb.hom_ext
    · rw [pb.lift_fst]
    · rw [pb.lift_snd, hz'.2]
  · intro u hu
    exact pb.lift_fst _ _ _
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    rw [hw]
    show d.w Ω (z ≫ a) * c.w Ω (z ≫ b) = c.w Ω s * d.w Ω (z ≫ a)
    rw [hz'.2, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

namespace UpperTheory.Gal.TranscendenceTraces.FamilyComposition

variable {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S)

private def cr (A : Sq (r ≫ p)) : A.V ⟶ pullback p A.u :=
  pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w)

private lemma cr_fst (A : Sq (r ≫ p)) : cr r p A ≫ pullback.fst p A.u = A.v ≫ r := pullback.lift_fst _ _ _

private lemma cr_snd (A : Sq (r ≫ p)) : cr r p A ≫ pullback.snd p A.u = A.r := pullback.lift_snd _ _ _

private abbrev sqB (A : Sq (r ≫ p)) : Sq p := Sq.of p A.u

private def sqC (A : Sq (r ≫ p)) : Sq r :=
  ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, cr r p A,
    IsPullback.of_bot (by rw [cr_snd]; exact A.pb) (cr_fst r p A).symm (IsPullback.of_hasPullback p A.u)⟩

variable {r p}

private def mid {A A' : Sq (r ≫ p)} (t : A.To A') : pullback p A.u ⟶ pullback p A'.u :=
  pullback.lift (pullback.fst p A.u) (pullback.snd p A.u ≫ t.g)
    (by rw [Category.assoc, t.hu]; exact pullback.condition)

private lemma mid_fst {A A' : Sq (r ≫ p)} (t : A.To A') : mid t ≫ pullback.fst p A'.u = pullback.fst p A.u :=
  pullback.lift_fst _ _ _

private lemma mid_snd {A A' : Sq (r ≫ p)} (t : A.To A') :
    mid t ≫ pullback.snd p A'.u = pullback.snd p A.u ≫ t.g := pullback.lift_snd _ _ _

private def toB {A A' : Sq (r ≫ p)} (t : A.To A') : (sqB r p A).To (sqB r p A') :=
  ⟨t.g, mid t, t.hu, mid_fst t, mid_snd t⟩

private def toC {A A' : Sq (r ≫ p)} (t : A.To A') : (sqC r p A).To (sqC r p A') :=
  ⟨mid t, t.k, mid_fst t, by
      have := t.hv
      exact this, by
      change t.k ≫ cr r p A' = cr r p A ≫ mid t
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, cr_fst, mid_fst, cr_fst, ← Category.assoc, t.hv]
      · rw [Category.assoc, Category.assoc, cr_snd, mid_snd, ← Category.assoc, cr_snd, t.hr]⟩

variable (r p)

private def comp0 {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] {F : Shv R₁} {G : Shv R₂} {H : Shv R₃}
    (a : Fam0 r F G) (b : Fam0 p G H) : Fam0 (r ≫ p) F H where
  app A := (b.app (sqB r p A)).comp (a.app (sqC r p A))
  nat {A A'} t x := by
    have h1 := b.nat (toB t) (a.app (sqC r p A') x)
    have h2 := a.nat (toC t) x
    exact h1.trans (congrArg (b.app (sqB r p A)) h2)

private lemma zsmul_finsum_mem {ι M : Type*} [AddCommGroup M] (d : ℤ) {s : Set ι} (f : ι → M) (hs : s.Finite) :
    d • ∑ᶠ i ∈ s, f i = ∑ᶠ i ∈ s, d • f i :=
  (zsmulAddGroupHom d).map_finsum_mem f hs

end UpperTheory.Gal.TranscendenceTraces.FamilyComposition

open UpperTheory.Gal.TranscendenceTraces.FamilyComposition in
theorem UpperTheory.Gal.TranscendenceTraces.famComp_of :
    SumComp → FibFin → FamComp := by
  intro hS hF q i W Z S r p _ _ w' w τ' τ h' h
  refine ⟨⟨fun s => comp0 r p (τ'.deg s) (τ.deg s), fun A s t a => ?_⟩, fun A a => ?_, fun n a => ?_⟩
  · exact ((τ.comm (sqB r p A) s t _).trans
      (congrArg ((τ.deg t).app (sqB r p A)) (τ'.comm (sqC r p A) s t a)))
  · obtain ⟨b1, e1, s1⟩ := h' (sqC r p A) a
    obtain ⟨b2, e2, s2⟩ := h (sqB r p A) b1
    refine ⟨b2, (congrArg ((τ.deg 0).app (sqB r p A)) e1).trans e2, ?_⟩
    intro Ω _ _ x
    haveI fB : IsFinite (pullback.snd p A.u) := Sq.finite (sqB r p A)
    haveI fC : IsFinite (cr r p A) := Sq.finite (sqC r p A)
    have key := hS (cr r p A) (pullback.snd p A.u) Ω x (Sec (tw q i) (gp Ω))
      (fun z => (Wt.mul r w' w) Ω (z ≫ A.v) • Sec.res z a)
    rw [cr_snd] at key
    refine (s2 Ω x).trans (Eq.trans ?_ key.symm)
    refine finsum_mem_congr rfl fun (y : gp Ω ⟶ pullback p A.u) _ => ?_
    have e : (Sec.res y b1 : Sec (tw q i) (gp Ω)) = ∑ᶠ z ∈ fib (cr r p A) y, w' Ω (z ≫ A.v) • Sec.res z a := s1 Ω y
    refine (congrArg (fun m => w Ω (y ≫ pullback.fst p A.u) • m) e).trans ?_
    refine (zsmul_finsum_mem _ _ (hF (cr r p A) Ω y)).trans ?_
    refine finsum_mem_congr rfl fun z hz => ?_
    have hy : (z ≫ A.v) ≫ r = y ≫ pullback.fst p A.u := by
      have hz' : z ≫ cr r p A = y := hz
      rw [← hz', Category.assoc, Category.assoc, cr_fst]
    change _ = (w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r)) • Sec.res z a
    rw [hy, mul_comm, mul_smul]
  · let t1 : (sqB r p (Sq.self (r ≫ p))).To (Sq.self p) :=
      ⟨𝟙 S, pullback.fst p (𝟙 S), Category.comp_id _, Category.comp_id _,
        pullback.condition⟩
    let t2 : (sqC r p (Sq.self (r ≫ p))).To (Sq.self r) :=
      ⟨pullback.fst p (𝟙 S), 𝟙 W, Category.comp_id _, Category.comp_id _, by
        have := cr_fst r p (Sq.self (r ≫ p))
        exact (Eq.trans this.symm rfl : _)⟩
    have n1 := (τ.deg n).nat t1 ((τ'.deg n).app (Sq.self r) a)
    have n2 := (τ'.deg n).nat t2 a
    have e1 : (τ.deg n).app (Sq.self p) ((τ'.deg n).app (Sq.self r) a) =
        (τ.deg n).app (sqB r p (Sq.self (r ≫ p))) (Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a)) :=
      (res_id _).symm.trans n1
    have e2 : Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a) =
        (τ'.deg n).app (sqC r p (Sq.self (r ≫ p))) a :=
      n2.trans (congrArg _ (res_id a))
    exact (e1.trans (congrArg _ e2)).symm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamLin
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

private def famAdd {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ τ' : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => (τ.deg s).app A + (τ'.deg s).app A, fun t a => by
    simp only [AddMonoidHom.add_apply]
    rw [← (τ.deg s).nat t a, ← (τ'.deg s).nat t a]
    exact map_add _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.add_apply]
    rw [← τ.comm, ← τ'.comm]
    exact map_add _ _ _

private def famSmul {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (d : ℤ) (τ : Fam p I J) : Fam p I J where
  deg s := ⟨fun A => d • (τ.deg s).app A, fun t a => by
    simp only [AddMonoidHom.smul_apply]
    rw [← (τ.deg s).nat t a]
    exact map_zsmul _ _ _⟩
  comm A s t a := by
    simp only [AddMonoidHom.smul_apply]
    rw [← τ.comm]
    exact map_zsmul _ _ _

private theorem isIso_r {S : Scheme.{0}} (A : Sq (𝟙 S)) : IsIso A.r := A.pb.isIso_snd_of_isIso

private def resInv {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) : Sec F A.V →+ Sec F A.U :=
  haveI := isIso_r A
  AddMonoidHom.mk' (fun a => Sec.res (inv A.r) a) (fun a b => map_add _ _ _)

private theorem resInv_apply {S : Scheme.{0}} {R : Type} [CommRing R] (F : Shv R) (A : Sq (𝟙 S)) [IsIso A.r] (a : Sec F A.V) :
    resInv F A a = Sec.res (inv A.r) a := rfl

private def famId (S : Scheme.{0}) {R : Type} [CommRing R] (I : Cx R) (d : ℤ) : Fam (𝟙 S) I I where
  deg s := ⟨fun A => d • resInv (I.X s) A, fun {A B} t a => by
    haveI := isIso_r A
    haveI := isIso_r B
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    have e : t.g ≫ inv B.r = inv A.r ≫ t.k := by
      rw [IsIso.comp_inv_eq, Category.assoc, t.hr, IsIso.inv_hom_id_assoc]
    rw [show Sec.res t.g (d • Sec.res (inv B.r) a) = d • Sec.res t.g (Sec.res (inv B.r) a) from map_zsmul _ _ _,
      res_res, res_res, e]⟩
  comm A s t a := by
    haveI := isIso_r A
    simp only [AddMonoidHom.smul_apply, resInv_apply]
    rw [show Sec.map (I.d s t) (d • Sec.res (inv A.r) a) = d • Sec.map (I.d s t) (Sec.res (inv A.r) a) from map_zsmul _ _ _,
      map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famLin_of :
    FibFin → FamLin := by
  intro hF q i
  refine ⟨?_, ?_, ?_⟩
  · intro Z S p _ w w' τ τ' hτ hτ'
    refine ⟨famAdd τ τ', fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    obtain ⟨b', hb', hs'⟩ := hτ' A a
    refine ⟨b + b', ?_, fun Ω _ _ x => ?_⟩
    · change (τ.deg 0).app A _ + (τ'.deg 0).app A _ = _
      rw [hb, hb']
      exact (map_add _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (b + b') = Sec.res x b + Sec.res x b' from map_add _ _ _, hs Ω x, hs' Ω x,
        ← finsum_mem_add_distrib hfin]
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.add, add_smul]
  · intro Z S p _ d w τ hτ
    refine ⟨famSmul d τ, fun A a => ?_, fun n A a => rfl⟩
    obtain ⟨b, hb, hs⟩ := hτ A a
    refine ⟨d • b, ?_, fun Ω _ _ x => ?_⟩
    · change d • (τ.deg 0).app A _ = _
      rw [hb]
      exact (map_zsmul _ _ _).symm
    · haveI := Sq.finite A
      have hfin := hF A.r Ω x
      rw [show Sec.res x (d • b) = d • Sec.res x b from map_zsmul _ _ _, hs Ω x]
      have := (zsmulAddGroupHom (α := Sec (tw q i) (gp Ω)) d).map_finsum_mem
        (fun z => w Ω (z ≫ A.v) • Sec.res z a) hfin
      refine this.trans ?_
      refine finsum_mem_congr rfl fun z _ => ?_
      simp only [Wt.smul, mul_smul, zsmulAddGroupHom_apply]
  · intro S d
    refine ⟨famId S _ d, fun A a => ?_, fun n a => ?_⟩
    · haveI := isIso_r A
      refine ⟨d • Sec.res (inv A.r) a, ?_, fun Ω _ _ x => ?_⟩
      · change d • resInv ((res _ (tw q i)).X 0) A (Sec.map (resι _ (tw q i)) a) = _
        rw [resInv_apply, ← map_res]
        exact (map_zsmul _ _ _).symm
      · have hf : fib A.r x = {x ≫ inv A.r} := by
          ext z
          simp only [fib, Set.mem_setOf_eq, Set.mem_singleton_iff]
          rw [IsIso.eq_comp_inv]
        rw [hf, finsum_mem_singleton]
        rw [show Sec.res x (d • Sec.res (inv A.r) a) = d • Sec.res x (Sec.res (inv A.r) a) from map_zsmul _ _ _, res_res]
        rfl
    · change d • resInv ((res _ (tw q i)).X n) (Sq.self (𝟙 S)) a = _
      haveI := isIso_r (Sq.self (𝟙 S))
      rw [resInv_apply]
      have e : inv (Sq.self (𝟙 S)).r = 𝟙 _ := IsIso.inv_id
      rw [e]
      exact congrArg (d • ·) (res_id a)

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamSemi
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.famSemi_of :
    FamSemi := by
  intro Z S p R₁ R₂ R₃ _ _ _ I J K
  refine ⟨fun τ ρ => ?_, fun ρ τ => ?_⟩
  · refine ⟨⟨fun s => ⟨fun A => (ρ.app A.U s).comp ((τ.deg s).app A), ?_⟩, ?_⟩, fun _ _ _ => rfl⟩
    · intro A B t a
      change Sec.res t.g (ρ.app B.U s ((τ.deg s).app B a)) = ρ.app A.U s ((τ.deg s).app A (Sec.res t.k a))
      rw [ρ.nat t.g s, (τ.deg s).nat t a]
    · intro A s t a
      change Sec.map (K.d s t) (ρ.app A.U s ((τ.deg s).app A a)) =
        ρ.app A.U t ((τ.deg t).app A (Sec.map (I.d s t) a))
      rw [ρ.comm A.U s t, τ.comm A s t a]
  · refine ⟨⟨fun s => ⟨fun A => ((τ.deg s).app A).comp (ρ.app A.V s), ?_⟩, ?_⟩, fun _ _ _ => rfl⟩
    · intro A B t a
      change Sec.res t.g ((τ.deg s).app B (ρ.app B.V s a)) = (τ.deg s).app A (ρ.app A.V s (Sec.res t.k a))
      rw [(τ.deg s).nat t, ρ.nat t.k s]
    · intro A s t a
      change Sec.map (K.d s t) ((τ.deg s).app A (ρ.app A.V s a)) =
        (τ.deg t).app A (ρ.app A.V t (Sec.map (I.d s t) a))
      rw [τ.comm A s t, ρ.comm A.V s t]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem fib_spec_finite (Ω B : Type) [Field Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] :
    (fib (Ω := Ω) (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) (𝟙 (gp Ω))).Finite := by
  apply (Set.finite_range (fun g : B →ₐ[Ω] Ω => Spec.map (CommRingCat.ofHom (g : B →+* Ω)))).subset
  intro z hz
  have hz' : z ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = 𝟙 _ := hz
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = z := ⟨Spec.preimage z, Spec.map_preimage z⟩
  rw [← Spec.map_comp, ← Spec.map_id] at hz'
  have h2 := Spec.map_injective hz'
  refine ⟨{ φ.hom with commutes' := fun c => ?_ }, ?_⟩
  · have := congrArg (fun g => g.hom c) h2
    simpa using this
  · rfl

theorem UpperTheory.Gal.TranscendenceTraces.fibFin_of :
    Chart → FibFin := by
  intro hC
  unfold Chart at hC
  unfold FibFin
  intro V U r _ Ω _ x
  obtain ⟨B, iB, iAB, v, hfin, hpb⟩ := hC r Ω x
  haveI := hfin
  have h := (fib_bijOn hpb (𝟙 (gp Ω))).image_eq
  rw [Category.id_comp] at h
  rw [← h]
  exact (fib_spec_finite Ω B).image _
end

