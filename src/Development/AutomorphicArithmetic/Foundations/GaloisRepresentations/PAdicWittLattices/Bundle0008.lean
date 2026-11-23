module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem mem_lev {G : Type} [Group G] {K : Subgroup G} {h u : G} :
    u ∈ lev K h ↔ u ∈ K ∧ h * u * h⁻¹ ∈ K := (Iff.rfl)

private theorem ind_eq_one {G : Type} [Group G] (R : Type) [Field R] {K : Subgroup G} {g x : G}
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K) : ind R K g x = 1 := by
  simp [ind, Set.indicator_of_mem hx]

private theorem ind_eq_zero {G : Type} [Group G] (R : Type) [Field R] {K : Subgroup G} {g x : G}
    (hx : x ∉ DoubleCoset.doubleCoset g (K : Set G) K) : ind R K g x = 0 := by
  simp [ind, Set.indicator_of_notMem hx]

private theorem class_eq {G : Type} [Group G] {K : Subgroup G} {h : G}
    (p : K) (b : K ⧸ (lev K h).subgroupOf K) (e : (QuotientGroup.mk p : K ⧸ (lev K h).subgroupOf K) = b) :
    (QuotientGroup.mk ((p : G) * h⁻¹) : G ⧸ K) = QuotientGroup.mk (((b.out : K) : G) * h⁻¹) := by
  subst e
  have h0 : (p⁻¹ * (QuotientGroup.mk p : K ⧸ (lev K h).subgroupOf K).out : K) ∈ (lev K h).subgroupOf K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
  have h1 := (mem_lev.mp (Subgroup.mem_subgroupOf.mp h0)).2
  rw [QuotientGroup.eq]
  convert h1 using 1
  push_cast
  group

private theorem fib_inj {G : Type} [Group G] {K : Subgroup G} {h : G}
    (b b' : K ⧸ (lev K h).subgroupOf K)
    (e : (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K) = QuotientGroup.mk (((b'.out : K) : G) * h⁻¹)) :
    b = b' := by
  rw [QuotientGroup.eq] at e
  rw [← QuotientGroup.out_eq' b, ← QuotientGroup.out_eq' b', QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_lev]
  refine ⟨(b.out⁻¹ * b'.out).2, ?_⟩
  convert e using 1
  push_cast
  group

private theorem count {G : Type} [Group G] {R : Type} {M : Type v} [Field R] [AddCommGroup M] [Module R M]
    (K K' : Subgroup G) (h : G) (hle : K' ≤ lev K h) [Finite (K ⧸ K'.subgroupOf K)] [Fintype (K ⧸ K'.subgroupOf K)]
    (φ : G ⧸ K → M) :
    ∑ a : K ⧸ K'.subgroupOf K, φ (QuotientGroup.mk (((a.out : K) : G) * h⁻¹)) =
      K'.relIndex (lev K h) • ∑ᶠ y : G ⧸ K, (ind R K h⁻¹ y.out) • φ y := by
  classical
  have hLK : lev K h ≤ K := inf_le_left
  have hle' : K'.subgroupOf K ≤ (lev K h).subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))
  let e := Subgroup.quotientEquivProdOfLE hle'
  haveI : Finite ((K ⧸ (lev K h).subgroupOf K) ×
      ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K))) :=
    Finite.of_equiv _ e
  haveI : Nonempty ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) :=
    ⟨QuotientGroup.mk 1⟩
  haveI : Nonempty (K ⧸ (lev K h).subgroupOf K) := ⟨QuotientGroup.mk 1⟩
  haveI : Finite (K ⧸ (lev K h).subgroupOf K) :=
    Finite.prod_left ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K))
  haveI : Finite ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) :=
    Finite.prod_right (K ⧸ (lev K h).subgroupOf K)
  letI := Fintype.ofFinite (K ⧸ (lev K h).subgroupOf K)
  letI := Fintype.ofFinite ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K))
  have key : ∀ a, (e a).1 = QuotientGroup.mk (a.out : K) := by
    intro a
    conv_lhs => rw [← QuotientGroup.out_eq' a]
    rfl
  have hcard : Fintype.card ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) =
      K'.relIndex (lev K h) := by
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.relIndex_subgroupOf hLK
  have hψ : Function.Injective
      (fun b : K ⧸ (lev K h).subgroupOf K => (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K)) :=
    fun b b' hb => fib_inj b b' hb
  have hR : ∑ᶠ y : G ⧸ K, (ind R K h⁻¹ y.out) • φ y =
      ∑ b : K ⧸ (lev K h).subgroupOf K, φ (QuotientGroup.mk (((b.out : K) : G) * h⁻¹)) := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image
      (fun b : K ⧸ (lev K h).subgroupOf K => (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K))) _ ?sub]
    · rw [Finset.sum_image (fun b _ b' _ hb => hψ hb)]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (((b.out : K) : G) * h⁻¹)
      have hm : (QuotientGroup.mk (((b.out : K) : G) * h⁻¹) : G ⧸ K).out ∈
          DoubleCoset.doubleCoset h⁻¹ (K : Set G) K := by
        rw [hk, DoubleCoset.mem_doubleCoset]
        exact ⟨b.out, b.out.2, k, k.2, rfl⟩
      rw [ind_eq_one R hm, one_smul]
    · intro y hy
      rw [Function.mem_support] at hy
      have hm : y.out ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set G) K := by
        by_contra hn
        rw [ind_eq_zero R hn, zero_smul] at hy
        exact hy rfl
      obtain ⟨k1, hk1, k2, hk2, he⟩ := DoubleCoset.mem_doubleCoset.mp hm
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨QuotientGroup.mk ⟨k1, hk1⟩, Finset.mem_univ _, ?_⟩)
      show (QuotientGroup.mk ((((QuotientGroup.mk ⟨k1, hk1⟩ : K ⧸ (lev K h).subgroupOf K).out : K) : G) * h⁻¹) :
        G ⧸ K) = y
      rw [← class_eq ⟨k1, hk1⟩ _ rfl, ← QuotientGroup.out_eq' y, he, QuotientGroup.eq]
      have hk2' : k2 ∈ K := hk2
      show (k1 * h⁻¹)⁻¹ * (k1 * h⁻¹ * k2) ∈ K
      simpa [mul_assoc] using hk2'
  calc ∑ a : K ⧸ K'.subgroupOf K, φ (QuotientGroup.mk (((a.out : K) : G) * h⁻¹))
      = ∑ a : K ⧸ K'.subgroupOf K, φ (QuotientGroup.mk ((((e a).1.out : K) : G) * h⁻¹)) :=
        Finset.sum_congr rfl (fun a _ => congrArg φ (class_eq a.out (e a).1 (key a).symm))
    _ = ∑ x : (K ⧸ (lev K h).subgroupOf K) ×
          ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)),
          φ (QuotientGroup.mk (((x.1.out : K) : G) * h⁻¹)) :=
        Equiv.sum_comp e (fun x => φ (QuotientGroup.mk (((x.1.out : K) : G) * h⁻¹)))
    _ = Fintype.card ((lev K h).subgroupOf K ⧸ (K'.subgroupOf K).subgroupOf ((lev K h).subgroupOf K)) •
          ∑ b : K ⧸ (lev K h).subgroupOf K, φ (QuotientGroup.mk (((b.out : K) : G) * h⁻¹)) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Finset.smul_sum]
    _ = _ := by rw [hcard, hR]

private theorem isOp_of {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y Z' W : Scheme.{0}} (p : Z ⟶ B)
    (p' : Z' ⟶ B) (s : Y ⟶ Z) (t : Y ⟶ Z') (A : T.H p' →ₗ[R] T.H p) (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r)
    (Γ : Type) [Group Γ] [Finite Γ] (a : Γ → (W ⟶ W)) (J : Type) [Fintype J] (σ : J → (W ⟶ Y))
    (h : ∀ j, (σ j ≫ t) ≫ p' = r) (h1 : IsGalois c Γ a) (h2 : Splits s c σ)
    (h3 : ∀ x, T.pull c hc (A x) = ∑ j, T.pull (σ j ≫ t) (h j) x) : T.IsOp p p' s t A := by
  subst hc
  exact ⟨W, c, Γ, inferInstance, inferInstance, a, J, inferInstance, σ, h, h1, h2, h3⟩

private theorem pull_eq {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Y Z : Scheme.{0}} {p : Z ⟶ B} {q : Y ⟶ B}
    {f g : Y ⟶ Z} (e : f = g) (hf : f ≫ p = q) (hg : g ≫ p = q) (x : T.H p) : T.pull f hf x = T.pull g hg x := by
  subst e
  rfl

theorem UpperTheory.Gal.G3.pHopOp :
    FnRing → HopEx.{u} → TwSplit → TwGal → HopOp.{u} := by
  intro hF hE hS hG B G _ X R _ _ T hT i j h a b
  classical
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have hil : X.K i ≤ lev (X.K j) h := fun u hu => mem_lev.mpr ⟨hij hu, b.2 u hu⟩
  have hL : lev (X.K j) h ≤ X.K j := inf_le_left
  have hn : (X.K i).relIndex (lev (X.K j) h) ≠ 0 := by
    have := X.idx i j
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hil hL] at this
    exact left_ne_zero_of_mul this
  refine ⟨hn, ?_⟩
  obtain ⟨m, hmj, hnorm, hS'⟩ := X.deep j {(i, (1 : G))}
  have hmi : X.K m ≤ X.K i := fun u hu => by
    simpa using hS' (i, 1) (Finset.mem_singleton_self _) u hu
  haveI : Finite (X.K j ⧸ (X.K i).subgroupOf (X.K j)) := Nat.finite_of_card_ne_zero (X.idx i j)
  letI : Fintype (X.K j ⧸ (X.K i).subgroupOf (X.K j)) := Fintype.ofFinite _
  have bm : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one hmj
  have bmi : X.admitted m i 1 := X.isAdmissibleIntegralBasisChange_one hmi
  have admr : ∀ c : X.K j ⧸ (X.K i).subgroupOf (X.K j), X.admitted m i ((c.out : G))⁻¹ := fun c =>
    ⟨X.K_le j _ (inv_mem c.out.2), fun u hu => hmi (hnorm _ (inv_mem c.out.2) u hu)⟩
  obtain ⟨Γ, _, _, r', c', -, -, hgal⟩ := hG X m j bm hnorm
  have hsplit := hS X m i j a bm hmi hnorm (X.K j ⧸ (X.K i).subgroupOf (X.K j))
    (fun c => ((c.out : G))⁻¹) admr (fun c => inv_mem c.out.2) (by
      intro k hk
      refine ⟨QuotientGroup.mk ⟨k⁻¹, inv_mem hk⟩, ?_, ?_⟩
      · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul ((X.K i).subgroupOf (X.K j)) (⟨k⁻¹, inv_mem hk⟩ : X.K j)
        simp only [inv_inv]
        rw [hu]
        have hu' : ((u : X.K j) : G) ∈ X.K i := Subgroup.mem_subgroupOf.mp u.2
        simpa [mul_assoc] using hu'
      · intro c hc
        simp only [inv_inv] at hc
        rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [mul_inv_rev] using inv_mem hc)
  have hσ : ∀ c : X.K j ⧸ (X.K i).subgroupOf (X.K j),
      (X.tr m i ((c.out : G))⁻¹ (admr c).1 (admr c).2 ≫ X.tr i j h b.1 b.2) ≫ X.q j = X.q m := by
    intro c
    rw [Category.assoc, X.tr_q, X.tr_q]
  have hfn : X.IsFn j (ind R (X.K j) h⁻¹) := (hF X R j).1 h b.1
  have hhop := (hE X T hT j _ hfn).1
  have hadm : ∀ g : G, ind R (X.K j) h⁻¹ g ≠ 0 → X.admitted m j g⁻¹ := by
    intro g hg
    have hm : g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
      by_contra hn'
      exact hg (ind_eq_zero R hn')
    obtain ⟨k1, hk1, k2, hk2, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hm
    have e1 : (k1 * h⁻¹ * k2)⁻¹ = k2⁻¹ * (h * (1 * k1⁻¹)) := by group
    rw [e1]
    have hk1' : k1⁻¹ ∈ X.K j := inv_mem hk1
    have hk2' : k2⁻¹ ∈ X.K j := inv_mem hk2
    have a1 : X.admitted m m k1⁻¹ := ⟨X.K_le j _ hk1', fun u hu => hnorm _ hk1' u hu⟩
    exact Tower.admitted.mul (Tower.admitted.mul (Tower.admitted.mul a1 bmi) b) (X.tower_admissible_self hk2')
  show T.IsOp (X.q j) (X.q j) _ _ _
  refine isOp_of T _ _ _ _ _ (X.q m) (X.tr m j 1 bm.1 bm.2) (X.tr_q _ _ _ _ _) Γ _
    (X.K j ⧸ (X.K i).subgroupOf (X.K j))
    (fun c => X.tr m i ((c.out : G))⁻¹ (admr c).1 (admr c).2) hσ hgal hsplit ?_
  intro x
  have hφ : ∀ c : X.K j ⧸ (X.K i).subgroupOf (X.K j),
      T.pull (X.tr m i ((c.out : G))⁻¹ (admr c).1 (admr c).2 ≫ X.tr i j h b.1 b.2) (hσ c) x =
        X.pl T m j ((QuotientGroup.mk ((c.out : G) * h⁻¹) : G ⧸ X.K j).out)⁻¹ x := by
    intro c
    have adm1 : X.admitted m j (h * ((c.out : G))⁻¹) := Tower.admitted.mul (admr c) b
    rw [pull_eq T (X.tr_mul _ _ _ _ _ _ _ _ _ adm1.1 adm1.2) _ (X.tr_q _ _ _ _ _), ← X.pl_eq T adm1]
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (X.K j) ((c.out : G) * h⁻¹)
    rw [hu]
    have e2 : ((c.out : G) * h⁻¹ * u)⁻¹ = (u : G)⁻¹ * (h * (c.out : G)⁻¹) := by group
    rw [e2, X.pl_left T adm1 (inv_mem u.2)]
  have hc := count (R := R) (X.K j) (X.K i) h hil (fun y : G ⧸ X.K j => X.pl T m j (y.out)⁻¹ x)
  beta_reduce at hc
  rw [Finset.sum_congr rfl (fun c _ => hφ c), hc, LinearMap.smul_apply, map_smul, ← X.pl_eq T bm,
    hhop m hmj hadm x]
  simp [Nat.cast_smul_eq_nsmul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h
    apply hl
    apply (algebraMap k Ω).injective
    rw [map_natCast, h, map_zero]
  have h2 : IsUnit (l : Ω) := isUnit_iff_ne_zero.mpr h1
  have h3 := h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  simpa using h3

theorem UpperTheory.Gal.G3.pHopSpec :
    EtGood → BcGood.{1} → GalClos → OpEx.{1} → OpTr.{1} → OpEt → OpBc.{1} → BcSplits → HopSpec := by
  intro hEt hBc hClos hEx hTr hOpEt hOpBc hSpl l _ k _ hl H Ω _ _ g d hd
  obtain ⟨_, _, hcard⟩ := hd
  have gs : GalSplit (H.s g) := hClos (H.s g) d hcard
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hT : (et l (sp Ω)).Good := hEt l (sp Ω) (l_unit l hl Ω)
  have hT' : ((et l (sp Ω)).bc g₀).Good := hBc _ g₀ hT
  have hs : H.sΩ Ω g = bcMap g₀ (H.s g) rfl := rfl
  have ht : H.tΩ Ω g = bcMap g₀ (H.t g) (H.comm g) := rfl
  have hfe := hSpl g₀ H.q (H.s g ≫ H.q) H.q (H.s g) rfl (𝟙 _) (Category.id_comp _) PEmpty (fun j => j.elim) (fun j => j.elim)
  obtain ⟨_, _, -⟩ := hfe
  have hEq := hOpEt l (pullback.snd H.q g₀) (pullback.snd H.q g₀) (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g))
    ((bcMap_snd g₀ (H.t g) (H.comm g)).trans (bcMap_snd g₀ (H.s g) rfl).symm)
  have toCorr : ∀ A, ((et l (sp Ω)).bc g₀).IsOp H.q H.q (H.s g) (H.t g) A → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    intro A hA
    have h1 := hOpBc (et l (sp Ω)) g₀ H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) A hA
    exact (hEq A).1 h1
  have hex : ∃ A, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    obtain ⟨A, hA, -⟩ := (hEx _ hT' H.q H.q (H.s g) (H.t g) (H.comm g)).1 gs
    exact ⟨A, toCorr A hA⟩
  have hspec : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) := by
    unfold hop
    rw [dite_eq_left hex]
    exact hex.choose_spec
  refine ⟨hspec, fun tr htr => ?_⟩
  have hA := ((hTr _ hT' H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) tr htr) _).2 gs rfl
  have hcorr := toCorr _ hA
  obtain ⟨tr', htr'⟩ := hT.tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  have key := fun A => hTr _ hT (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (pullback.snd H.q g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) (bcMap_snd _ _ _) tr' htr' A
  have e1 := (key _).1 ((hEq _).2 hspec)
  have e2 := (key _).1 ((hEq _).2 hcorr)
  exact e1.trans e2.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3

private noncomputable def geomPt (X : Scheme.{0}) (x : X) : sp (AlgebraicClosure (X.residueField x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

private theorem geomPt_apply (X : Scheme.{0}) (x : X)
    (s : sp (AlgebraicClosure (X.residueField x))) : geomPt X x s = x := by
  exact Scheme.fromSpecResidueField_apply x _

private theorem surj_of_pts {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) : Surjective f := by
  constructor
  intro z
  obtain ⟨y, hy, -⟩ := h (AlgebraicClosure (Z.residueField z)) (geomPt Z z)
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure (Z.residueField z))) := ⟨IsLocalRing.closedPoint _⟩
  have key : (y ≫ f) s = geomPt Z z s := by rw [hy]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨y s, key⟩

private theorem diag_surj {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) :
    Surjective (pullback.diagonal f) := by
  constructor
  intro p
  obtain ⟨y, hy, huniq⟩ := h _ (geomPt (pullback f f) p ≫ pullback.fst f f ≫ f)
  have e1 : geomPt (pullback f f) p ≫ pullback.fst f f = geomPt (pullback f f) p ≫ pullback.snd f f := by
    rw [huniq (geomPt (pullback f f) p ≫ pullback.fst f f) (by dsimp only; rw [Category.assoc]),
      huniq (geomPt (pullback f f) p ≫ pullback.snd f f)
        (by dsimp only; rw [Category.assoc, pullback.condition])]
  have e2 : (geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f = geomPt (pullback f f) p := by
    apply pullback.hom_ext
    · simp
    · simp [e1]
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure ((pullback f f).residueField p))) :=
    ⟨IsLocalRing.closedPoint _⟩
  have key : ((geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f) s =
      geomPt (pullback f f) p s := by rw [e2]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨_, key⟩

theorem UpperTheory.Gal.G3.pIsoPts :
    IsoPts := by
  intro Y Z f _ h
  have hd : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, diag_surj f h⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).1 hd
  have : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨this, surj_of_pts f h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesGen
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fEt_comp_iso {Y X X' : Scheme.{0}} (f : Y ⟶ X) (i : X ⟶ X') [IsIso i] (d : ℕ) (hf : FEt f d) :
    FEt (f ≫ i) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  haveI := h1
  haveI := h2
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv i)]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun y => ?_
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [← Category.assoc, h]
    simp

theorem UpperTheory.Gal.G3.pLiesGen :
    LiesGen := by
  intro k L O _ _ _ _ H θ C g D s t hst m hL
  obtain ⟨-, κ0, h0, h1, hF⟩ := hL
  have hq : κ0 ≫ s ≫ C.p = (H.s g ≫ H.q) ≫ gen O k := by
    rw [← Category.assoc, ← h0, Category.assoc, C.ov, Category.assoc]
  let κ : H.Y g ⟶ pullback (s ≫ C.p) (gen O k) := pullback.lift κ0 (H.s g ≫ H.q) hq
  have hA : H.s g ≫ piK C = κ ≫ bcMap (gen O k) s rfl := by
    apply pullback.hom_ext
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact h0
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
  refine ⟨κ, hA, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact h1
    · simp only [piK, bcMap, κ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact (H.comm g).symm
  · have w1 : pullback.snd C.π s ≫ s ≫ C.p = (pullback.fst C.π s ≫ H.q) ≫ gen O k := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc, C.ov, Category.assoc]
    let i0 : pullback C.π s ⟶ pullback (s ≫ C.p) (gen O k) :=
      pullback.lift (pullback.snd C.π s) (pullback.fst C.π s ≫ H.q) w1
    have w2 : pullback.fst C.π s ≫ piK C = i0 ≫ bcMap (gen O k) s rfl := by
      apply pullback.hom_ext
      · simp only [piK, bcMap, i0, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact pullback.condition
      · simp only [piK, bcMap, i0, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    let i : pullback C.π s ⟶ pullback (piK C) (bcMap (gen O k) s rfl) :=
      pullback.lift (pullback.fst C.π s) i0 w2
    have c0 := pullback.condition (f := piK C) (g := bcMap (gen O k) s rfl)
    have c1 := congrArg (· ≫ pullback.fst C.p (gen O k)) c0
    have c2 := congrArg (· ≫ pullback.snd C.p (gen O k)) c0
    simp only [piK, bcMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc] at c1 c2
    have w3 : pullback.fst (piK C) (bcMap (gen O k) s rfl) ≫ C.π
        = (pullback.snd (piK C) (bcMap (gen O k) s rfl) ≫ pullback.fst (s ≫ C.p) (gen O k)) ≫ s := by
      rw [Category.assoc]
      exact c1
    let j : pullback (piK C) (bcMap (gen O k) s rfl) ⟶ pullback C.π s :=
      pullback.lift _ _ w3
    haveI : IsIso i := by
      refine ⟨⟨j, ?_, ?_⟩⟩
      · apply pullback.hom_ext
        · simp only [i, j, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      · apply pullback.hom_ext
        · simp only [i, j, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc]
        · apply pullback.hom_ext
          · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc]
          · simp only [i, j, i0, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd,
              pullback.lift_fst_assoc, pullback.lift_snd_assoc]
            exact c2
    have key : pullback.lift (H.s g) κ hA = pullback.lift (H.s g) κ0 h0 ≫ i := by
      apply pullback.hom_ext
      · simp only [i, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · apply pullback.hom_ext
        · simp only [i, i0, κ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
        · simp only [i, i0, κ, Category.assoc, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    rw [key]
    exact fEt_comp_iso _ i m hF
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultiSplit
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pMultiSplit :
    FEtBasic → SplitsBasic → GalClosD → MultiSplit := by
  intro hF hS hG Z n
  induction n with
  | zero =>
    intro Y s d _
    exact ⟨Z, 𝟙 Z, 1, one_pos, UpperTheory.Gal.Int.Geo.fEt_id Z, fun i => i.elim0⟩
  | succ n ih =>
    intro Y s d hs
    obtain ⟨W, c, e, he, hc, hspl⟩ := ih (fun i => Y i.castSucc) (fun i => s i.castSucc)
      (fun i => d i.castSucc) (fun i => hs i.castSucc)
    have hP : FEt (pullback.snd (s (Fin.last n)) c) (d (Fin.last n)) :=
      hF.1 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c _
        (IsPullback.of_hasPullback _ _) (hs _)
    obtain ⟨W2, c2, G, _, _, a, σ, hgal, hσ⟩ := hG (pullback.snd (s (Fin.last n)) c) _ hP
    have hc2 : FEt c2 (Nat.card G) := hF.2.2 c2 G a hgal
    refine ⟨W2, c2 ≫ c, e * Nat.card G, Nat.mul_pos he Nat.card_pos,
      hF.2.1 c2 c e (Nat.card G) hc2 hc, ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_)
    · haveI := (hs (Fin.last n)).1
      haveI := (hs (Fin.last n)).2.1
      exact ⟨fun j => σ j ≫ pullback.fst _ _,
        (hS.2 (pullback.fst _ _) (pullback.snd _ _) (s (Fin.last n)) c
          (IsPullback.of_hasPullback _ _) c2 (Fin (d (Fin.last n))) σ hσ.1).mp hσ⟩
    · obtain ⟨τ, hτ⟩ := hspl i
      haveI := (hs i.castSucc).1
      haveI := (hs i.castSucc).2.1
      exact ⟨fun j => c2 ≫ τ j, hS.1 (s i.castSucc) c _ τ c2 hτ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEt :
    OpEt := by
  intro l _ B Z Y Z' p p' s t hst A
  constructor
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, _hh, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ,
      fun j => by rw [Category.assoc, hst, ← Category.assoc, hrest.2.1.1 j], hrest⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEx :
    OpTr.{u} → OpEx.{u} := by
  intro hTr B R _ T hG Z Y Z' p p' s _ _ t hcomm
  obtain ⟨tr, htr⟩ := hG.tr p (s ≫ p) s rfl
  have key := fun A => hTr T hG p (s ≫ p) p' s t rfl hcomm tr htr A
  refine ⟨fun hgs => ⟨tr ∘ₗ T.pull t hcomm, (key _).2 hgs rfl, fun A hA => (key A).1 hA⟩, ?_⟩
  intro A hA W r c hc J _ σ h hsp x
  have hσ : ∀ j, σ j ≫ (s ≫ p) = r := by
    intro j
    rw [← hcomm, ← Category.assoc]
    exact h j
  rw [(key A).1 hA, LinearMap.comp_apply, htr W r c hc J σ hσ hsp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [T.pull_comp (σ j) t (hσ j) hcomm]
end

