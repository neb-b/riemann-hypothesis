module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0019
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  intro R _ _ T _ _ Γ
  let A := Γ.btOrder ⊤
  have htop (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
      valAt (Γ.pt t).left ⊤ h s = val (Γ.pt t).left s := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hsec (a : A) : ∃ s : Γ(Γ.G.left, ⊤), ∀ t,
      val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t) := by
    have ha := (Twhopf.mem_order R T Γ ⊤ a.1).1 a.2
    obtain ⟨s, hs⟩ := (Twhopf.reg_iff R T Γ ⊤ _).1 (ha 1)
    refine ⟨s, fun t => (htop t le_top s).symm.trans ?_⟩
    simpa only [_root_.one_mul] using hs t le_top
  have hsec_ext {s s' : Γ(Γ.G.left, ⊤)}
      (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') : s = s' := by
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [htop, map_sub, h, sub_self]
  have hhom_ext {B : Type} [CommRing B] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of B)}
      (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
    pb_ext fun a => hsec_ext fun t => by rw [val_pb_comp, h, ← val_pb_comp]
  choose s hs using hsec
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := hsec_ext fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => hsec_ext fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := hsec_ext fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => hsec_ext fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hhom_ext fun t => by rw [hj'.pt, hpt]⟩
  apply hhom_ext
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

theorem emb_square : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (A : Subalgebra R (T → R)) (A' : Subalgebra R' (T → R')) (ψ : A →+* A'), (∀ (a : A) t, (ψ a).1 t = algebraMap R R' (a.1 t)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of A')), Γ.IsEmb A j → Γ'.IsEmb A' j' → F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF A A' ψ hψ j j' hj hj'
  obtain ⟨B, _, i, k, k', σ, hk, hki, hki', -, hσ, hσ'⟩ := hF.pts
  have hhom_ext {f g : Γ'.G.left ⟶ Spec (CommRingCat.of A)}
      (h : ∀ t, (Γ'.pt t).left ≫ f = (Γ'.pt t).left ≫ g) : f = g := by
    apply pb_ext
    intro a
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R' T Γ' ⊤ _ fun t ht => ?_
    unfold valAt
    change val (Γ'.pt t).left (pb f a - pb g a) = 0
    rw [map_sub, val_pb_comp, h, ← val_pb_comp, sub_self]
  refine hhom_ext fun t => ?_
  have h1 : σ t ≫ j = Spec.map (CommRingCat.ofHom
      (i.comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (σ t ≫ j)
    have h2 := hj.pt t
    rw [← hσ t, Category.assoc, ← hc, ← CommRingCat.ofHom_hom c, spec_comp, ← hki] at h2
    rw [← hc, ← CommRingCat.ofHom_hom c]
    congr 2
    exact RingHom.ext fun a => hk (RingHom.congr_fun (spec_inj h2) a)
  rw [← Category.assoc, ← hσ', Category.assoc, h1, spec_comp, ← Category.assoc, hj'.pt t, spec_comp,
    ← RingHom.comp_assoc, hki']
  congr 2
  exact RingHom.ext fun a => congrArg (algebraMap R' (FractionRing R')) (hψ a t).symm

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem exists_den_of_open {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A))
    [IsOpenImmersion j] (g : X) (s : Γ(X, ⊤)) :
    ∃ u a : A, u ∉ (j g).asIdeal ∧ ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X),
      val x (pb j u) * val x s = val x (pb j a) := by
  have htop {K : Type} [CommRing K] {Y : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ Y)
      (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (b : Γ(Y, ⊤)) : valAt x ⊤ h b = val x b := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hY := isAffineOpen_top (Spec (CommRingCat.of A))
  obtain ⟨r, hr, hg⟩ := hY.exists_basicOpen_le (V := j.opensRange) ⟨j g, g, rfl⟩ trivial
  let D := (Spec (CommRingCat.of A)).basicOpen r
  have := j.isIso_app D hr
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso (j.app D)).2
    ((X.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)).op).hom s)
  have hl := hY.isLocalization_basicOpen r
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) s'
  let c := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
  have hc : ∀ b, pb j (c b) = j.appTop b := fun b => by simp [pb, c]
  refine ⟨c (r ^ (n + 1)), c (r * a), ?_, fun K _ x => ?_⟩
  · rw [map_pow]
    intro h
    have h1 := (j g).isPrime.mem_of_pow_mem _ h
    have h2 : j g ∈ (Spec (CommRingCat.of A)).basicOpen r := hg
    rw [basicOpen_eq_of_affine'] at h2
    exact h2 h1
  · rw [hc, hc, ← val_comp, ← val_comp, map_pow, map_mul, pow_succ']
    by_cases h0 : val (x ≫ j) r = 0
    · simp [h0]
    have hx : ⊤ ≤ (x ≫ j) ⁻¹ᵁ D := by
      rw [Scheme.preimage_basicOpen_top, top_le_iff]
      apply Scheme.basicOpen_of_isUnit
      have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((x ≫ j).appTop r)) := Ne.isUnit h0
      simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have e := congrArg (SubOrder.valHom (x ≫ j) D hx) ha
    have hres : ∀ b, SubOrder.valHom (x ≫ j) D hx (algebraMap Γ(Spec (CommRingCat.of A), ⊤) _ b) = val (x ≫ j) b :=
      fun b => (Twhopf.valAt_restrict (x ≫ j) (homOfLE (le_top : D ≤ ⊤)) hx le_top b).trans (htop _ _ _)
    rw [map_mul, hres, hres, SubOrder.valHom_apply, valAt_comp] at e
    have e2 : valAt x (j ⁻¹ᵁ D) hx ((j.app D).hom s') = val x s :=
      (congrArg (valAt x (j ⁻¹ᵁ D) hx) hs').trans
        ((Twhopf.valAt_restrict x (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)) hx le_top s).trans (htop _ _ _))
    rw [e2, map_pow] at e
    rw [← e]
    ring

theorem char : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A := by
  intro R _ _ T _ _ Γ A hA j hj hopen hcov
  have htop (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
      valAt (Γ.pt t).left ⊤ h s = val (Γ.pt t).left s := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hmem (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
      ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h,
        val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
    rw [Twhopf.mem_order]
    change (∀ t, ∀ g ∈ (⊤ : Γ.G.left.Opens), Γ.RegularAt
      (fun h => algebraMap R (FractionRing R) (f (t * h))) g) ↔ _
    simp only [Twhopf.reg_iff, htop]
    simp
  have hval (t : T) (a : A) :
      val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
    val_pb (hj.pt t) a
  have tr := Twhopf.translate_mem R T A hA
  apply le_antisymm
  · intro f hf
    rw [hmem] at hf
    let I : Ideal A :=
      { carrier := {a | a.1 * f ∈ A}
        add_mem' := fun {a b} ha hb => by
          change (a.1 + b.1) * f ∈ A
          rw [add_mul]
          exact A.add_mem ha hb
        zero_mem' := by
          change (0 : T → R) * f ∈ A
          rw [zero_mul]
          exact A.zero_mem
        smul_mem' := fun c a ha => by
          change (c.1 * a.1) * f ∈ A
          rw [_root_.mul_assoc]
          exact A.mul_mem c.2 ha }
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
      obtain ⟨t, g, -, hg⟩ := hcov ⟨P, hP.isPrime⟩
      obtain ⟨s, hs⟩ := hf t
      obtain ⟨u, a, hu, hua⟩ := exists_den_of_open j g s
      have h1 : ∀ h, u.1 h * f (t * h) = a.1 h := fun h => by
        have := hua _ (Γ.pt h).left
        rw [hval, hval, hs, ← map_mul] at this
        exact IsFractionRing.injective R (FractionRing R) this
      let u' : A := ⟨_, tr _ u.2 t⁻¹⟩
      refine hu ((hg u' u fun h => by simp [u']).1 (hIP ?_))
      change u'.1 * f ∈ A
      convert tr _ a.2 t⁻¹ using 1
      funext h
      rw [← h1]
      simp [u']
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : T → R) * f ∈ A := h1
    rwa [_root_.one_mul] at h2
  · intro f hf
    rw [hmem]
    exact fun t => ⟨pb j ⟨_, tr f hf t⟩, fun h => hval h _⟩

end PositivityTheory.HtPt.Mh
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpB
section
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

theorem mem_of_forall_dvd {O A : Type} [CommRing O] [IsDomain O] [ValuationRing O] [AddCommGroup A]
    [Module O A] [Module.IsTorsionFree O A] (N : Submodule O A) (hN : N.FG) {q : O} (hq : q ≠ 0)
    (hqN : ∀ a, q • a ∈ N) (x : A)
    (h : ∀ φ : A →ₗ[O] O, (∀ y ∈ N, q ∣ φ y) → q ∣ φ x) : x ∈ N := by
  classical
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  haveI : Module.Flat O N := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O N
  let ψ : A →ₗ[O] N := LinearMap.codRestrict N (q • LinearMap.id) (fun a => hqN a)
  have hψ : ∀ a, (ψ a : A) = q • a := fun a => rfl
  have key : ∀ i, q ∣ b.coord i (ψ x) := by
    intro i
    apply h ((b.coord i).comp ψ)
    intro y hy
    have hy' : ψ y = q • (⟨y, hy⟩ : N) := Subtype.ext (hψ y)
    rw [LinearMap.comp_apply, hy', map_smul, smul_eq_mul]
    exact dvd_mul_right _ _
  choose d hd using key
  let z : N := ∑ i, d i • b i
  have hz : ψ x = q • z := by
    apply b.ext_elem
    intro i
    have := hd i
    simp only [Module.Basis.coord_apply] at this
    simp [z, this, Finset.smul_sum, smul_smul, Finsupp.single_apply]
  have hxz : x = (z : A) := by
    have h1 : q • x = q • (z : A) := by
      rw [← hψ, hz]; rfl
    exact Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hq) h1
  rw [hxz]
  exact z.2

variable {p : ℕ} {O : Type} [CommRing O]

theorem dUnit_mulBy {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ) (a : A) :
    dUnit (R := O) (mulBy O A k a) = (k : O) • dUnit (R := O) a := by
  rw [← cotMap_d]
  show cotMap ((toConv (BialgHom.id O A) ^ k).ofConv) (dUnit (R := O) a) = _
  rw [cotMap_pow, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  simp [cotMap_id]

theorem dUnit_of_mem_torsionIdeal {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ)
    {t : A} (ht : t ∈ torsionIdeal (R := O) (A := A) k) : ∃ y, dUnit (R := O) t = (k : O) • y := by
  suffices H : counitAlgHom O A t = 0 ∧ ∃ y, dUnit (R := O) t = (k : O) • y from H.2
  change t ∈ Ideal.span _ at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit (R := O) a, dUnit_mulBy k a⟩
    have ha' : counitAlgHom O A a = 0 := ha
    simpa using ha'
  | zero => exact ⟨by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx0, u, hu⟩ := hx
    obtain ⟨hy0, v, hv⟩ := hy
    exact ⟨by rw [map_add (f := _), hx0, hy0, add_zero], u + v, by simp [hu, hv, smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨hx0, u, hu⟩ := hx
    refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], counitAlgHom O A c • u, ?_⟩
    show AugCot.d _ (c * x) = _
    rw [AugCot.d_mul, hx0, zero_smul, add_zero]
    change _ • dUnit (R := O) x = _
    rw [hu, smul_comm]

theorem exists_of_cotMap_res_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A (n + 1)))
    (hy : cotMap (G.res n) y = 0) : ∃ y', y = (p : O) ^ n • y' := by
  unfold cotMap at hy
  obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map _ _ (G.res_surjective n) y).1 hy
  have hx' : dUnit (R := O) (x : G.A (n + 1)) = y := by
    rw [← hx]
    exact (AugCot.kerMap_apply _ _ x).symm
  have hxmem : (x : G.A (n + 1)) ∈ torsionIdeal (R := O) (A := G.A (n + 1)) (p ^ n) := by
    rw [← G.ker_res n]
    exact x.2
  obtain ⟨y', hy'⟩ := dUnit_of_mem_torsionIdeal (p ^ n) hxmem
  refine ⟨y', ?_⟩
  rw [← hx', ← Nat.cast_pow]
  exact hy'

def lev (G : PDivGroup p O) (n : ℕ) : G.omega →ₗ[O] Cot O (G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype

theorem lev_apply (G : PDivGroup p O) (n : ℕ) (w : G.omega) : lev G n w = w.1 n := rfl

private theorem prime_pow_smul_cot_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A n)) :
    (p : O) ^ n • y = 0 := by
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ y
  obtain ⟨a, rfl⟩ := G.res_surjective n b
  set r := counitAlgHom O (G.A (n + 1)) a
  have hmem : mulBy O (G.A (n + 1)) (p ^ n) (a - algebraMap O _ r) ∈ RingHom.ker (G.res n) := by
    rw [G.ker_res n]
    apply Ideal.mem_map_of_mem
    show a - algebraMap O _ r ∈ RingHom.ker (counitAlgHom O (G.A (n + 1)))
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp [r]
  have h2 : G.res n (mulBy O _ (p ^ n) a) = algebraMap O _ r := by
    rw [RingHom.mem_ker] at hmem
    have := hmem
    simp only [map_sub, AlgHomClass.commutes, sub_eq_zero] at this
    exact this
  rw [← Nat.cast_pow]
  change ((p ^ n : ℕ) : O) • dUnit (R := O) (G.res n a) = 0
  rw [← dUnit_mulBy, ← map_mulBy, h2]
  exact AugCot.d_algebraMap _ _

theorem smul_mem_of_levels [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O)
    (L : Submodule O G.omega) (hL : L.FG) (κ : O)
    (hκ : ∀ n (y : Cot O (G.A n)), κ • y ∈ L.map (lev G n))
    (hp : ∀ n (y : Cot O (G.A n)), (p : O) • y ∈ L.map (lev G n)) (w : G.omega) : κ • w ∈ L := by
  classical
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let g : (Fin m → O) →ₗ[O] G.omega := Fintype.linearCombination O s
  have hg : LinearMap.range g = L := by rw [Fintype.range_linearCombination, hs]
  let Φ : (k : ℕ) → (Fin m → O) →ₗ[O] Cot O (G.A k) := fun k => (lev G k).comp g
  have compat : ∀ k (v : G.omega), cotMap (G.res k) (lev G (k + 1) v) = lev G k v := by
    intro k v
    rw [lev_apply, lev_apply]
    exact v.2 k
  have compatΦ : ∀ k c, cotMap (G.res k) (Φ (k + 1) c) = Φ k c := fun k c => compat k (g c)
  have lift : ∀ k (y : Cot O (G.A k)), y ∈ L.map (lev G k) → ∃ c, Φ k c = y := by
    intro k y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg] at hv
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, rfl⟩
  let W : (k : ℕ) → Cot O (G.A k) := fun k => lev G k w
  have hWc : ∀ k, cotMap (G.res k) (κ • W (k + 1)) = κ • W k := by
    intro k
    rw [map_smul, compat]
  have step : ∀ n (c : {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}),
      ∃ c' : {c : Fin m → O // Φ (n + 2) c = κ • W (n + 2)},
        ∃ f : Fin m → O, c'.1 = c.1 + (p : O) ^ n • f := by
    intro n c
    obtain ⟨d, hd⟩ := lift (n + 2) _ (hκ (n + 2) (W (n + 2)))
    have hd1 : Φ (n + 1) d = κ • W (n + 1) := by
      rw [← compatΦ, hd, hWc]
    have he : cotMap (G.res (n + 1)) (Φ (n + 2) (d - c.1)) = 0 := by
      rw [compatΦ, map_sub, hd1, c.2, sub_self]
    obtain ⟨y', hy'⟩ := exists_of_cotMap_res_eq_zero G (n + 1) _ he
    obtain ⟨f, hf⟩ := lift (n + 2) _ (hp (n + 2) y')
    refine ⟨⟨c.1 + (p : O) ^ n • f, ?_⟩, f, rfl⟩
    have key : Φ (n + 2) (d - c.1) = Φ (n + 2) ((p : O) ^ n • f) := by
      rw [hy', map_smul, hf, smul_smul, ← pow_succ]
    have : c.1 + (p : O) ^ n • f = d - (d - c.1) + (p : O) ^ n • f := by abel
    rw [this, map_add (f := _), map_sub, key, hd]
    abel
  choose nxt hnxt using step
  obtain ⟨c0, hc0⟩ := lift 1 _ (hκ 1 (W 1))
  let seq : (n : ℕ) → {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)} :=
    fun n => @Nat.rec (fun n => {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}) ⟨c0, hc0⟩
      (fun k ck => nxt k ck) n
  have seq_succ : ∀ n, seq (n + 1) = nxt n (seq n) := fun n => rfl
  have diff : ∀ a b, a ≤ b → ∃ t : Fin m → O, (seq b).1 = (seq a).1 + (p : O) ^ a • t := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ b hab ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨f, hf⟩ := hnxt b (seq b)
      refine ⟨t + (p : O) ^ (b - a) • f, ?_⟩
      rw [seq_succ, hf, ht, smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hab, add_assoc]
  have hpre : ∀ j, ∃ l : O, ∀ n, (seq n).1 j ≡ l [SMOD ((Ideal.span {(p : O)}) ^ n • ⊤ : Submodule O O)] := by
    intro j
    apply IsPrecomplete.prec inferInstance
    intro a b hab
    obtain ⟨t, ht⟩ := diff a b hab
    rw [SModEq.sub_mem, ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_cancel_left, Ideal.mul_top]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) a))
  choose l hl using hpre
  have close : ∀ N, ∃ t : Fin m → O, l = (seq N).1 + (p : O) ^ N • t := by
    intro N
    have : ∀ j, ∃ a : O, a * (p : O) ^ N = l j - (seq N).1 j := by
      intro j
      have h1 := (SModEq.sub_mem.1 (hl j N).symm)
      simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h1
      exact Ideal.mem_span_singleton'.1 h1
    choose t ht using this
    refine ⟨t, funext fun j => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ht]
    ring
  have good : ∀ n, Φ (n + 1) l = κ • W (n + 1) := by
    intro n
    obtain ⟨t, ht⟩ := close (n + 1)
    have h1 : Φ (n + 1) (seq (n + 1)).1 = κ • W (n + 1) := by
      rw [← compatΦ, (seq (n + 1)).2, hWc]
    rw [ht, map_add (f := _), h1, map_smul, prime_pow_smul_cot_eq_zero, add_zero]
  have good' : ∀ n, Φ n l = κ • W n := by
    intro n
    cases n with
    | zero => rw [← compatΦ, good 0, hWc]
    | succ n => exact good n
  have hgl : g l = κ • w := by
    apply Subtype.ext
    funext k
    have := good' k
    simp only [Φ, W, LinearMap.comp_apply, lev_apply] at this
    rw [this]
    rfl
  rw [← hg, ← hgl]
  exact LinearMap.mem_range_self g l

end PositivityTheory.HtPt.Farsharp
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentreUnique
section
noncomputable section

namespace PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  show IsLocalRing (genMap ξ p).range
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ)
    (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have e : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have ha : (a : Ω) ≠ 0 := fun h0 => by simp [h0] at e
    refine ⟨ha, a.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right e]
    exact b.2
  · rintro ⟨h0, -, h2⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem unitAt_iff_of_dominated {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'} {q : Cpt ξ}
    (h : (∀ a ∈ regAt ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ q, unitAt ξ' p' (i a) → unitAt ξ q a)
    {a : Ω} (ha : a ∈ regAt ξ q) : unitAt ξ q a ↔ unitAt ξ' p' (i a) := by
  refine ⟨fun hu => ⟨(map_ne_zero i).2 hu.1, h.1 a hu.2.1, ?_⟩, h.2 a ha⟩
  rw [← map_inv₀]
  exact h.1 _ hu.2.2

theorem eq_of_dominated_of_inChart {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    {i : Ω →+* Ω'} {p' : Cpt ξ'} {c : κ} {q r : Cpt M.ξ} (hq : InChart M.ξ x c q) (hr : InChart M.ξ x c r)
    (dq : (∀ a ∈ regAt M.ξ q, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q, unitAt ξ' p' (i a) → unitAt M.ξ q a)
    (dr : (∀ a ∈ regAt M.ξ r, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ r, unitAt ξ' p' (i a) → unitAt M.ξ r a) :
    q = r := by
  have cq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).1
  have cr := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c r hr).1
  haveI := isLocalRing_regAt M.ξ q
  let f : chRing o x c →+* regAt M.ξ q :=
    ((chRing o x c).val : chRing o x c →+* Ω).codRestrict (regAt M.ξ q) fun u => cq _ u.2
  have hP : ∀ u : chRing o x c, u ∈ (IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f ↔ ¬ unitAt M.ξ q (u : Ω) := by
    intro u
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
    rfl
  obtain ⟨p, -, huniq⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω κ x M c hq.1 _
    (inferInstance : ((IsLocalRing.maximalIdeal (regAt M.ξ q)).comap f).IsPrime)
  have e1 := huniq q ⟨hq, hP⟩
  have e2 := huniq r ⟨hr, fun u => by
    rw [hP, unitAt_iff_of_dominated dq (cq _ u.2), unitAt_iff_of_dominated dr (cr _ u.2)]⟩
  exact e1.trans e2.symm

theorem eq_of_dominated : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' q₁ q₂ d₁ d₂
  obtain ⟨c₁, hc₁⟩ := M.tie.cover q₁
  obtain ⟨c₂, hc₂⟩ := M.tie.cover q₂
  have hctr : p' ∈ ctrSet o x i ξ' :=
    ⟨c₁, hc₁.1, fun a ha => d₁.1 a ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ q₁ hc₁).1 a ha)⟩
  obtain ⟨p₀, d₀, -, hp₀⟩ := PositivityTheory.HtPt.Mb.centre o Ω κ x M X' Ω' ξ' i p' hctr
  have e₁ : q₁ = p₀ := eq_of_dominated_of_inChart M hc₁ (hp₀ c₁ hc₁.1 fun j => d₁.1 _ (hc₁.2 j)) d₁ d₀
  have e₂ : q₂ = p₀ := eq_of_dominated_of_inChart M hc₂ (hp₀ c₂ hc₂.1 fun j => d₂.1 _ (hc₂.2 j)) d₂ d₀
  exact e₁.trans e₂.symm

end PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.centre_unique : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ') (q₁ q₂ : Cpt M.ξ), ((∀ a ∈ regAt M.ξ q₁, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₁, unitAt ξ' p' (i a) → unitAt M.ξ q₁ a) → ((∀ a ∈ regAt M.ξ q₂, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ q₂, unitAt ξ' p' (i a) → unitAt M.ξ q₂ a) → q₁ = q₂ :=
  @PositivityTheory.HtPt.Mb.LCentreUnique.Centre.Sep.eq_of_dominated
end
end

