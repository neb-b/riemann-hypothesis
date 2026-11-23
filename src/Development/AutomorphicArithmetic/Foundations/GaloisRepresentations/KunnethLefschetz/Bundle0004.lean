module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Development.EtaleCohomology.EtaleTrace.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DivLHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc {l : ℕ} [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem powV_pull {l : ℕ} [Fact l.Prime] (R : Ring l) {Y X : Scheme.{0}} (f : Y ⟶ X) (hu : IsUnit (l : Γ(X, ⊤)))
    (x : V l X 2) (j : ℕ) : pb l f _ (powV l x j) = powV l (pb l f 2 x) j := by
  induction j with
  | zero => exact R.one_nat f hu
  | succ j ih =>
    change pb l f _ (cupV l X _ (powV l x j) x) = cupV l Y _ (powV l (pb l f 2 x) j) (pb l f 2 x)
    rw [R.nat, ih]

private theorem pull_onto {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (hu : IsUnit (l : Γ(W, ⊤))) (e : V l W 2) (hP : PBQ l (i ≫ s) (pb l i 2 e)) (n : ℤ) (b : V l E n) :
    ∃ m, pb l i n m = b := by
  have hle : (⊤ : Submodule ℚ_[l] (V l E n)) ≤ LinearMap.range (pb l i n) := by
    rw [← hP.span n, Submodule.span_le]
    rintro z ⟨j, a, h, u, rfl⟩
    refine ⟨cupV l W h (pb l s a u) (powV l e j), ?_⟩
    rw [R.nat, pbc, powV_pull R i hu]
  exact hle (Submodule.mem_top (x := b))

private theorem unit_eq {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (uX : IsUnit (l : Γ(X, ⊤))) (uE : IsUnit (l : Γ(E, ⊤))) (e ε : V l W 2) (u0 a v : _)
    (he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε)
    (hP : PBQ l (i ≫ s) (pb l i 2 e))
    (hav : pb l i 2 ε = pb l (i ≫ s) 2 a + cupV l E (zero_add 2) (pb l (i ≫ s) 0 v) (pb l i 2 e)) :
    cupV l X (add_zero 0) v u0 = oneV l X := by
  set ξ := pb l i 2 e with hξdef
  have h0 : ξ = cupV l E (zero_add 2) (pb l (i ≫ s) 0 u0) (pb l i 2 ε) := by
    rw [hξdef, he, R.nat, pbc]
  have h1 : ξ = pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v)) ξ := by
    conv_lhs => rw [h0, hav]
    rw [map_add (f := _), ← R.nat,
      ← R.assoc E 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat]
  have h2 : cupV l E (zero_add 2) (pb l (i ≫ s) 0 (oneV l X)) ξ = ξ := by
    rw [R.one_nat _ uX, R.one_mul E uE]
  have h3 : pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v - oneV l X)) ξ = 0 := by
    rw [map_sub, map_sub, LinearMap.sub_apply, h2, ← add_sub_assoc, ← h1, sub_self]
  have h4 := hP.indep _ _ h3
  rw [sub_eq_zero] at h4
  rw [R.comm X 0 0 0 (add_zero 0) (add_zero 0) v u0, h4]
  simp

theorem divL_holds : DivL := by
  intro l _ k _ _ hl R G W E X px i s c hpair hprop U hoff e he0 hP n w h z hz
  have hk : IsUnit (l : k) := isUnit_iff_ne_zero.2 hl
  have uX := LPdCut.unit_of px hk
  have uW := LPdCut.unit_of (s ≫ px) hk
  have uE := LPdCut.unit_of (i ≫ s ≫ px) hk
  have h02 : (0 : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 := by norm_num
  have hnw : n + 2 * ((1 : ℕ) : ℤ) = w := by push_cast; omega
  have hn2 : n + 2 = w := by omega
  obtain ⟨ε, hε⟩ : ∃ ε, G.g hpair h02 (oneV l E) = ε := ⟨_, rfl⟩
  obtain ⟨ε0, hε0⟩ := G.onto hpair h02 U hoff hprop e he0
  obtain ⟨u0, rfl⟩ := hP.zero ε0
  have he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε := by
    rw [← hε, ← G.proj hpair (add_zero 0) h02 h02 (zero_add 2), R.mul_one E uE, ← pbc, hε0]
  obtain ⟨a, v, hav⟩ := hP.two (pb l i 2 ε)
  have hunit := unit_eq R i s uX uE e ε u0 a v he hP hav
  have hε' : cupV l W (add_zero 2) e (pb l s 0 v) = ε := by
    rw [R.comm W 2 0 2 (add_zero 2) (zero_add 2), he,
      ← R.assoc W 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat, hunit,
      R.one_nat _ uX, R.one_mul W uW]
    simp
  obtain ⟨b, hb⟩ := G.onto hpair hnw U hoff hprop z hz
  obtain ⟨m', rfl⟩ := pull_onto R i s uW e hP n b
  have hz' : z = cupV l W hn2 m' ε := by
    rw [← hb, ← hε, ← G.proj hpair (add_zero n) hnw h02 hn2, R.mul_one E uE]
  refine ⟨cupV l W (zero_add n) (pb l s 0 v) m', ?_⟩
  rw [hz', ← R.assoc W 2 0 n 2 n w (add_zero 2) h (zero_add n) h, hε',
    R.comm W n 2 w hn2 h, Int.negOnePow_even _ ⟨n, by ring⟩, one_smul]

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.IntOne
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

structure Steps : Prop where
  offEx : OffEx
  pairs : Pairs
  pn : PnFacts
  hyp : HypEmb
  cov : FinCov
  fib : FinFib
  comps : Comps
  ring : RingL
  lowT : LowTL
  ptVan : PtVanT
  low : LowL
  tower : TowerL
  aff : AffVan
  twBij : TwBij
  gysT : GysTL
  gys0 : GysinCondition
  qEasy : QEasy
  lim : LimOnto
  qOnto : QOnto
  qProj : QProj
  kunBij : KunBij
  kun : KunL
  swap : Swap
  slice : Slice
  ptInt : PtInt
  detect : DetectL
  dual : DualL
  supp : FinSupp
  cls : PnCls
  inj : InjL
  trComp : TrComp
  div : DivL
  basis : BasisOne
  top : TopPart

namespace Steps
variable (H : Steps) (hI : In) (hT : TrIn) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0)
include H hI hl

theorem low' : Low l k := H.low hI H.ptVan l k hl (H.ring hI l) (H.lowT hI l k hl)

theorem gysQ : Nonempty (GysQ k l) := by
  obtain ⟨G⟩ := H.gys0 hI H.twBij l k hl (H.tower hI l k hl) (H.gysT hI H.offEx k)
  obtain ⟨h1, h2, h3⟩ := H.qEasy l k G
  exact ⟨⟨fun h _ _ hn => G.q h hn, h1, H.qOnto hI H.lim l k hl G, h2, h3, H.qProj hI l k G⟩⟩

theorem kun' (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) : Kun l k d p :=
  H.kun l k d p (H.kunBij hI l k hl (H.ring hI l) d p hp)

theorem int_pt (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0) (hΛ : IsInt l p lam (add_zero _) Λ) (y : Pt p) :
    pb l y.1 0 (Λ (G.diag d p)) = lam (G.pt d y) • oneV l (S k) := by
  rw [H.ptInt l k hl d p hp (H.ring hI l) (H.low' hI l k hl) (H.kun' hI l k hl d p hp) lam Λ hΛ y,
    H.slice H.pairs l k hl d p hp (H.ring hI l) G y]

theorem int_one (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) (Λ : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0)
    (hΛ : IsInt l p lam (add_zero _) Λ) : Λ (G.diag d p) = oneV l X := by
  rw [← sub_eq_zero]
  refine (H.low' hI l k hl).pts p hp.1 _ fun y => ?_
  rw [map_sub, H.int_pt hI l k hl G d p hp lam Λ hΛ y, h1, one_smul,
    (H.ring hI l).one_nat y.1 (LPdCut.unit_of p (isUnit_iff_ne_zero.2 hl)), sub_self]

include hT

theorem pt_ne (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ y : Pt p, G.pt d y ≠ 0 := by
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have := hp.1
  obtain ⟨t, U, z, hU, hz, hzU⟩ := H.cls hI H.pn H.hyp H.offEx l k hl hR hL (fun j d n hn => by
    have : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact H.aff hI H.ptVan k (l ^ j) (by rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hl).pow _) d n 0 hn) ⟨G⟩ d
  obtain ⟨π, hπ, hf, hs⟩ := H.cov k d p hp hP hX
  obtain ⟨s, hs'⟩ := H.fib k p _ π hπ hf t U hU
  have hinj := H.inj hT l π hf hs (H.pn k d).2.1 (H.pn k d).2.2.1
    (LPdCut.unit_of (PNto k d) (isUnit_iff_ne_zero.2 hl)) (2 * d)
  have h0 : pb l (π ⁻¹ᵁ U).ι _ (pb l π (2 * d) z) = 0 := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply, hzU, map_zero]
  have hm := H.supp H.offEx H.pairs l k hl hR hL G d p inferInstance hp.2 s _ hs' _ h0
  by_contra hc
  have hc' : ∀ y : Pt p, G.pt d y = 0 := fun y => by_contra fun h => hc ⟨y, h⟩
  rw [Submodule.span_eq_bot.2 (by rintro _ ⟨y, rfl⟩; exact hc' y), Submodule.mem_bot] at hm
  exact hz (hinj (hm.trans (map_zero _).symm))

theorem tr_int (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hP : IsProj p) (hX : IsIntegral X) :
    ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam ≠ 0 ∧ ∀ y : Pt p, lam (G.pt d y) = 1 := by
  have hL := H.low' hI l k hl
  obtain ⟨y, hy⟩ := H.pt_ne hI hT l k hl G d p hp hP hX
  obtain ⟨lam, hlam⟩ : ∃ lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l], lam (G.pt d y) = 1 := by
    obtain ⟨f, hf⟩ := not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff ℚ_[l] _).1 hy)
    exact ⟨(f (G.pt d y))⁻¹ • f, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]⟩
  refine ⟨lam, fun h => by simp [h] at hlam, fun y' => ?_⟩
  obtain ⟨Λ, hΛ⟩ := (H.kun' hI l k hl d p hp).int lam 0 (2 * d) (add_zero _)
  have h := hL.conn p hp.1 inferInstance (Λ (G.diag d p)) y y'
  rw [H.int_pt hI l k hl G d p hp lam Λ hΛ, H.int_pt hI l k hl G d p hp lam Λ hΛ, hlam] at h
  exact ((hL.line _).unique h rfl)

theorem detect' (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l])
    (h1 : ∀ y : Pt p, lam (G.pt d y) = 1) : Detect l d X lam :=
  H.detect l k hl d p hp (H.ring hI l) (H.kun' hI l k hl d p hp) lam (G.diag d p)
    (H.swap H.pairs l k hl d p hp (H.ring hI l) G) (H.int_one hI l k hl G d p hp lam h1)

omit hl [IsAlgClosed k] in
theorem qDual : QDual := by
  intro l _ k _ _ hl d X p hp hP hX
  obtain ⟨G⟩ := H.gysQ hI l k hl
  obtain ⟨lam, h0, h1⟩ := H.tr_int hI hT l k hl G d p hp hP hX
  exact H.dual l k hl d p hp hX (H.ring hI l) (H.low' hI l k hl) lam (H.detect' hI hT l k hl G d p hp lam h1) h0

end Steps

theorem Detect.finite {l : ℕ} [Fact l.Prime] {d : ℕ} {X : Scheme.{0}} {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]}
    (h : Detect l d X lam) (n : ℤ) : FiniteDimensional ℚ_[l] (V l X n) := by
  classical
  obtain ⟨s, c, a, h⟩ := h
  refine FiniteDimensional.of_injective (LinearMap.pi fun t : Fin s =>
    if hn : n + c t = 2 * d then lam ∘ₗ (cupV l X hn).flip (a t) else 0) ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
  refine h n x fun t hn => ?_
  have := congrFun hx t
  simpa [dif_pos hn] using this

theorem Steps.qDiag (H : Steps) (hI : In) (hT : TrIn) : QDiag := by
  intro l _ k _ _ hl d X p hp hP W E π i r c hpb hi hr U hU e he hPB
  obtain ⟨G⟩ := H.gysQ hI l k hl
  have hR := H.ring hI l
  have hL := H.low' hI l k hl
  have hK := H.kun' hI l k hl _ p hp
  have := hp.1
  obtain ⟨lam, h1⟩ := H.trComp H.comps H.offEx H.pairs l k hl hR G (d + 1) (fun p hp hP hX => by
    obtain ⟨lam, -, h⟩ := H.tr_int hI hT l k hl G _ p hp hP hX
    exact ⟨lam, h⟩) p hp hP
  have hD := H.detect' hI hT l k hl G _ p hp lam h1
  have := hD.finite (2 * ((d + 1 : ℕ) : ℤ))
  obtain ⟨s, a, ha⟩ := H.basis ℚ_[l] _ lam fun h0 => by
    obtain ⟨s, c, a, h⟩ := hD
    exact subsingleton_of_forall_eq 0 fun x => h _ x fun t hn => by rw [h0]; rfl
  obtain ⟨Λ, hΛ⟩ := hK.int lam 0 _ (add_zero _)
  obtain ⟨b, hb, hδ⟩ := H.top l k hl _ p hp hR hL hK lam s a ha Λ hΛ (G.diag (d + 1) p)
  rw [H.int_one hI l k hl G _ p hp lam h1 Λ hΛ] at hb
  have hr' : i ≫ π ≫ pullback.fst p p = r := by rw [← Category.assoc, hpb.w, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hΔ := (H.pairs k (d + 1) p inferInstance hp.2).1
  obtain ⟨U₀, hU₀⟩ := H.offEx.1 _ hΔ.cl
  have hUU : U = π ⁻¹ᵁ U₀ := TopologicalSpace.Opens.ext (hU.trans (H.offEx.2 _ _ _ _ hpb U₀ hU₀).symm)
  have h0 : pb l U.ι _ (pb l π _ (G.diag (d + 1) p)) = 0 := by
    rw [hUU, ← LinearMap.comp_apply, ← pb_comp, ← morphismRestrict_ι, pb_comp, LinearMap.comp_apply]
    unfold GysQ.diag GysQ.cls
    rw [dif_pos hΔ, G.off hΔ _ U₀ hU₀, map_zero]
  have hw : (2 : ℤ) + 2 * d = 2 * ((d + 1 : ℕ) : ℤ) := by push_cast; ring
  obtain ⟨m, hm⟩ := H.div l k hl hR G p i (π ≫ pullback.fst p p) c (by rwa [Category.assoc])
    (by rw [← Category.assoc, hr']; infer_instance) U hU e he (by rwa [hr']) (2 * d) _ hw _ h0
  have key : ∀ (w : ℤ) (hw : 2 + 2 * d = w) (δ : V l (pullback p p) w) (a : Fin s → V l X w),
      pb l π _ δ = cupV l W hw e m → LinearIndependent ℚ_[l] a →
      δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {x : V l (pullback p p) w |
        ∃ (n n' : ℤ) (h : n + n' = w) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ x = ext2 l p h u v} →
      ∃ (δ : V l (pullback p p) (2 + 2 * d)) (m : V l W (2 * d)) (s : ℕ) (a : Fin s → V l X (2 + 2 * d)) (b : Fin s → V l X 0),
        pb l π _ δ = cupV l W rfl e m ∧ LinearIndependent ℚ_[l] a ∧ ∑ t, b t = oneV l X ∧
        δ - ∑ t, ext2 l p (add_zero _) (a t) (b t) ∈ Submodule.span ℚ_[l] {w : V l (pullback p p) (2 + 2 * d) |
          ∃ (n n' : ℤ) (h : n + n' = 2 + 2 * d) (u : V l X n) (v : V l X n'), 0 ≤ n ∧ 0 < n' ∧ w = ext2 l p h u v} := by
    rintro _ rfl δ a h1 h2 h3
    exact ⟨δ, m, s, a, b, h1, h2, hb, h3⟩
  exact key _ hw _ a hm a.linearIndependent hδ

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PDetectL
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

private theorem exterior_product_cup_snd (R : Ring l) {X : Scheme.{0}} (p : X ⟶ S k) {a b n m t w : ℤ}
    (h1 : a + b = m) (h2 : m + n = w) (h3 : b + n = t) (h4 : a + t = w)
    (u : V l X a) (v : V l X b) (x : V l X n) :
    cupV l _ h2 (ext2 l p h1 u v) (pb l (pullback.snd p p) n x) =
      ext2 l p h4 u (cupV l X h3 v x) := by
  simp only [ext2]
  rw [R.assoc _ a b n m t w h1 h2 h3 h4, ← R.nat (pullback.snd p p) b n t h3 v x]

private theorem cup_fst_exterior_product (R : Ring l) {X : Scheme.{0}} (p : X ⟶ S k) {a b n m t w : ℤ}
    (h1 : a + b = m) (h2 : n + m = w) (h3 : n + a = t) (h4 : t + b = w)
    (x : V l X n) (u : V l X a) (v : V l X b) :
    cupV l _ h2 (pb l (pullback.fst p p) n x) (ext2 l p h1 u v) =
      ext2 l p h4 (cupV l X h3 x u) v := by
  simp only [ext2]
  rw [← R.assoc _ n a b t m w h3 h4 h1 h2, ← R.nat (pullback.fst p p) n a t h3 x u]

private theorem int_cup_snd (R : Ring l) {d : ℕ} {X : Scheme.{0}} {p : X ⟶ S k} (K : Kun l k d p)
    {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]} {n w : ℤ} (h : 2 * d + n = w)
    {Λ : V l (pullback p p) w →ₗ[ℚ_[l]] V l X n} (hΛ : IsInt l p lam h Λ)
    {Λ0 : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0} (h0 : IsInt l p lam (add_zero _) Λ0)
    (x : V l X n) (y : V l (pullback p p) (2 * d)) :
    Λ (cupV l _ h y (pb l (pullback.snd p p) n x)) = cupV l X (zero_add n) (Λ0 y) x := by
  have key : Λ ∘ₗ (cupV l (pullback p p) h).flip (pb l (pullback.snd p p) n x) =
      ((cupV l X (zero_add n)).flip x) ∘ₗ Λ0 := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      rw [exterior_product_cup_snd R p hab h (zero_add n) h u v x, hΛ.1, h0.1, map_smul, LinearMap.smul_apply]
    · rw [exterior_product_cup_snd R p hab h rfl (by omega : a + (b + n) = w) u v x,
        hΛ.2 a (b + n) _ (by omega) u _, h0.2 a b hab hb u v, map_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun key y

private theorem int_fst_cup {d : ℕ} (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]} {n w a b : ℤ} (h : 2 * d + n = w) (h2 : n + 2 * d = w)
    (h1 : a + b = 2 * d) {Λ : V l (pullback p p) w →ₗ[ℚ_[l]] V l X n} (hΛ : IsInt l p lam h Λ)
    (x : V l X n) (u : V l X a) (v : V l X b)
    (hx : ∀ hh : n + a = 2 * d, lam (cupV l X hh x u) = 0) :
    Λ (cupV l _ h2 (pb l (pullback.fst p p) n x) (ext2 l p h1 u v)) = 0 := by
  by_cases hb : b = n
  · subst b
    have ht : n + a = 2 * d := by omega
    rw [cup_fst_exterior_product R p h1 h2 ht h, hΛ.1, hx ht, zero_smul]
  · rw [cup_fst_exterior_product R p h1 h2 rfl (by omega : n + a + b = w)]
    exact hΛ.2 _ b _ hb _ _

theorem detectL_holds : DetectL := by
  intro l _ k _ _ hl d X p hSP R K lam δ hswap hΛ0
  obtain ⟨Λ0, h0⟩ := K.int lam 0 (2 * d) (add_zero _)
  have hone := hΛ0 Λ0 h0
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hδ : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [K.span]
    trivial
  obtain ⟨N, f, g, hsum⟩ := Submodule.mem_span_set'.mp hδ
  have hg : ∀ t, ∃ a b, ∃ h : a + b = 2 * (d : ℤ), ∃ u v, (g t : V l (pullback p p) (2 * d)) = ext2 l p h u v :=
    fun t => (g t).2
  choose A B hAB U W hUW using hg
  refine ⟨N, A, U, fun n x hx => ?_⟩
  obtain ⟨Λ, hΛ⟩ := K.int lam n (2 * d + n) rfl
  calc x = cupV l X (zero_add n) (oneV l X) x := (R.one_mul X hunit n x).symm
    _ = cupV l X (zero_add n) (Λ0 δ) x := by rw [hone]
    _ = Λ (cupV l _ (rfl : 2 * (d : ℤ) + n = 2 * d + n) δ (pb l (pullback.snd p p) n x)) :=
        (int_cup_snd R K rfl hΛ h0 x δ).symm
    _ = Λ (cupV l _ (by ring : n + 2 * (d : ℤ) = 2 * d + n) (pb l (pullback.fst p p) n x) δ) := by
        rw [hswap n _ (by ring) rfl x]
    _ = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hsum, map_sum, map_sum]
        apply Finset.sum_eq_zero
        intro t _
        rw [map_smul, map_smul, hUW t,
          int_fst_cup R rfl (by ring) (hAB t) hΛ x (U t) (W t) (hx t), smul_zero]

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PDualL
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.dualL_holds :
    UpperTheory.Gal.KunnethLefschetz.DualL := by
  intro l _ k _ _ hl d X p hSP hint R L lam hdet hlam
  obtain ⟨s, c, a, hA⟩ := hdet
  have hprop := hSP.1
  have nd : ∀ (n m : ℤ) (h : n + m = 2 * (d : ℤ)) (y : V l X m),
      (∀ x : V l X n, lam (cupV l X h x y) = 0) → y = 0 := by
    intro n m h y hy
    apply hA m y
    intro t ht
    obtain rfl : c t = n := by omega
    rw [R.comm X m (c t) _ ht h, Units.smul_def, map_zsmul, hy, smul_zero]
  have fd : ∀ n, FiniteDimensional ℚ_[l] (V l X n) := by
    intro n
    classical
    let f : V l X n →ₗ[ℚ_[l]] (Fin s → ℚ_[l]) := LinearMap.pi fun t =>
      if h : n + c t = 2 * (d : ℤ) then lam ∘ₗ (cupV l X h).flip (a t) else 0
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hA n x
    intro t h
    have := congrFun hx t
    simpa [f, h] using this
  have van : ∀ n, 2 * (d : ℤ) < n → Subsingleton (V l X n) := by
    intro n hn
    have key : ∀ z : V l X n, z = 0 := fun z => hA n z (fun t h => by
      haveI := L.neg X (c t) (by omega)
      rw [Subsingleton.elim (a t) 0]
      simp)
    exact ⟨fun x y => by rw [key x, key y]⟩
  have le : ∀ n m (h : n + m = 2 * (d : ℤ)),
      Module.finrank ℚ_[l] (V l X m) ≤ Module.finrank ℚ_[l] (V l X n) := by
    intro n m h
    haveI := fd n
    haveI := fd m
    have inj : Function.Injective ((cupV l X h).compr₂ lam).flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
    have := LinearMap.finrank_le_finrank_of_injective inj
    rwa [Subspace.dual_finrank_eq] at this
  have d0 : Module.finrank ℚ_[l] (V l X 0) ≤ 1 := by
    by_cases hpt : Nonempty (Pt p)
    · obtain ⟨y0⟩ := hpt
      have hcon : ConnectedSpace X :=
        connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected
      have inj : Function.Injective (pb l y0.1 0) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply L.pts p hprop z
        intro y
        rw [L.conn p hprop hcon z y y0, hz]
      have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℚ_[l] _ (oneV l (S k))) := by
        intro w
        obtain ⟨r, hr, -⟩ := L.line w
        exact ⟨r, hr.symm⟩
      haveI : Module.Finite ℚ_[l] (V l (S k) 0) := Module.Finite.of_surjective _ hsurj
      calc Module.finrank ℚ_[l] (V l X 0) ≤ Module.finrank ℚ_[l] (V l (S k) 0) :=
            LinearMap.finrank_le_finrank_of_injective inj
        _ ≤ 1 := finrank_le_one (oneV l (S k)) (fun w => (L.line w).exists.imp fun r hr => hr.symm)
    · have hz : ∀ z : V l X 0, z = 0 := fun z => L.pts p hprop z (fun y => (hpt ⟨y⟩).elim)
      haveI : Subsingleton (V l X 0) := ⟨fun x y => by rw [hz x, hz y]⟩
      simp [Module.finrank_zero_of_subsingleton]
  obtain ⟨x0, hx0⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hlam (LinearMap.ext hc)
  have surj : Function.Surjective lam := fun r => ⟨(r / lam x0) • x0, by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx0]⟩
  haveI := fd (2 * (d : ℤ))
  have hnt : Nontrivial (V l X (2 * (d : ℤ))) := ⟨⟨x0, 0, fun h => hx0 (by rw [h, map_zero])⟩⟩
  have d2 : Module.finrank ℚ_[l] (V l X (2 * (d : ℤ))) = Module.finrank ℚ_[l] ℚ_[l] := by
    rw [Module.finrank_self]
    have h1 := (le 0 (2 * (d : ℤ)) (zero_add _)).trans d0
    have h2 := Module.finrank_pos (R := ℚ_[l]) (M := V l X (2 * (d : ℤ)))
    omega
  have inj : Function.Injective lam := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d2).2 surj
  refine ⟨fd, van, LinearEquiv.ofBijective lam ⟨inj, surj⟩, fun n m h => ?_⟩
  have htr : ((LinearEquiv.ofBijective lam ⟨inj, surj⟩ : V l X (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l]) :
      V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] ℚ_[l]) = lam := LinearMap.ext fun x => rfl
  rw [htr]
  haveI := fd n
  haveI := fd m
  have injf : Function.Injective ((cupV l X h).compr₂ lam).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
  have heq : Module.finrank ℚ_[l] (V l X m) = Module.finrank ℚ_[l] (V l X n →ₗ[ℚ_[l]] ℚ_[l]) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm (le n m h) (le m n (by omega))
  exact ⟨injf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 injf⟩
end
end

