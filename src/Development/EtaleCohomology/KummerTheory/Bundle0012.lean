module

public import Development.EtaleCohomology.KummerTheory.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0030
public import Development.EtaleCohomology.KummerTheory.Bundle0009
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Development.EtaleCohomology.TateTwists.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0015
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.KummerTheory.Bundle0006
public import Development.EtaleCohomology.KummerTheory.ForgetInjPf
public import Development.EtaleCohomology.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.AdicLimPfKer
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

universe u

namespace LateralTheory.KummerTheory.KerPf

theorem seqSec (S : ℕ → Type u) [∀ a, Finite (S a)] [∀ a, Nonempty (S a)] (t : ∀ a, S (a + 1) → S a) :
    ∃ s : ∀ a, S a, ∀ a, t a (s (a + 1)) = s a :=
  _root_.UpperTheory.Reformulated.B.DYra4.main S t

variable (l : ℕ) [Fact l.Prime]

theorem redk (hA : A11) (E : Spc) (n i : ℤ) (x : Hl l E n i) (m : ℕ) :
    ∀ a : ℕ, red (l ^ (m + a)) (l ^ m) E n i (x.1 (m + a)) = x.1 m := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  intro a
  induction a with
  | zero => exact (@hA (l ^ m) (l ^ m) _ dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    have h := (@hA (l ^ (m + (a + 1))) (l ^ (m + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (x.1 (m + (a + 1)))
    rw [← h, ← ih]
    exact congrArg _ (x.2 (m + a))

omit [Fact l.Prime] in
theorem smul_zero_of (E : Spc) (n i : ℤ) (k b : ℕ) (hkb : k ≤ b) (z : Ht (l ^ k) E n i) : (l ^ b) • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ k)), (CharP.cast_eq_zero_iff (ZMod (l ^ k)) (l ^ k) _).2 (pow_dvd_pow l hkb), zero_smul]

theorem ker (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) (b : ℕ) (x : Hl l E n i) (hx : lev l x b = 0) :
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ b) • y := by
  obtain ⟨u, d, h⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin a n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).1 (x.1 (b + a))).1 (by rw [redk l hA E n i x b a]; exact hx)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (h a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  obtain ⟨s, hs⟩ := seqSec S t
  let y : Hl l E n i := ⟨fun a => (s a).1, fun a => congrArg Subtype.val (hs a)⟩
  refine ⟨y, ?_⟩
  have e : ((l : ℤ_[l]) ^ b) • y = (l ^ b : ℕ) • y := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]; push_cast; rfl
  rw [e]
  apply Subtype.ext
  funext k
  change x.1 k = (l ^ b) • (s k).1
  rcases le_or_gt b k with hk | hk
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hr := redk l hA E n i y a b
    rw [Nat.add_comm a b] at hr
    rw [← (h a n).2.2.2.1 ((s (b + a)).1)]
    change x.1 (b + a) = u a n (red _ _ E n i (y.1 (b + a)))
    rw [hr]
    exact (s a).2.symm
  · rw [smul_zero_of l E n i k b hk.le]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    rw [← redk l hA E n i x k c]
    change red _ _ E n i (lev l x (k + c)) = 0
    rw [hx, map_zero]

end LateralTheory.KummerTheory.KerPf

namespace LateralTheory.KummerTheory

theorem AdicKer_holds : AdicKer := fun hA l _ E i hB hFin n k x hx => KerPf.ker l hA E i hB hFin n k x hx

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.CokAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem bcMap_comp' {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (g' : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = g') :
    bcMap p g g' h' e' ≫ bcMap p f g h e = bcMap p f g' (h ≫ h') (by rw [← Category.assoc, e, e']) := by
  apply pullback.hom_ext <;>
    simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.comp_id, Spec.map_comp]

theorem bcMap_eq {X : Scheme.{0}} {R A B : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B)
    (h h' : A ⟶ B) (e : f ≫ h = g) (hh : h = h') : bcMap p f g h e = bcMap p f g h' (hh ▸ e) := by
  subst hh; rfl

theorem CokAff_of (hS : StrictHenselization) (hC : Cont) (hL : LhNat) : CokAff := by
  classical
  intro h2 h6 hb1 q _ X R p _ _ hq i r c M N n hiso B s b x
  obtain ⟨J, _, _, D, cc, hcc, u, hSH, hu⟩ := hS B b
  have hun : ∀ {j k : J} (f : j ⟶ k), u.app j ≫ D.map f = u.app k := by
    intro j k f
    have := u.naturality f
    simpa using this.symm
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  let w : B ⟶ cc.pt := u.app j0 ≫ cc.ι.app j0
  have hw : ∀ j, u.app j ≫ cc.ι.app j = w := by
    intro j
    show _ = u.app j0 ≫ cc.ι.app j0
    rw [← cc.w (IsFiltered.leftToMax j j0), ← cc.w (IsFiltered.rightToMax j j0), ← Category.assoc,
      ← Category.assoc, hun, hun]
  let v : R ⟶ cc.pt := s ≫ w
  obtain ⟨y, hy⟩ := (hiso cc.pt v hSH).2 (pull _ (sch.map (bcMap p s v w rfl)) _ _ x)
  have hqc : IsUnit ((q : ℕ) : cc.pt) := by simpa using hq.map v.hom
  have hB := fun n' i' => (hb1 q D cc hcc n' i').1
  choose jj z hz using fun (a : Fin (M + 1)) (t : Fin (r a)) => hB _ _ (y a t) hqc
  obtain ⟨k0, hk0⟩ := IsFiltered.sup_objs_exists
    (Finset.univ.image (fun pr : (Σ a : Fin (M + 1), Fin (r a)) => jj pr.1 pr.2))
  have fk : ∀ a t, jj a t ⟶ k0 := fun a t => (hk0 (Finset.mem_image.2 ⟨⟨a, t⟩, Finset.mem_univ _, rfl⟩)).some
  let y0 : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj (Spec (D.obj k0))) (n - ((a : ℕ) : ℤ)) 0 :=
    fun a t => pull _ (sch.map (Spec.map (D.map (fk a t)))) _ _ (z a t)
  have hy0 : ∀ a t, pull _ (sch.map (Spec.map (cc.ι.app k0))) _ _ (y0 a t) = y a t := by
    intro a t
    rw [← hz a t]
    simp only [y0]
    rw [← pull_comp, ← Functor.map_comp, ← Spec.map_comp, cc.w]
    rfl
  let g : Over.mk (Spec.map v) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
    Over.homMk (Spec.map (cc.ι.app k0)) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, Category.assoc, hw])
  have hrst : rst p g = bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]) := rfl
  have h0 := hL h6 q p i r c M n g y0
  rw [hrst] at h0
  have hyy : (fun a t => pull _ (sch.map g.left) _ _ (y0 a t)) = y := by
    funext a t; exact hy0 a t
  rw [hyy] at h0
  let e := lh q p (Spec.map (s ≫ u.app k0)) i r c M n y0 -
    N • pull _ (sch.map (bcMap p s (s ≫ u.app k0) (u.app k0) rfl)) _ _ x
  have he : pull _ (sch.map (bcMap p (s ≫ u.app k0) v (cc.ι.app k0) (by rw [Category.assoc, hw]))) _ _ e = 0 := by
    simp only [e, map_sub, map_nsmul]
    erw [h0, hy, ← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hw k0)]
    exact sub_self _
  have hC2 := (hC h2 hb1 q p hq D cc hcc (fun j => s ≫ u.app j)
    (fun {j k} f => by simp only [Category.assoc, hun]) v (fun j => by simp only [v, Category.assoc, hw]) n i).2 k0 e he
  obtain ⟨k1, f1, hk1⟩ := hC2
  obtain ⟨het, 𝔮, h𝔮⟩ := hu k1
  refine ⟨D.obj k1, u.app k1, het, ⟨(by exact 𝔮 : Spec (D.obj k1)), ?_⟩, fun a t => pull _ (sch.map (Spec.map (D.map f1))) _ _ (y0 a t), ?_⟩
  · exact (PrimeSpectrum.ext h𝔮 : PrimeSpectrum.comap (u.app k1).hom 𝔮 = b)
  · let g' : Over.mk (Spec.map (s ≫ u.app k1)) ⟶ Over.mk (Spec.map (s ≫ u.app k0)) :=
      Over.homMk (Spec.map (D.map f1)) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, Category.assoc, hun])
    have h1 := hL h6 q p i r c M n g' y0
    have hrst' : rst p g' = bcMap p (s ≫ u.app k0) (s ≫ u.app k1) (D.map f1) (by rw [Category.assoc, hun]) := rfl
    rw [hrst'] at h1
    beta_reduce at hk1
    simp only [e, map_sub, map_nsmul, sub_eq_zero] at hk1
    erw [h1] at hk1
    refine hk1.trans ?_
    erw [← pull_comp, ← Functor.map_comp, bcMap_comp', bcMap_eq _ _ _ _ _ _ (hun f1)]

end LateralTheory.KummerTheory.LHCut
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.CupAWCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AW
variable {R : Type} [CommRing R] {E : Spc} {I J K : Cx R} {n m k : ℤ} {U : Scheme.{0}}

def ev0 (α : Cochain ((chains R).obj E) I n) (s : ℤ) (U : Scheme.{0}) (p : ℕ) (x : Sx E p U) : Sec (I.X s) U :=
  if h : -(p : ℤ) + n = s then ev α p s h U x else 0

theorem ev_delta {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (x : Sx E p U) :
    ev (δ n m α) p t ht U x = Sec.map (I.d s t) (ev α p s hs U x) + m.negOnePow • bd (ev0 α t U) p x := by
  cases p with
  | zero => rw [ev_delta_zero hm α s t hs]; simp [bd]
  | succ p =>
    rw [ev_delta_succ hm α p s t hs]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dite_eq_left]

def pr (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (w : ℤ) (U : Scheme.{0})
    (p q : ℕ) (y : Sx E p U) (z : Sx E q U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w h (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

variable (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem mul_ev {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (ev β q t ht U z) = pr μ α β w U p q y z := by
  subst hs ht
  rw [pr, dite_eq_left h]

theorem mul_bd_left {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + (n + 1) = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (bd (ev0 α s U) p y) (ev β q t ht U z) = bd (fun a y => pr μ α β w U a q y z) p y := by
  cases p with
  | zero => simp [bd]
  | succ p =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dite_eq_left (by omega), mul_ev]

theorem mul_bd_right {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + (m + 1) = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (bd (ev0 β t U) q z) = bd (fun b z => pr μ α β w U p b y z) q z := by
  cases q with
  | zero => simp [bd]
  | succ q =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dite_eq_left (by omega), mul_ev]

theorem d_pr {w : ℤ} {p q : ℕ} (h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w) (y : Sx E p U) (z : Sx E q U) :
    Sec.map (K.d w (w + 1)) (pr μ α β w U p q y z) =
      (pr μ (δ n (n + 1) α) β (w + 1) U p q y z -
        (((n + 1).negOnePow : ℤˣ) : ℤ) • bd (fun a y => pr μ α β (w + 1) U a q y z) p y) +
      (((-(p : ℤ) + n).negOnePow : ℤˣ) : ℤ) • (pr μ α (δ m (m + 1) β) (w + 1) U p q y z -
        (((m + 1).negOnePow : ℤˣ) : ℤ) • bd (fun b z => pr μ α β (w + 1) U p b y z) q z) := by
  rw [pr, dite_eq_left h, μ.leibniz, Units.smul_def]
  congr 1
  · rw [← mul_ev μ (δ n (n + 1) α) β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      ev_delta rfl α p _ _ rfl, ← mul_bd_left μ α β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      map_add, Units.smul_def, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, add_sub_cancel_right]
  · rw [← mul_ev μ α (δ m (m + 1) β) (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      ev_delta rfl β q _ _ rfl, ← mul_bd_right μ α β (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      map_add, Units.smul_def, map_zsmul, add_sub_cancel_right]

variable {μ α β} in
theorem aw_eq {hk : n + m = k} {γ : Cochain ((chains R).obj E) K k} (hγ : μ.IsAW hk α β γ) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) : ev γ N w h U x = ∑ p : Fin (N + 1), (((m * (p : ℕ)).negOnePow : ℤˣ) : ℤ) •
      pr μ α β w U p (N - p) (x.sub 0 p (by omega)) (x.sub p (N - p) (by omega)) := by
  rw [hγ N w h U x]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_ev, Units.smul_def]

theorem leibniz : LateralTheory.EtaleFoundations.cupflip_aw_leibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ h h1 h2
  refine ev_ext _ _ fun M w' hw' U x => ?_
  obtain ⟨w, rfl⟩ : ∃ w, w' = w + 1 := ⟨w' - 1, by omega⟩
  have hw : -(M : ℤ) + k = w := by omega
  have hb : bd (ev0 γ (w + 1) U) M x = _ :=
    (bd_congr (fun N y e => by rw [ev0, dite_eq_left (by omega), aw_eq h]) x).trans
      (bd_aw (pr μ α β (w + 1) U) (fun p => (((m * p).negOnePow : ℤˣ) : ℤ))
        (fun p => ((m.negOnePow * (m * p).negOnePow : ℤˣ) : ℤ)) (fun p => by
          push_cast
          rw [mul_add, mul_one, Int.negOnePow_add]
          rcases Int.units_eq_one_or m.negOnePow with e | e <;> simp [e]) M x)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ev_delta rfl γ M w _ hw, ev_add, ev_units_smul, aw_eq h, aw_eq h1, aw_eq h2, hb, Sec.map, map_sum,
    Units.smul_def, Units.smul_def, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  have hd := d_pr μ α β (w := w) (p := p) (q := M - p) (by omega) (x.sub 0 p (by omega)) (x.sub p (M - p) (by omega))
  rw [Sec.map] at hd
  rw [map_zsmul, hd]
  have e : (-1 : ℤ) ^ (p : ℕ) = ((((p : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) := by simp [Int.coe_negOnePow_natCast]
  rw [e, ← hk, add_mul, one_mul]
  simp only [Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one]
  generalize (m * (p : ℕ)).negOnePow = c
  generalize ((p : ℕ) : ℤ).negOnePow = d
  generalize n.negOnePow = a
  rcases Int.units_eq_one_or m.negOnePow with e | e <;> rw [e] <;> push_cast <;> module

theorem aw_cochain : LateralTheory.EtaleFoundations.cupflip_aw_cochain :=
  LateralTheory.EtaleFoundations.cupflip_aw_cochain_of LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
    (fun _ _ _ _ _ α p s h _ _ g x => ev_res α p s h g x) LateralTheory.EtaleFoundations.cupflip_sub_res_holds

theorem aw_exists : LateralTheory.EtaleFoundations.cupflip_aw_exists := LateralTheory.EtaleFoundations.cupflip_aw_exists_of aw_cochain leibniz

variable {μ α β} in
theorem aw_unique {hk : n + m = k} {γ γ' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk α β γ) (h' : μ.IsAW hk α β γ') :
    γ = γ' := ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem wd_aw : LateralTheory.EtaleFoundations.cupflip_wd_aw := by
  intro R _ I J K μ E n m k hk
  refine ⟨aw_exists R μ E hk, fun _ _ _ _ => aw_unique, fun α α' β γ γ' h h' N w hw U x => ?_,
    fun α β β' γ γ' h h' N w hw U x => ?_⟩ <;>
  · rw [ev_add, h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem wd_cobdry : LateralTheory.EtaleFoundations.cupflip_wd_cobdry := by
  rintro R _ I J K μ E n m k hk α β γ h (⟨n', hn, η, hη⟩ | ⟨m', hm, η, hη⟩)
  · subst hn
    obtain rfl : k = n' + m + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl η β.1
    refine ⟨n' + m, rfl, θ, ?_⟩
    rw [leibniz R μ rfl η β.1 θ γ.1 0 hθ (by rw [hη]; exact h)
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_right μ _ _), smul_zero, add_zero]
  · subst hm
    obtain rfl : k = n + m' + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl α.1 η
    refine ⟨n + m', rfl, n.negOnePow • θ, ?_⟩
    rw [δ_units_smul, leibniz R μ rfl α.1 η θ 0 γ.1 hθ
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_left μ _ _) (by rw [hη]; exact h), zero_add, smul_smul,
      Int.units_mul_self, one_smul]

theorem wd : LateralTheory.EtaleFoundations.cupflip_wd := LateralTheory.EtaleFoundations.cupflip_wd_of wd_aw wd_cobdry

theorem cup_mk {hk : n + m = k} (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) :
    μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  pick_spec (wd R μ E hk) α β γ h

end LateralTheory.KummerTheory.AW

theorem LateralTheory.KummerTheory.CupAW_of : LateralTheory.KummerTheory.CupAW := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := AW.aw_exists R μ E hk α β
  exact ⟨γ, hγ, AW.cup_mk μ α β γ hγ⟩

end
end

-- bundled from Development.EtaleCohomology.KummerTheory.DictNormalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def NrmMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (a p s h U x) = a p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def NrmDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (_hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
  (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
  ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
    m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U ((E.δ i).app (op U) x)

def up {X U : Scheme.{0}} {p q : ℕ} (x : Sx (sch.obj X) p U) : Sx (sch.obj X) q U := x

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) :
    ((sch.obj X).δ i).app (op U) x = up x := rfl

theorem altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h2, this, hk.neg_one_pow]

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]

theorem ev_sub' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of (hM : NrmMk) (hD : NrmDelta) : DictNormal := by
  intro R _ I X n α
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  obtain ⟨β, hβ⟩ := hM R (E := sch.obj X) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      dsimp only
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))
      · exact map_zero _)
  let γ : Cocycle ((chains R).obj (sch.obj X)) I n :=
    ⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩
  refine ⟨α - γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff γ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p s h U y
    show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0
    rw [ev_sub', sub_eq_zero]
    rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
    simp only [face_sch, hβ]
    rcases Nat.even_or_odd p with hp | hp
    ·
      have hp1 : Odd (p + 1) := hp.add_one
      have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
      simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
      have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
        (by push_cast at h ⊢; omega) (up y)
      rw [hα, ev_zero'] at hc
      simp only [face_sch] at hc
      rw [← Finset.sum_smul, altsum] at hc
      have he : ¬ Even (p + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
      simp only [he, if_false, one_smul] at hc
      rw [Int.negOnePow_succ, Units.neg_smul] at hc
      have key := add_neg_eq_zero.1 hc.symm
      rw [Units.smul_def]
      refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
      rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
          = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
      rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      rfl
    · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
      simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
      rw [← Finset.sum_smul, altsum]
      have he : ¬ Even (p + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
      simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
      rfl

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem chains_d (R : Type) [CommRing R] (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  simp only [chainsN, Functor.comp_obj]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

def evAt {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := (φ.hom.app (op U)).hom y
  map_zero' := by simp
  map_add' := by simp

theorem evAt_apply {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) (φ : F ⟶ G) :
    evAt U y φ = (φ.hom.app (op U)).hom y := rfl

theorem nrmDelta : NrmDelta := by
  intro R _ E I n m hm α U p s t hs ht x
  unfold ev
  rw [δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
    chains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp [Units.smul_def, Finset.smul_sum]
  refine (map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 2
  have := free_gen_map R (E.δ i) U x
  rw [evAt_apply]
  simp
  exact congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U)))
    ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of' (hM : NrmMk) : DictNormal := DictNormal_of hM nrmDelta
end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.FinInjSlice
section
namespace LateralTheory.Fin.InjSlice
theorem etale_forget_preservesInjectiveObjects : LateralTheory.KummerTheory.ForgetInj := by
  apply LateralTheory.KummerTheory.ForgetInj_of
theorem etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a : LateralTheory.KummerTheory.InjSlice := by
  apply LateralTheory.KummerTheory.InjSlice_of <;> first | exact etale_forget_preservesInjectiveObjects
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.InjSlice := etale_injective_sheaf_restricts_to_slice_injective_in_local_homotopy_a
end LateralTheory.Fin.InjSlice
end

