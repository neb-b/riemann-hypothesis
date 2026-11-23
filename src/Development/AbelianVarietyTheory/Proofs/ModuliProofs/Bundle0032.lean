module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TateTower

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelIso (D : Datum H) {K : Type} [Field K] {Q : Type} [Group Q] (act : 𝓞 E → Q → Q)
    (e : ℕ → Q → Q → Kˣ → Prop) (N : ℕ) (p : Kˣ × (D.La → Q)) : Prop :=
  IsPrimitiveRoot p.1 N ∧ (∀ a c, p.2 (a + c) = p.2 a * p.2 c) ∧ (∀ (c : 𝓞 E) a, p.2 (c • a) = act c (p.2 a)) ∧
    (∀ a, p.2 a = 1 ↔ ∃ c, a = N • c) ∧ (∀ x, x ^ N = 1 ↔ ∃ a, p.2 a = x) ∧
    ∀ a c, e N (p.2 a) (p.2 c) (p.1 ^ D.EF a c)

variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem map_nsmul_of_add {M : Type} [AddCommGroup M] {f : M → Q} (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : M) : f (n • a) = f a ^ n :=
  map_nsmul (AddMonoidHom.mk' (fun a => Additive.ofMul (f a)) hf) n a

theorem nsmul_cancel (D : Datum H) {r : ℕ} (hr : 0 < r) {a c : D.La} (h : r • a = r • c) : a = c := by
  have := D.proj
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have h' : (r : ℤ) • a = (r : ℤ) • c := by simpa only [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hr.ne' : (r : ℤ) ≠ 0) h'

theorem LevelIso.pow
    (he : ∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c →
      e n (x ^ m) (x' ^ m) (c ^ m))
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) {p : Kˣ × (D.La → Q)} (h : LevelIso D act e (N * r) p) :
    LevelIso D act e N (p ^ r) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hp : ∀ a, (p ^ r).2 a = p.2 (r • a) := fun a => (map_nsmul_of_add h2 r a).symm
  refine ⟨h1.pow (Nat.mul_pos hN hr) (mul_comm _ _), fun a c => ?_, fun c a => ?_, fun a => ?_, fun x => ?_,
    fun a c => ?_⟩
  · rw [hp, hp, hp, smul_add, h2]
  · rw [hp, hp, smul_comm, h3]
  · rw [hp, h4]
    refine exists_congr fun c => ⟨fun h => nsmul_cancel D hr ?_, fun h => ?_⟩
    · rw [h, mul_comm, mul_smul]
    · rw [h, mul_comm, mul_smul]
  · constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (h5 x).1 (by rw [pow_mul, hx, one_pow])
      rw [← map_nsmul_of_add h2, h4] at hx
      obtain ⟨c, hc⟩ := hx
      rw [mul_smul] at hc
      exact ⟨c, by rw [hp, nsmul_cancel D hN hc]⟩
    · rintro ⟨a, rfl⟩
      rw [hp, ← map_nsmul_of_add h2, h4]
      exact ⟨a, by rw [mul_smul]⟩
  · have := he N r _ _ _ hN hr ((h5 _).2 ⟨a, rfl⟩) ((h5 _).2 ⟨c, rfl⟩) (h6 a c)
    have e1 : (p.1 ^ D.EF a c) ^ r = (p.1 ^ r) ^ D.EF a c := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e1] at this
    exact this

theorem finite_levelIso {N : ℕ} (hN : 0 < N) (hQ : Finite {x : Q // x ^ N = 1}) :
    {p | LevelIso D act e N p}.Finite := by
  have := D.fin
  have hf : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 hf)
  have := hSf.to_subtype
  have hQ' : {x : Q | x ^ N = 1}.Finite := hQ
  have hζ : {ζ : Kˣ | ζ ^ N = 1}.Finite := by
    have : NeZero N := ⟨hN.ne'⟩
    have : Finite (rootsOfUnity N K) := inferInstance
    exact this
  refine Set.Finite.of_finite_image (f := fun p => (p.1, fun s : S => p.2 s))
    ((hζ.prod (Set.Finite.pi' (fun _ : S => hQ'))).subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨hp.1.pow_eq_one, fun s => (hp.2.2.2.2.1 _).2 ⟨_, rfl⟩⟩
  · intro p hp q hq h
    refine Prod.ext (Prod.ext_iff.1 h).1 (funext fun a => ?_)
    have := AddMonoidHom.eq_of_eqOn_dense hS
      (f := AddMonoidHom.mk' (fun a => Additive.ofMul (p.2 a)) hp.2.1)
      (g := AddMonoidHom.mk' (fun a => Additive.ofMul (q.2 a)) hq.2.1)
      (fun s hs => congrFun (Prod.ext_iff.1 h).2 ⟨s, hs⟩)
    exact DFunLike.congr_fun this a

theorem tateIso_of_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (k : ℕ) (z : K) (κ : Type) (lam : κ → D.La) (y : κ → Q), 0 < k → (∀ n, 0 < n → Finite {x : Q // x ^ n = 1}) → (∀ n m x x' c, 0 < n → 0 < m → x ^ (n * m) = 1 → x' ^ (n * m) = 1 → e (n * m) x x' c → e n (x ^ m) (x' ^ m) (c ^ m)) → (∀ m, 0 < m → ∃ (ζ : Kˣ) (ev : D.La → Q), IsPrimitiveRoot ζ (k * m) ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = act c (ev a)) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = (k * m) • c) ∧ (∀ x, x ^ (k * m) = 1 ↔ ∃ a, ev a = x) ∧ (∀ a c, e (k * m) (ev a) (ev c) (ζ ^ D.EF a c)) ∧ (ζ : K) ^ m = z ∧ ∀ i, ev (lam i) ^ m = y i) → ∃ I : TateIso D K Q act e, (I.ζ k : K) = z ∧ ∀ i, I.ev k (lam i) = y i := by
  intro E _ _ _ H D K _ Q _ act e k z κ lam y hk hQ he hex
  have hx : ∀ j : ℕ, ∃ p : Kˣ × (D.La → Q), LevelIso D act e (k * j.factorial) p ∧
      (p.1 : K) ^ j.factorial = z ∧ ∀ i, p.2 (lam i) ^ j.factorial = y i := fun j => by
    obtain ⟨ζ, ev, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hex _ j.factorial_pos
    exact ⟨(ζ, ev), ⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩
  choose x hx hz hy using hx
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ k * j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj =>
      Dvd.dvd.mul_left (Nat.dvd_factorial hn hj) k)
  have hs : ∀ n, 0 < n → ∃ s, LevelIso D act e n s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s := fun n hn => by
    have hm : {p | LevelIso D act e n p} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      refine (hU n hn).mono fun j hj => ?_
      have hj' := hx j
      have hpos := Nat.mul_pos hk j.factorial_pos
      rw [← Nat.mul_div_cancel' hj] at hj'
      exact hj'.pow he hn (Nat.div_pos (Nat.le_of_dvd hpos hj) hn)
    obtain ⟨s, h1, h2⟩ := Ultrafilter.eq_pure_of_finite_mem (finite_levelIso hn (hQ n hn)) hm
    refine ⟨s, h1, ?_⟩
    have : {s} ∈ U.map fun j => x j ^ (k * j.factorial / n) := by
      rw [h2]
      exact rfl
    exact this
  have hs' : ∀ n, ∃ s, LevelIso D act e (max n 1) s ∧ ∀ᶠ j in U, x j ^ (k * j.factorial / max n 1) = s :=
    fun n => hs _ (by omega)
  choose s hs1 hs2 using hs'
  have hs3 : ∀ n, 0 < n → LevelIso D act e n (s n) := fun n hn => by
    have := hs1 n
    rwa [max_eq_left hn] at this
  have hs4 : ∀ n, 0 < n → ∀ᶠ j in U, x j ^ (k * j.factorial / n) = s n := fun n hn => by
    have := hs2 n
    rwa [max_eq_left hn] at this
  have htow : ∀ n m, 0 < n → 0 < m → s (n * m) ^ m = s n := fun n m hn hm => by
    have hnm := Nat.mul_pos hn hm
    obtain ⟨j, h1, h2, c, h3⟩ := ((hs4 _ hnm).and ((hs4 n hn).and (hU _ hnm))).exists
    rw [← h1, ← h2, h3, ← pow_mul, Nat.mul_div_cancel_left _ hnm, Nat.mul_assoc, Nat.mul_div_cancel_left _ hn,
      mul_comm c m]
  obtain ⟨j, hj⟩ := (hs4 k hk).exists
  rw [Nat.mul_div_cancel_left _ hk] at hj
  refine ⟨⟨fun n => (s n).1, fun n hn => (hs3 n hn).1, fun n m hn hm => congrArg Prod.fst (htow n m hn hm),
    fun n => (s n).2, fun n => (hs1 n).2.1, fun n => (hs1 n).2.2.1, fun n hn => (hs3 n hn).2.2.2.1,
    fun n hn => (hs3 n hn).2.2.2.2.1, fun n m hn hm a => congrFun (congrArg Prod.snd (htow n m hn hm)) a,
    fun n hn => (hs3 n hn).2.2.2.2.2⟩, ?_, fun i => ?_⟩
  · show ((s k).1 : K) = z
    rw [← hj, ← hz j]
    exact Units.val_pow_eq_pow_val _ _
  · show (s k).2 (lam i) = y i
    rw [← hj, ← hy j i]
    rfl

end GlobalTheory.TateTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsIsometry


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (hB : Function.Bijective B) (n : ℕ) (d : M) (hd : ∀ b, (n : ℤ) ∣ B d b) : ∃ f : M, d = n • f := by
  let φ : M →ₗ[ℤ] ℤ :=
    { toFun := fun b => B d b / n
      map_add' := fun x y => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hd x)
      map_smul' := fun c x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hd x) }
  obtain ⟨f, hf⟩ := hB.2 φ
  refine ⟨f, hB.1 ?_⟩
  ext b
  simp only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hd b)).symm


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
theorem _root_.GlobalTheory.TorsIsometry.ker_and_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  intro E _ _ _ H D K _ Q _ e n ζ ev hn hcard he1 hζ hev hevn hpair
  have hev0 : ev 0 = 1 := by
    have h := hev 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hevsmul : ∀ (m : ℕ) (c : D.La), ev (m • c) = ev c ^ m := by
    intro m c
    induction m with
    | zero => simp [hev0]
    | succ m ih => rw [succ_nsmul, hev, ih, pow_succ]
  have hker : ∀ a, ev a = 1 ↔ ∃ c, a = n • c := by
    intro a
    constructor
    · intro ha
      refine _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd D.EF D.unimod n a fun c => ?_
      have h := hpair a c
      rw [ha] at h
      exact (hζ.zpow_eq_one_iff_dvd _).1 (he1 _ _ (hevn c) h)
    · rintro ⟨c, rfl⟩
      rw [hevsmul, hevn]
  refine ⟨hker, fun y => ⟨fun hy => ?_, ?_⟩⟩
  swap
  · rintro ⟨a, rfl⟩
    exact hevn a
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : NoZeroSMulDivisors ℤ D.La := ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply D.unimod.1
      ext b
      have := congrArg (fun x => D.EF x b) h
      simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_zero,
        LinearMap.zero_apply] at this
      simpa [hc] using this⟩
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ D.La
  let g : (Fin (Module.finrank ℤ D.La) → ZMod n) → {y : Q // y ^ n = 1} :=
    fun t => ⟨ev (b.equivFun.symm fun i => ((t i).val : ℤ)), hevn _⟩
  have hinj : Function.Injective g := by
    intro t t' htt
    have h : ev (b.equivFun.symm fun i => ((t i).val : ℤ)) =
        ev (b.equivFun.symm fun i => ((t' i).val : ℤ)) := congrArg Subtype.val htt
    have hdiff : ev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) = 1 := by
      have h2 := hev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) (b.equivFun.symm fun i => ((t' i).val : ℤ))
      rw [sub_add_cancel, h] at h2
      exact mul_eq_right.1 h2.symm
    obtain ⟨c, hc⟩ := (hker _).1 hdiff
    funext i
    have hi := congrArg (fun z => b.equivFun z i) hc
    simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_nsmul,
      Pi.smul_apply, nsmul_eq_mul] at hi
    have hcast := congrArg (Int.cast : ℤ → ZMod n) hi
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  haveI : Finite {y : Q // y ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  obtain ⟨t, ht⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val ht⟩

end GlobalTheory.TorsIsometry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionFieldExt

variable {S : Scheme.{0}}

theorem comp_injective {K Ω : Type} [Field K] [Field Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (A : Over S) : Function.Injective (fun y : Over.mk x ⟶ A => u ≫ y) := by
  let v : Sp Ω ⟶ Sp K := u.left
  have : Surjective v := ⟨fun z => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi v := Flat.epi_of_flat_of_surjective v
  intro a b h
  have h' : v ≫ a.left = v ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi v).1 h')

theorem card_torsion (hL : Out.Laws) (P : Out.PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) {n : ℕ}
    (hn : (n : K) ≠ 0) : Nat.card {y : Over.mk x ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g) := by
  have hn' : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hL.polBaseChange S _ x P
  have c := (hL.mulN _ P' n hn').2.2.2.2 K (𝟙 _) hn
  let Φ : (Over.mk (𝟙 (Sp K)) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ x) ⟶ P.A) :=
    MonoidHom.mk' (fun y => Out.toBase hg.w y) (hmul _)
  have hΦ : Function.Bijective Φ :=
    ⟨fun a b e => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z =>
      ⟨Over.homMk (hg.lift z.left (𝟙 _) (Over.w z)) (hg.lift_snd _ _ _), Over.OverMorphism.ext (hg.lift_fst _ _ _)⟩⟩
  have e : Nat.card {y : Over.mk (𝟙 (Sp K)) ⟶ P'.A // y ^ n = 1} =
      Nat.card {y : Over.mk (𝟙 _ ≫ x) ⟶ P.A // y ^ n = 1} :=
    Nat.card_congr ((Equiv.ofBijective Φ hΦ).subtypeEquiv fun y => by
      show _ ↔ Φ y ^ n = 1
      rw [← map_pow, map_eq_one_iff Φ hΦ.1])
  rw [Category.id_comp] at e
  rw [← e, ← hdim]
  exact c

theorem exists_of_isAlgClosed (hL : Out.Laws) (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [IsAlgClosed Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S} (u : Over.mk x' ⟶ Over.mk x) {n : ℕ} (hK : (n : K) ≠ 0)
    (hΩ : (n : Ω) ≠ 0) (z : Over.mk x' ⟶ P.A) (hz : z ^ n = 1) :
    ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ u ≫ y = z := by
  have hn' : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hK Nat.cast_zero)
  have c₁ := card_torsion hL P x hK
  have c₂ := card_torsion hL P x' hΩ
  have : Finite {y : Over.mk x' ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {y : Over.mk x ⟶ P.A // y ^ n = 1} → {y : Over.mk x' ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨u ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (comp_injective u _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

end GlobalTheory.TorsionFieldExt

namespace GlobalTheory


open TorsionFieldExt in
theorem torsion_points_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  intro hL S P K Ω _ _ _ i x
  refine ⟨comp_injective _ _, fun n z hn hz => ?_⟩
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let v : Over.mk (spMap j ≫ spMap i ≫ x) ⟶ Over.mk (spMap i ≫ x) := Over.homMk (spMap j) rfl
  have hn' : (n : AlgebraicClosure Ω) ≠ 0 := by
    rw [← map_natCast (j.comp i)]
    exact (map_ne_zero _).2 hn
  obtain ⟨y, hy, e⟩ := exists_of_isAlgClosed hL P
    (v ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x)) hn hn' (v ≫ z)
    (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
  exact ⟨y, hy, comp_injective v _ ((Category.assoc _ _ _).symm.trans e)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.VerticalDeriv

open GlobalTheory.FibreDeriv

variable {g : ℕ} {X Z : Scheme.{0}}

theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (H' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at H H'
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have h := (top_le_preimage_eps v _ H.1 U).2 h0
  have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
  exact TangentOrigin.ext_evalPt hU h h' (RingHom.ext fun f => (H.2 U h f).trans (H'.2 U h' f).symm)

theorem exists_isDerivAt0 {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol (Set.mem_univ _) h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

theorem isDerivAt0_vertical (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z} (H : IsDerivAt0 e w v) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := by
  have h1 := isDerivAt0_comp H p
  simp only [he] at h1
  exact isDerivAt0_unique h1 (LocalLift.isDerivAt0_const (fun _ => x) w fun U f _ => by simp)

theorem isDerivAt0_snd {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) {U : Z.Opens} {n : ℕ}
    (t : Fin n → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (h : ⊤ ≤ v ⁻¹ᵁ U) (i : Fin n) :
    (TangentOrigin.evalPt v U h (t i)).snd = fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 w i := by
  rw [fderiv_pi fun i => LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0 (t i)]
  exact H.2 U h (t i)

theorem bijective_iff_injective (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    (hol : IsHolTo Set.univ e) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U)
    (hun : ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' →
      (∀ i, TangentOrigin.evalPt v U h (t i) = TangentOrigin.evalPt v' U h' (t i)) → v = v') :
    (∀ v : Sp (DualNumber ℂ) ⟶ Z, v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∃! w, IsDerivAt0 e w v) ↔
      Function.Injective (fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0) := by
  set T := fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 with hT
  have key : ∀ (v : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∀ w,
      (IsDerivAt0 e w v ↔ T w = fun i => (TangentOrigin.evalPt v U h (t i)).snd) := by
    intro v h hv hv0 w
    refine ⟨fun H => funext fun i => (isDerivAt0_snd hol t h0 H h i).symm, fun H => ?_⟩
    obtain ⟨v', H'⟩ := exists_isDerivAt0 hol w
    have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
    rw [hun v v' h h' (hv.trans (isDerivAt0_vertical p x he H').symm) (hv0.trans H'.1.symm) fun i => ?_]
    · exact H'
    · refine TrivSqZeroExt.ext ((fst_evEps v _ hv0 U h _).trans (fst_evEps v' _ H'.1 U h' _).symm) ?_
      rw [isDerivAt0_snd hol t h0 H' h' i]
      exact (congrFun H i).symm
  constructor
  · intro H w w' hw
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    have h := (top_le_preimage_eps v _ Hv.1 U).2 h0
    have hv := isDerivAt0_vertical p x he Hv
    exact (H v hv Hv.1).unique Hv ((key v h hv Hv.1 w').2 (hw.symm.trans ((key v h hv Hv.1 w).1 Hv)))
  · intro H v hv hv0
    have h := (top_le_preimage_eps v _ hv0 U).2 h0
    simp only [key v h hv hv0]
    have hs : Function.Surjective T := (LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 H
    exact (Function.bijective_iff_existsUnique T).1 ⟨H, hs⟩ _

end GlobalTheory.VerticalDeriv

namespace GlobalTheory


open VerticalDeriv in
theorem vertical_derivative_in_coordinates :
    ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)) := by
  intro X G x g e hol
  have he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x := fun z => Over.w (e z)
  refine ⟨fun w => ?_, fun U t h0 hun => ?_⟩
  · obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    exact ⟨Over.homMk v (isDerivAt0_vertical G.hom x he Hv), Hv,
      fun v' Hv' => Over.OverMorphism.ext (isDerivAt0_unique Hv' Hv)⟩
  · refine Iff.trans ?_ (bijective_iff_injective G.hom x he hol U t h0 hun)
    exact ⟨fun H v hv hv0 => H (Over.homMk v hv) hv0, fun H v hv0 => H v.left (Over.w v) hv0⟩

end GlobalTheory
end
end

