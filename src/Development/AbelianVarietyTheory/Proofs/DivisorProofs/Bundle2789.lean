module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicFormEqRationalPhaseKernelSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneTheoryVEqVerschiebungInjective
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem theory_V_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
    Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧
      (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) = T.map (verschiebung (p_eq_zero p k) G) m) ∧
      (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[WittVector p k] T.M G),
        (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), T.map f (T.V H m) = T.V G (T.map f m) := by
  intro p _ T k _ _ _ G

  have tor : ∀ (K : PDivGroup p k) (m : T.M K), p • m = 0 → m = 0 := by
    intro K m hm
    exact T.base.eq_zero_of_pow_smul (G := K) trivial 1 m (by simpa only [pow_one] using hm)
  have Finj : ∀ K : PDivGroup p k, Function.Injective (T.F K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.V_F K x, ← T.V_F K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have Vinj : ∀ K : PDivGroup p k, Function.Injective (T.V K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.F_V K x, ← T.F_V K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have comm : ∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G),
      (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m) := by
    intro H φ hφ m
    apply Finj G
    rw [← hφ, T.F_V H m, T.F_V G, map_nsmul]
  refine ⟨Finj G, Vinj G, ?_, comm, ?_⟩
  · intro m
    have ht := frobTwist_module p T.base k G
    obtain ⟨n, hn⟩ := ht.1.2 (T.map (verschiebung (p_eq_zero p k) G) m)
    have hF : T.F G n = p • m := ht.2.2 m n hn
    have : n = T.V G m := Finj G (by rw [hF, T.F_V])
    rw [← this]; exact hn
  · intro H f m
    exact comm H (T.map f) (T.base.map_F trivial trivial f) m

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingThetaConstantsGenerateIntegralTorsionLab
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.IntLabel

section
variable {G X : Type} [AddCommGroup G] [AddCommGroup X] {N : ℕ} {Y : G → (Fin 8 → X) → Prop}

theorem yy_zero (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) : Y 0 0 := by
  obtain ⟨mu, hmu⟩ := h1 0
  have h2 := h4 0 0 mu mu hmu hmu
  rw [add_zero] at h2
  have hc := (h3 0 mu (mu + mu) hmu).1 h2
  refine (h3 0 mu 0 hmu).2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  have e : mu v = N • w := add_left_cancel (a := mu v) (by simpa using hw)
  exact ⟨-w, by simp [e]⟩

theorem yy_neg (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (-a) (-mu) := by
  obtain ⟨mu', h'⟩ := h1 (-a)
  have h0 := h4 a (-a) mu mu' ha h'
  rw [add_neg_cancel] at h0
  have hc := (h3 0 0 (mu + mu') (yy_zero h1 h3 h4)).1 h0
  refine (h3 (-a) mu' (-mu) h').2 fun v => ?_
  obtain ⟨w, hw⟩ := hc v
  simp only [Pi.add_apply, Pi.zero_apply, zero_add] at hw
  refine ⟨-w, ?_⟩
  simp only [Pi.neg_apply, smul_neg]
  rw [← hw]
  abel

theorem yy_sub (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a b : G} {mu nu : Fin 8 → X} (ha : Y a mu)
    (hb : Y b nu) : Y (a - b) (mu - nu) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h4 _ _ _ _ ha (yy_neg h1 h3 h4 hb)

theorem yy_nsmul (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (k : ℕ) {a : G} {mu : Fin 8 → X} (ha : Y a mu) :
    Y (k • a) (k • mu) := by
  induction k with
  | zero => simpa using yy_zero h1 h3 h4
  | succ k ih => rw [succ_nsmul, succ_nsmul]; exact h4 _ _ _ _ ih ha

theorem mem_closure_iff (p J : ℕ) (hJ : 2 ≤ J) (hN : N = p ^ J) (hG : ∀ a : G, N • a = 0)
    (htor : ∀ b : G, p • b = 0 → ∃ c, b = p ^ (J - 1) • c) (htf : ∀ x : X, p ^ (J - 1) • x = 0 → x = 0)
    (h1 : ∀ a, ∃ mu, Y a mu) (h2 : ∀ mu, ∃ a, Y a mu)
    (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ ∀ v, CongMod N (mu' v) (mu v)))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (S : Set G) (hS : ∀ a ∈ S, Y a 0)
    (hT : ∀ a, Y a 0 → ∃ b, p • b = 0 ∧ a + b ∈ S) (a : G) : a ∈ AddSubgroup.closure S ↔ Y a 0 := by
  constructor
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact yy_zero h1 h3 h4
    | add x y _ _ hx hy => simpa using h4 x y 0 0 hx hy
    | neg x _ hx => simpa using yy_neg h1 h3 h4 hx
  · intro ha
    obtain ⟨b, hb, hab⟩ := hT a ha
    have hYb : Y b 0 := by simpa using yy_sub h1 h3 h4 (hS _ hab) ha
    obtain ⟨c, rfl⟩ := htor b hb
    obtain ⟨muc, hc⟩ := h1 c
    have hcong := (h3 _ _ _ (yy_nsmul h1 h3 h4 (p ^ (J - 1)) hc)).1 hYb
    have hw : ∀ v, ∃ w : X, muc v = p • w := by
      intro v
      obtain ⟨w, hw⟩ := hcong v
      simp only [Pi.zero_apply, Pi.smul_apply] at hw
      refine ⟨-w, ?_⟩
      have e : p ^ (J - 1) • (muc v + p • w) = 0 := by
        rw [smul_add, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN]
        exact hw.symm
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact htf _ e
    choose w hw using hw
    have hmu : muc = p • w := funext fun v => by simp [hw v]
    obtain ⟨c', hc'⟩ := h2 w
    have hk : Y (c - p • c') 0 := by
      have := yy_sub h1 h3 h4 hc (yy_nsmul h1 h3 h4 p hc')
      rwa [← hmu, sub_self] at this
    obtain ⟨bk, hbk, hkS⟩ := hT _ hk
    have hbk0 : p ^ (J - 1) • bk = 0 := by
      obtain ⟨e, he⟩ : ∃ e, J - 1 = e + 1 := ⟨J - 2, by omega⟩
      rw [he, pow_succ, mul_smul, hbk, smul_zero]
    have key : p ^ (J - 1) • c = p ^ (J - 1) • ((c - p • c') + bk) := by
      rw [smul_add, hbk0, add_zero, smul_sub, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN, hG, sub_zero]
    have hbcl : p ^ (J - 1) • c ∈ AddSubgroup.closure S := by
      rw [key]; exact nsmul_mem (AddSubgroup.subset_closure hkS) _
    have e : a = (a + p ^ (J - 1) • c) - p ^ (J - 1) • c := by abel
    rw [e]
    exact sub_mem (AddSubgroup.subset_closure hab) hbcl

theorem zmod_tors {p J M : ℕ} (hp : 0 < p) (hJ : 1 ≤ J) (hM : M = p ^ J) (x : ZMod M) (hx : p • x = 0) :
    ∃ y : ZMod M, x = p ^ (J - 1) • y := by
  subst hM
  haveI : NeZero (p ^ J) := ⟨pow_ne_zero _ hp.ne'⟩
  have h1 : p ^ J ∣ p * x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ J)) (p ^ J)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    rwa [nsmul_eq_mul] at hx
  have h2 : p ^ (J - 1) ∣ x.val := by
    have e : p ^ J = p * p ^ (J - 1) := by rw [← pow_succ']; congr 1; omega
    have h1' : p * p ^ (J - 1) ∣ p * x.val := by rw [← e]; exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hp h1'
  obtain ⟨q, hq⟩ := h2
  refine ⟨(q : ZMod (p ^ J)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hq, nsmul_eq_mul]
  push_cast
  ring

end
end GlobalTheory.Poinc.Sep.IntLabel

namespace GlobalTheory.Poinc.Sep


open GlobalTheory.Poinc.Sep.IntLabel in
theorem mem_HH_iff_yy_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev X _ m t δ 𝔪 a
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨j, hj, hr⟩ := X₁.ρ.r_eq
  have hp : 0 < X₁.ρ.n := X₁.ρ.n_prime.pos
  have hk := X₁.ρ.two_le
  have hN : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j + X₁.ρ.k * 2) := by rw [hr, X₁.ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + X₁.ρ.k * 2 := by omega
  have hG : ∀ b : X₁.S.Gam, (X₁.S.r * X₁.S.N) • b = 0 := fun b => by
    funext v
    simp [nsmul_eq_mul]
  have htor : ∀ b : X₁.S.Gam, X₁.ρ.n • b = 0 → ∃ c : X₁.S.Gam, b = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • c := by
    intro b hb
    have hv : ∀ v, ∃ y : ZMod (X₁.S.r * X₁.S.N), b v = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • y := fun v =>
      zmod_tors hp (by omega) hN (b v) (by simpa using congrFun hb v)
    choose c hc using hv
    exact ⟨c, funext fun v => by simpa using hc v⟩
  have htf : ∀ x : X, X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • x = 0 → x = 0 := by
    intro x hx
    have hq : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) ≠ 0 := pow_ne_zero _ hp.ne'
    have hs : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • (Pi.single 0 x : Fin 8 → X) = 0 := by
      funext v
      by_cases hv : v = 0
      · subst hv; simp [hx]
      · simp [Pi.single_apply, hv]
    have he : ((X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) : ℕ) : ℤ) • 𝔪.e₈ (Pi.single 0 x) = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hs, map_zero]
    have h0 : 𝔪.e₈ (Pi.single 0 x) = 0 := (smul_eq_zero.1 he).resolve_left (by exact_mod_cast hq)
    have h0' : (Pi.single 0 x : Fin 8 → X) = 0 := 𝔪.e₈.injective (h0.trans (map_zero _).symm)
    simpa using congrFun h0' 0
  rw [ThetaSys.HH]
  exact mem_closure_iff (X₁.ρ.n) (j + X₁.ρ.k * 2) hJ hN hG htor htf h1 h2 h3 h4 _
    (fun b hb => _root_.GlobalTheory.Poinc.Sep.DivInt.label_zero_of_mem_supI g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 b hb)
    (fun b hb => _root_.GlobalTheory.Poinc.Sep.TorTrans.exists_translate_mem_supI g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hx₀ b hb) a

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isLocalizedModule_ratTensor (M : Type) [AddCommGroup M] :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 (TensorProduct.isBaseChange ℤ M ℚ)

theorem toEnd0_apply {K : Type} [Field K] (A : AbVar K) (f : End A) :
    toEnd0 A f = TensorProduct.mk ℤ ℚ (End A) 1 f := rfl

theorem toEnd0_injective_and_fraction : ∀ (K : Type) [Field K] (A : AbVar K),
    Function.Injective (toEnd0 A) ∧ ∀ x : End0 A, ∃ (n : ℕ) (f : End A), 0 < n ∧ n • x = toEnd0 A f := by
  intro K _ A
  haveI := isLocalizedModule_ratTensor (End A)
  refine ⟨fun f g h => ?_, fun x => ?_⟩
  · rw [toEnd0_apply, toEnd0_apply] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) h
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    have h1 : (c : ℤ) • (f - g) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [Submonoid.smul_def] using hc
    apply sub_eq_zero.1
    apply End.addEquiv.injective
    apply _root_.GlobalTheory.AV.AbVar.hom_torsionFree K A A (c : ℤ) _ hc0
    have hh := congrArg (End.addEquiv (X := A)) h1
    rw [map_zsmul, map_zero] at hh
    exact hh
  · obtain ⟨⟨m, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End A) 1) x
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    simp only [Submonoid.smul_def] at hc
    rcases Int.natAbs_eq (c : ℤ) with h | h
    · refine ⟨(c : ℤ).natAbs, m, Int.natAbs_pos.2 hc0, ?_⟩
      rw [toEnd0_apply, ← hc, ← natCast_zsmul, ← h]
    · refine ⟨(c : ℤ).natAbs, -m, Int.natAbs_pos.2 hc0, ?_⟩
      have h' : (((c : ℤ).natAbs : ℕ) : ℤ) = -(c : ℤ) := by omega
      rw [toEnd0_apply, map_neg, ← hc, ← natCast_zsmul, h', neg_smul]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeEqRigidifiedExtensionPullStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_eq_rigidifiedExtensionPullback : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' : PDivGroup p k') (G : PDivGroup p k) (h' : G'.IsEt) (h : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G h) (l' : Mod B G' h'), IsTr B σ h' h s l l' → red B G' h' l' = s.rig (red B G h l) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.red_of_isTr | exact GlobalTheory.Dieu.EtFromConn.red_of_isTr | (intros; apply GlobalTheory.Dieu.EtFromConn.red_of_isTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicFormEqRationalPhaseKernelSeriesStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicForm_eq_rationalPhase_kernelSeries : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (t : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RatHyp T Rl F κ v₀ O t j hV →
  ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
  ∀ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) →
  ∀ ph : ℂ, IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph →
  ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) χ ξR ω φ,
    KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ →
  ∀ h ∈ GfC (Vc D j), ∀ P ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) (fin (Vc D j) h)),
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = ph • singleSeries Rl.toRealDat j ω φ h (c0L j P) u := by
  first | exact @GlobalTheory.KerPhase.exists_adForm_eq_phase_smul | exact GlobalTheory.KerPhase.exists_adForm_eq_phase_smul | (intros; apply GlobalTheory.KerPhase.exists_adForm_eq_phase_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleEffectiveKltInductionStart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.PairStep


set_option maxHeartbeats 1000000 in
theorem exists_ample_eff_kltAt_start : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (β : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → 0 < β →
      ∃ (A F : CartierDiv X) (a : ℕ), IsAmpleLB (toLB A) ∧ 0 < a ∧ toPic F = a • cls N₀ hN₀ ∧
        ∃ (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ lam < β ∧
          (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧ ∀ y, KltAt p n (Δ + qWeil D₀ m') y := by
  intro hPr X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, hA⟩ := toPic_surjective (cls H hH.isLB)
  have hAamp : IsAmpleLB (toLB A) := by
    rw [toPic_apply] at hA
    exact hH.of_lbIso (isLB_toLB A) ((cls_eq_iff (isLB_toLB A) hH.isLB).1 hA)
  obtain ⟨a, E₀, ha, hE₀, hKod⟩ := GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig ℂ X p hp N₀ (toLB A) hbig hAamp
  obtain ⟨F, hF⟩ := toPic_surjective (a • cls N₀ hN₀)
  obtain ⟨m, G, hm, hG⟩ := _root_.GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt X p n hp hn Δ hΔ hklt
  have hB : IsQCart (qWeil E₀ 1) := ⟨1, E₀, one_pos, hE₀, rfl⟩
  obtain ⟨c₀, hc₀, hc₀k⟩ := _root_.GlobalTheory.PairStep.exists_pos_kltAt_add_smul hPr X p n hp hn Δ m G (qWeil E₀ 1) hm hG hklt hB
  set q : ℕ := ⌈1 / c₀ + (a : ℚ) * r / β⌉₊ + 1 with hq
  have hqpos : (0 : ℚ) < q := by positivity
  have hqgt : 1 / c₀ + (a : ℚ) * r / β < q := by
    have := Nat.le_ceil (1 / c₀ + (a : ℚ) * r / β)
    rw [hq]; push_cast; linarith
  have hara : (0 : ℚ) ≤ (a : ℚ) * r / β := by positivity
  have hinv : (0 : ℚ) < 1 / c₀ := by positivity
  have h1 : 1 / (q : ℚ) ≤ c₀ := by
    rw [div_le_iff₀ hqpos]
    have : 1 / c₀ < q := by linarith
    rw [div_lt_iff₀ hc₀] at this
    linarith
  have h2 : (a : ℚ) * r / q < β := by
    have : (a : ℚ) * r / β < q := by linarith
    rw [div_lt_iff₀ hβ] at this
    rw [div_lt_iff₀ hqpos]
    linarith
  refine ⟨A, F, a, hAamp, ha, hF, (a : ℚ) * r / q, 1 / q, q, E₀, by omega, hE₀, by positivity, h2, ?_, ?_⟩
  · intro C hC
    have e1 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) (toLB A) (toLB E₀)
      (isLB_lbPow hN₀ a) (isLB_toLB A) (isLB_toLB E₀) 1 1 C hC (by
        rw [cls_lbPow hN₀ a, one_smul, one_smul, ← toPic_apply]
        exact hKod)
    have e2 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) N₀ N₀
      (isLB_lbPow hN₀ a) hN₀ hN₀ a 0 C hC (by rw [cls_lbPow hN₀ a, zero_smul, add_zero])
    have e3 : (interNumRed ℂ C ![toLB E₀] : ℚ) = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
      have : interNumRed ℂ C ![toLB E₀] = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
        rw [e2] at e1; push_cast at e1; linarith
      exact_mod_cast this
    rw [e3]
    have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  · intro y
    have k := (kltAt_lcAt_of_le_coeff X p n hp hn Δ (qWeil E₀ 1) (1 / q) c₀ y hB h1).1 (hc₀k y)
    convert k using 2
    ext z
    simp [qWeil, div_eq_mul_inv, mul_comm]

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasepointFreeSectionTupleAmpleArithStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∃ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x := by
  first | exact @GlobalTheory.HSAmp.NoethGens.exists_gens | exact GlobalTheory.HSAmp.NoethGens.exists_gens | (intros; apply GlobalTheory.HSAmp.NoethGens.exists_gens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfPullbackNmulCoboundary
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Katz.exists_coboundary_of_pullback_nmul_coboundary' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ → cob1 μ B = pull2 (nmul μ p) κ → c.ev 1 B = 0 → ∃ s, κ = cob1 μ s := by
  intro p _ k _ d G c μ hμ κ B hκ hB h1
  have hcoc : ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := _root_.GlobalTheory.Katz.isCoc_iff_mem_cocycles p k d G c μ hμ
  have hlaw := (GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ
  have hfun := _root_.GlobalTheory.Katz.Chart.functions_are_series p k d G c
  have hsq := (_root_.GlobalTheory.chart_square_presents p k d G c).2
  have hmap := ((_root_.GlobalTheory.Katz.isMapOf_existsUnique_and p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (_root_.GlobalTheory.Katz.Chart.isMapOf_nmul p k d G c μ hμ p)).2
  let cz : G.cocycles := ⟨fun n => c.ev₂ n κ, (hcoc κ).1 hκ⟩
  let bB : G.funs := ⟨fun n => c.ev n B, fun n => hfun.1 n B⟩
  have key : G.cob bB = cocyclesMap ((p : ℤ_[p]) • 𝟙 G) cz := by
    apply Subtype.ext; funext n
    change cobOne k _ (c.ev n B) = pullbackTwo (((p : ℤ_[p]) • 𝟙 G).app n) (c.ev₂ n κ)
    rw [← (hlaw.2 n B).2, hB, (hmap n).2 κ]
  obtain ⟨b', hb'⟩ := _root_.GlobalTheory.cocycle_mem_range_cob_of_pullback_mulP G cz bB key h1
  obtain ⟨s, hs, -⟩ := hfun.2.2 b'.1 b'.2
  refine ⟨s, ?_⟩
  obtain ⟨t, -, ht⟩ := hsq (fun n => c.ev₂ n κ) (fun n => hfun.2.1 n κ)
  have e1 := ht κ (fun n => rfl)
  have e2 := ht (cob1 μ s) (fun n => by
    rw [(hlaw.2 n s).2, hs n]
    exact congrArg (fun x : G.cocycles => x.1 n) hb')
  exact e1.trans e2.symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteUnitaryRationalOfIsOpenStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (L : Subgroup (finU (E := E) (n := n))), IsOpen (L : Set (finU (E := E) (n := n))) → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (L : Set (finU (E := E) (n := n)))) := by
  first | exact @GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | exact GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen | (intros; apply GlobalTheory.BCT.finite_doubleCoset_ratFinU_isOpen <;> assumption)
end

