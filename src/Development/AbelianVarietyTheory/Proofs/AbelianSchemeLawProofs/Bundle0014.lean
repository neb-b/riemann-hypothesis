module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbLaw.PowVanish

section Descent

variable {X Y Z : Scheme.{0}}

def pb (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ h ⁻¹ᵁ U) : Γ(X, U) →+* Γ(Y, W) :=
  (h.appLE U W e).hom

theorem pre_mono (h : Y ⟶ X) {U U' : X.Opens} (i : U ≤ U') : h ⁻¹ᵁ U ≤ h ⁻¹ᵁ U' := fun _ hy => i hy

theorem pre_inf (h : Y ⟶ X) (U U' : X.Opens) : h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ U' ≤ h ⁻¹ᵁ (U ⊓ U') := fun _ hy => hy

theorem pre_inf' (h : Y ⟶ X) (U U' : X.Opens) : h ⁻¹ᵁ (U ⊓ U') ≤ h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ U' := fun _ hy => hy

theorem pre_comp (g : Z ⟶ Y) (h : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (e' : W ≤ g ⁻¹ᵁ V) : W ≤ (g ≫ h) ⁻¹ᵁ U := fun _ hy => e (e' hy)

theorem pre_pull (M : LB X) (f : Y ⟶ X) (i j : M.ι) {W : Y.Opens}
    (e : W ≤ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j)) : W ≤ f ⁻¹ᵁ (M.U i ⊓ M.U j) :=
  fun _ hy => ⟨mem_pull.1 (e hy).1, mem_pull.1 (e hy).2⟩

theorem rs_pb (h : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (e : W ≤ h ⁻¹ᵁ U) (i : W' ≤ W) (x : Γ(X, U)) :
    rs Y i (pb h e x) = pb h (i.trans e) x :=
  congrArg (fun q => q.hom x) (h.appLE_map e (homOfLE i).op)

theorem pb_rs (h : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (e : W ≤ h ⁻¹ᵁ U) (i : U ≤ U') (x : Γ(X, U')) :
    pb h e (rs X i x) = pb h (e.trans (pre_mono h i)) x :=
  congrArg (fun q => q.hom x) (h.map_appLE e (homOfLE i).op)

theorem pb_pb (g : Z ⟶ Y) (h : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens} (e : V ≤ h ⁻¹ᵁ U)
    (e' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)) :
    pb g e' (pb h e x) = pb (g ≫ h) (pre_comp g h e e') x :=
  congrArg (fun q => q.hom x) (Scheme.Hom.appLE_comp_appLE g h U V W e e')

theorem pb_congr {h h' : Y ⟶ X} (H : h = h') {U : X.Opens} {W : Y.Opens} (e : W ≤ h ⁻¹ᵁ U)
    (x : Γ(X, U)) : pb h e x = pb h' (H ▸ e) x := by
  subst H; rfl

theorem app_eq_pb (h : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)) : (h.app U).hom x = pb h le_rfl x := by
  rw [pb, Scheme.Hom.appLE_eq_app]

theorem rs_pull_g (M : LB X) (f : Y ⟶ X) (i j : M.ι) {W : Y.Opens}
    (e : W ≤ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j)) :
    rs Y e ((M.pull f).g (fun _ => i) (fun _ => j)).val =
      pb f (pre_pull M f i j e) (M.g i j).val := by
  change rs Y e (∏ _k : PUnit, (res _ (pullU f _ (M.g i j))) ^ (1 : ℤ)).val = _
  rw [Fintype.prod_unique, zpow_one]
  change rs Y e (rs Y _ ((f.app _).hom (M.g i j).val)) = _
  rw [app_eq_pb]
  exact (congrArg (rs Y e) (rs_pb f _ _ _)).trans (rs_pb f _ _ _)

theorem first_cohomology_vanishes_descent (f : Y ⟶ X) (M : LB X) (G : Type) [Group G] [Fintype G] (τ : G → (Y ⟶ Y))
    (hτ : ∀ y, τ y ≫ f = f) (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    (hu : IsUnit ((Fintype.card G : ℕ) : Γ(X, ⊤)))
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
    (H : FirstCohomologyVanishes (M.pull f)) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  have inv : ∀ y (U : X.Opens), f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U) := fun y U => by
    rw [← Scheme.Hom.comp_preimage, hτ]
  have pinv : ∀ y {U : X.Opens} {W W' : Y.Opens} (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ τ y ⁻¹ᵁ W)
      (e'' : W' ≤ f ⁻¹ᵁ U) (x : Γ(X, U)), pb (τ y) e' (pb f e x) = pb f e'' x := fun y U W W' e e' e'' x => by
    rw [pb_pb, pb_congr (hτ y)]
  have inj : ∀ (U : X.Opens) (a b : Γ(X, U)), pb f le_rfl a = pb f le_rfl b → a = b := fun U a b hab =>
    (hgal U (pb f le_rfl a) (fun y e => pinv y _ _ _ a)).unique (app_eq_pb f U a)
      ((app_eq_pb f U b).trans hab.symm)
  obtain ⟨ψ, hψ⟩ := H I (fun a => f ⁻¹ᵁ V a) (fun a _ => c a) (fun a => le_pull M f (hV a))
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl)
    (fun a b => pb f (pre_inf f (V a) (V b)) (φ a b)) (fun a b d => by
      have h := congrArg (pb f (U := V a ⊓ V b ⊓ V d) (W := f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ⊓ f ⁻¹ᵁ V d)
        ((inf_le_inf_right _ (pre_inf f _ _)).trans (pre_inf f _ _))) (hφ a b d)
      simp only [map_add (f := _), map_mul, pb_rs] at h
      simp only [rs_pb, rs_pull_g]
      exact h)
  have hχ : ∀ a, ∃ χ : Γ(X, V a), pb f le_rfl χ = ∑ y, pb (τ y) (inv y (V a)) (ψ a) := fun a => by
    obtain ⟨χ, h, -⟩ := hgal (V a) (∑ y, pb (τ y) (inv y (V a)) (ψ a)) (fun z e => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun y => ?_
      rw [pb_pb, pb_congr (hmul z y)]
      rfl)
    exact ⟨χ, (app_eq_pb f _ χ).symm.trans h⟩
  choose χ hχ using hχ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  refine ⟨fun a => rs X le_top u * χ a, fun a b => ?_⟩
  have key : ((Fintype.card G : ℕ) : Γ(X, V a ⊓ V b)) * φ a b = rs X inf_le_left (χ a) -
      rs X (inf_le_inf (hV a) (hV b) : V a ⊓ V b ≤ M.U (c a) ⊓ M.U (c b)) (M.g (c a) (c b)).val *
        rs X inf_le_right (χ b) := by
    apply inj
    have la : f ⁻¹ᵁ (V a ⊓ V b) ≤ f ⁻¹ᵁ V a := pre_mono f inf_le_left
    have lb : f ⁻¹ᵁ (V a ⊓ V b) ≤ f ⁻¹ᵁ V b := pre_mono f inf_le_right
    have ha := congrArg (rs Y la) (hχ a)
    have hb := congrArg (rs Y lb) (hχ b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, rs_pb] at ha hb
    simp only [map_sub, map_mul, map_natCast, pb_rs]
    rw [ha, hb, Finset.mul_sum, ← Finset.sum_sub_distrib, ← nsmul_eq_mul, ← Finset.card_univ,
      ← Finset.sum_const]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h := congrArg (pb (τ y) (U := f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b) (W := f ⁻¹ᵁ (V a ⊓ V b))
      ((inv y (V a ⊓ V b)).trans (pre_mono _ (pre_inf' f _ _)))) (hψ a b)
    simp only [map_sub, map_mul, pb_rs, rs_pull_g] at h
    rw [pinv y _ _ le_rfl, pinv y _ _ (pre_mono f (inf_le_inf (hV a) (hV b)))] at h
    exact h
  have hu' := congrArg (rs X (le_top : V a ⊓ V b ≤ ⊤)) hu
  simp only [map_mul, map_natCast, map_one] at hu'
  simp only [map_mul, rs_rs]
  linear_combination (rs X (le_top : V a ⊓ V b ≤ ⊤) u) * key - φ a b * hu'

end Descent

theorem exists_iso_tw {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : X ⟶ X) (k n r N t : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![k, -1])) (hα : α.IsGen) (h : k * n = r + N * t) :
    ∃ w : LB.Iso ((pw L n).pull f) ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)), w.IsGen := by
  have l₁ : ∀ (p : PUnit → L.ι × (PUnit → L.ι)) (q : PUnit → L.ι),
      ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)).U p ⊓ ((pw L n).pull f).U q ≤
        LB.wchart L (K := Fin 2) ![𝟙 X, f] ![(p PUnit.unit).1, q PUnit.unit] := fun p q y hy =>
    Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact (mem_pull.1 hy.1).1
      · exact mem_pull.1 hy.2
  have l₂ : ∀ (p : PUnit → L.ι × (PUnit → L.ι)) (q : PUnit → L.ι),
      ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)).U p ⊓ ((pw L n).pull f).U q ≤
        L.U ((p PUnit.unit).2 PUnit.unit) ⊓ L.U (p PUnit.unit).1 := fun p q y hy =>
    ⟨mem_pull (L := L) (F := 𝟙 X).1 (mem_pull.1 hy.1).2, (mem_pull.1 hy.1).1⟩
  refine ⟨⟨fun p => res (l₁ p.1 p.2) (α.s _) ^ n * res (l₂ p.1 p.2) (L.g _ _) ^ (N * t)⟩,
    fun p q => unit_ext fun y hy => ?_⟩
  have val : ∀ (p : PUnit → L.ι × (PUnit → L.ι)) (q : PUnit → L.ι),
      y ∈ ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)).U p ⊓ ((pw L n).pull f).U q →
      gm (𝟙 X) y _ (res (l₁ p q) (α.s _) ^ n * res (l₂ p q) (L.g _ _) ^ (N * t)) =
        gm (𝟙 X) y (LB.wchart L (K := Fin 2) ![𝟙 X, f] ![(p PUnit.unit).1, q PUnit.unit]) (α.s _) ^ n *
          gm (𝟙 X) y _ (L.g ((p PUnit.unit).2 PUnit.unit) (p PUnit.unit).1) ^ (N * t) := fun p q hp => by
    rw [map_mul, map_zpow, map_zpow]
    exact congrArg₂ (fun a b => a ^ n * b ^ (N * t)) (gm_res _ y (l₁ p q) hp _) (gm_res _ y (l₂ p q) hp _)
  refine ((gm_res (𝟙 X) y _ hy _).trans (val p.1 p.2 hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div _ _ (𝟙 X) y p q hy)
    ((gm_res (𝟙 X) y _ hy _).trans (val q.1 q.2 hy.2)))).trans ?_
  have hp := l₂ _ _ hy.1
  have hq := l₂ _ _ hy.2
  have e₁ := gen_trans hα (𝟙 X) y (l₁ _ _ hy.1) (l₁ _ _ hy.2)
  have e₂ := gm_pull_g (pw L n) f (𝟙 X) y p.2 q.2 hy.1.2 hy.2.2
  have e₃ := gm_pull_g (tw (pw L r) (pw (L.pull (𝟙 X)) N) t) (𝟙 X) (𝟙 X) y p.1 q.1 hy.1.1 hy.2.1
  have e₄ : gm (𝟙 X ≫ 𝟙 X) y _ ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).g (p.1 PUnit.unit) (q.1 PUnit.unit)) =
      gm (𝟙 X) y _ (L.g (p.1 PUnit.unit).1 (q.1 PUnit.unit).1) ^ r *
        (gm (𝟙 X) y _ (L.g ((p.1 PUnit.unit).2 PUnit.unit) ((q.1 PUnit.unit).2 PUnit.unit)) ^ (N * t)) := by
    rw [Category.comp_id]
    refine (gm_div _ _ (𝟙 X) y (p.1 PUnit.unit) (q.1 PUnit.unit) ⟨mem_pull.1 hy.1.1, mem_pull.1 hy.2.1⟩).trans ?_
    refine congrArg₂ (· * ·) (map_zpow _ _ _) ?_
    have e := gm_pull_g L (𝟙 X) (𝟙 X) y (p.1 PUnit.unit).2 (q.1 PUnit.unit).2 (mem_pull.1 hy.1.1).2
      (mem_pull.1 hy.2.1).2
    rw [Category.comp_id] at e
    rw [← e, zpow_mul, ← inv_inv ((_ ^ N) ^ t), ← zpow_neg]
    exact congrArg (·⁻¹) ((map_zpow _ _ _).trans (congrArg (· ^ (-t)) (map_zpow _ _ _)))
  have e₅ : gm (𝟙 X ≫ f) y _ ((pw L n).g (p.2 PUnit.unit) (q.2 PUnit.unit)) =
      gm (𝟙 X ≫ f) y _ (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)) ^ n := map_zpow _ _ _
  have c₁ := gm_cocycle hL (𝟙 X) y hp.1 hp.2 hq.2
  have c₂ := gm_cocycle hL (𝟙 X) y hp.1 hq.1 hq.2
  have e₆ : trF (L := L) (K := Fin 2) ![𝟙 X, f] ![k, -1] (𝟙 X) y ![(p.1 PUnit.unit).1, p.2 PUnit.unit]
      ![(q.1 PUnit.unit).1, q.2 PUnit.unit] =
      gm (𝟙 X) y _ (L.g (p.1 PUnit.unit).1 (q.1 PUnit.unit).1) ^ k *
        (gm (𝟙 X ≫ f) y _ (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)))⁻¹ := by
    rw [trF, Fin.prod_univ_two, ← zpow_neg_one]
    exact congrArg₂ (· * ·) (congrArg (fun s => gm s y _ _ ^ k) (Category.comp_id (𝟙 X))) rfl
  refine (congrArg₂ (· * ·) (congrArg₂ (fun a b => a * b⁻¹) (e₃.trans e₄) (e₂.trans e₅)) rfl).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b => a ^ n * b) (e₁.trans (congrArg₂ (· * ·) e₆ rfl)) rfl).symm
  have alg : ∀ {U : Type} [CommGroup U] (a b c d e s u : U), d * a = u → b * e = u →
      a ^ r * b ^ (N * t) * (c ^ n)⁻¹ * (s ^ n * e ^ (N * t)) = (a ^ k * c⁻¹ * s) ^ n * d ^ (N * t) := by
    intro U _ a b c d e s u h₁ h₂
    have hd : d = b * e * a⁻¹ := by rw [h₂, ← h₁, mul_inv_cancel_right]
    have hr : r = k * n - N * t := by rw [h]; ring
    subst hd hr
    simp only [mul_zpow, inv_zpow, zpow_sub, ← zpow_mul]
    simp only [_root_.mul_comm, mul_left_comm, _root_.mul_assoc]
  exact alg _ _ _ _ _ _ _ c₁ c₂

theorem first_cohomology_vanishes_powers : (∀ (S : Scheme.{0}) (P : PolAV S) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (X : Scheme.{0}) (π : X ⟶ P.A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f P.A.hom t → ∃ N : ℕ, 1 ≤ N ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (P.L.pull π) N)), (pw (P.L.pull π) N).IsLB ∧ VeryAmpleBy f (pw (P.L.pull π) N) s) → (∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ M : LB X, M.IsLB → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → FirstCohomologyVanishes (tw M H t)) → (∀ (X X' : Scheme.{0}) (e : X' ⟶ X) (M : LB X) (M' : LB X'), IsIso e → M.IsLB → M'.IsLB → (∃ w : LB.Iso M' (M.pull e), w.IsGen) → FirstCohomologyVanishes M → FirstCohomologyVanishes M') → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), (n : K) ≠ 0 → ∀ (U : P.A.left.Opens) (f : Γ(P.A.left, (mulA P.A n).left ⁻¹ᵁ U)), (∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A, y ^ n = 1 → ∀ (e : (mulA P.A n).left ⁻¹ᵁ U ≤ ((toUnit P.A ≫ y) * 𝟙 P.A).left ⁻¹ᵁ ((mulA P.A n).left ⁻¹ᵁ U)), (((toUnit P.A ≫ y) * 𝟙 P.A).left.appLE _ _ e).hom f = f) → ∃! g : Γ(P.A.left, U), ((mulA P.A n).left.app U).hom g = f) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), 1 ≤ n → FirstCohomologyVanishes (pw P.L n) := by
  intro hproj hsv hiso hmulp hfin hgal K _ _ P n hn
  classical
  haveI := P.isAb.comm
  obtain ⟨N, hN, m, s, hH, hva⟩ := hproj _ P K (𝟙 _) P.A.left (𝟙 _) P.A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩)
  choose t₀ ht₀ using fun r : ℕ => hsv K P.A.left P.A.hom _ m s hH hva (pw P.L r) (isLB_pw P.isLB r)
  let T : ℕ := (Finset.range N).sup fun r => (t₀ r).toNat
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (N * T + ringChar K + 1)
  haveI : Fact q.Prime := ⟨hqp⟩
  have hqK : (q : K) ≠ 0 := fun h0 => by
    rcases (Nat.dvd_prime hqp).1 ((ringChar.spec K q).1 h0) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  obtain ⟨α, hα⟩ := hmulp _ P q
  haveI := (hfin _ P q hqp.one_lt.le).1
  have hdiv : q ^ 2 * n = q ^ 2 * n % N + N * (q ^ 2 * n / N) := (Nat.mod_add_div _ _).symm
  have hT : T ≤ q ^ 2 * n / N := by
    rw [Nat.le_div_iff_mul_le hN]
    nlinarith [hqp.one_lt, Nat.mul_le_mul_left (q ^ 2) hn]
  have ht : t₀ (q ^ 2 * n % N) ≤ ((q ^ 2 * n / N : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2 (le_trans (Finset.le_sup (f := fun r => (t₀ r).toNat)
      (Finset.mem_range.2 (Nat.mod_lt _ hN))) hT))
  have H : FirstCohomologyVanishes ((pw P.L n).pull (mulA P.A q).left) :=
    hiso _ _ (𝟙 _) _ _ inferInstance (isLB_tw (isLB_pw P.isLB _) hH _)
      (DVR.linComb_isLB _ (isLB_pw P.isLB n) _ _)
      (exists_iso_tw P.L P.isLB _ _ n _ N _ α hα (by exact_mod_cast hdiv)) (ht₀ _ _ ht)
  let G : Subgroup (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A) := (powMonoidHom q).ker
  haveI : Finite G := finite_torsion_of_isFinite_mul K P q
  haveI : Fintype G := Fintype.ofFinite G
  have hG : IsPGroup q G := fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact g.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hG
  refine first_cohomology_vanishes_descent (mulA P.A q).left _ G (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left)
    (fun y => ?_) (fun y z => ?_) ?_ (fun U f hf => hgal K P q hqK U f fun y hy e => hf ⟨y, hy⟩ e) H
  · have hy : y.1 ^ q = 1 := y.2
    rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hj, Nat.cast_pow]
    refine IsUnit.pow _ ?_
    have := (IsUnit.mk0 _ hqK).map (cst P.A.hom ⊤)
    rwa [map_natCast] at this

end GlobalTheory.AbLaw.PowVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MulFinite

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace Polynomial

theorem exists_pow_mul_eq_zero {k R : Type} [CommRing k] [CommRing R] (hk : IsField k) (φ : k →+* R)
    (a : R) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (c b : R), IsUnit c ∧ a ^ m * (c + a * b) = 0 := by
  letI := hk.toField
  obtain ⟨p, hp, h0⟩ := ha
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hnd
  rw [X_dvd_iff] at hnd
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hnd).map φ, ?_⟩
  rw [hq, ← X_mul_divX_add q, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_X,
    eval₂_C] at h0
  rw [add_comm]
  exact h0

theorem isClosed_basicOpen {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [UniversallyClosed f] (a : Γ(Z, ⊤)) : IsClosed (Z.basicOpen a : Set Z) := by
  have hk : IsField Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨m, c, b, hc, e⟩ := exists_pow_mul_eq_zero hk _ a (isIntegral_appTop_of_universallyClosed f a)
  have : (Z.basicOpen a : Set Z) = (Z.basicOpen (c + a * b) : Set Z)ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    rw [Scheme.mem_basicOpen Z a z trivial, Scheme.mem_basicOpen Z (c + a * b) z trivial]
    let G : Γ(Z, ⊤) →+* Z.presheaf.stalk z := (Z.presheaf.germ ⊤ z trivial).hom
    change IsUnit (G a) ↔ ¬ IsUnit (G (c + a * b))
    have e' : G a ^ m * G (c + a * b) = 0 := by rw [← map_pow, ← map_mul, e, map_zero]
    constructor
    · intro h1 h2
      exact ((h1.pow m).mul h2).ne_zero e'
    · intro h2
      have hc' : IsUnit (G (c + a * b) + (- (G a * G b))) := by
        have := hc.map G
        simpa using this
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hc' with h | h
      · exact absurd h h2
      · exact isUnit_of_mul_isUnit_left ((IsUnit.neg_iff _).1 h)
  rw [this]
  exact (Z.basicOpen _).isOpen.isClosed_compl

theorem locallyQuasiFinite_of_cover {Z : Scheme.{0}} {K : Type} [Field K] (f : Z ⟶ Spec (.of K))
    [IsProper f] {I : Type} (a : I → Γ(Z, ⊤)) (hc : ⨆ i, Z.basicOpen (a i) = ⊤)
    (ha : ∀ i, IsAffineOpen (Z.basicOpen (a i))) : LocallyQuasiFinite f := by
  have : IsZariskiLocalAtSource @LocallyQuasiFinite.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyQuasiFinite.{0}) _ hc fun i => ?_
  have : IsClosedImmersion (Z.basicOpen (a i)).ι :=
    .of_isPreimmersion _ (by simpa using isClosed_basicOpen f (a i))
  have : IsAffine (Z.basicOpen (a i)).toScheme := ha i
  have : IsFinite ((Z.basicOpen (a i)).ι ≫ f) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  infer_instance

theorem isAffineHom_fromSpecResidueField (Y : Scheme.{0}) (y : Y) :
    IsAffineHom (Y.fromSpecResidueField y) := by
  refine ⟨fun U _ => ?_⟩
  by_cases h : y ∈ U
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊤ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_top _
  · have : Y.fromSpecResidueField y ⁻¹ᵁ U = ⊥ := by
      ext x; simpa using h
    rw [this]; exact isAffineOpen_bot _

theorem isUnit_gs {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

theorem gs_appLE {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (V : Z.Opens) (hle : V ≤ r ⁻¹ᵁ U)
    (h : z ∈ V) (a : Γ(Y, U)) : gs (𝟙 Z) z V ((r.appLE U V hle).hom a) = gs r z U a :=
  (gs_res (𝟙 Z) z hle h _).trans ((gs_pull (𝟙 Z) r z U (hle h) a).trans (by rw [Category.id_comp]))

theorem gs_pow {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem pow_aux {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e N : ℕ) :
    ((g ^ N).val * x) ^ e * ((g ^ e * t)⁻¹).val ^ N = x ^ e * (t⁻¹).val ^ N := by
  have h : ((g ^ N) ^ e * ((g ^ e * t)⁻¹) ^ N) = (t⁻¹) ^ N := by
    rw [mul_inv, mul_pow, ← _root_.mul_assoc, inv_pow, ← pow_mul, ← pow_mul, _root_.mul_comm e N,
      mul_inv_cancel, _root_.one_mul]
  have h' : (g ^ N).val ^ e * ((g ^ e * t)⁻¹).val ^ N = (t⁻¹).val ^ N := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1])) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : L.ι) (h₀ : ∀ z, m (w (r z)) ∈ L.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => (r ≫ w) ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ (r ≫ w) ⁻¹ᵁ LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀] :=
    fun j z hz => Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact hz
      · exact h₀ z
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j)) ^ e *
        ((gm (r ≫ w) z (LB.wchart L (K := Fin 2) ![𝟙 X, m] ![j, j₀]) (α.s ![j, j₀]))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) ^ e *
      ((r ≫ w).appLE _ _ (l₂ j)).hom ((α.s ![j, j₀])⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · refine congrArg (· ^ N) ((gs_appLE (r ≫ w) z _ _ _ hz _).trans ?_)
      exact (gs_unit (r ≫ w) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans hα (r ≫ w) z (l₂ j hz.1) (l₂ j' hz.2)]
      have h1 : gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) = 1 := gm_self hL _ z (h₀ z)
      have t₁ : trF (L := L) (K := Fin N) (fun _ => w) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := Fin 2) ![𝟙 X, m] ![(e : ℤ), -1] (r ≫ w) z ![j, j₀] ![j', j₀] =
          gm (r ≫ w) z (L.U j ⊓ L.U j') (L.g j j') ^ e := by
        rw [trF, Fin.prod_univ_two]
        change gm ((r ≫ w) ≫ 𝟙 X) z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) *
          gm ((r ≫ w) ≫ m) z (L.U j₀ ⊓ L.U j₀) (L.g j₀ j₀) ^ (-1 : ℤ) = _
        rw [h1, Category.comp_id]; simp
      rw [t₁, t₂]
      exact pow_aux _ _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL ((r ≫ w) z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => w) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => w) k := W.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_relAmple {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsProper A.hom] (L : LB A.left)
    (hL : L.IsLB) (hA : RelAmple A L) (m : A ⟶ A) (e : ℕ) (he : e ≠ 0)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, m.left] ![(e : ℤ), -1])) (hα : α.IsGen) :
    IsFinite m.left := by
  have hm : m.left ≫ A.hom = A.hom := Over.w m
  have : IsProper (m.left ≫ A.hom) := by rw [hm]; infer_instance
  have : IsProper m.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite m.left from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (A.hom y)) isOpen_univ
  obtain ⟨N, -, M, s, hcov, hs⟩ := hA U hU
  have hy : ∀ z, m.left (m.left.fiberι y z) = y := fun z =>
    (m.left.range_fiberι y).le ⟨z, rfl⟩
  let r : m.left.fiber y ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι (m.left.fiberι y) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change A.hom (m.left.fiberι y z) ∈ U
      rw [← hm, Scheme.Hom.comp_apply, hy]
      exact hyU)
  have hr : r ≫ (A.hom ⁻¹ᵁ U).ι = m.left.fiberι y := IsOpenImmersion.lift_fac _ _ _
  have := isAffineHom_fromSpecResidueField A.left y
  have : IsAffineHom (r ≫ (A.hom ⁻¹ᵁ U).ι) := by
    rw [hr]; exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback m.left (A.left.fromSpecResidueField y)).flip this
  have : IsAffineHom r := .of_comp r (A.hom ⁻¹ᵁ U).ι
  obtain ⟨j₀, hj₀⟩ := exists_chart hL y
  have key := fun i => exists_fn L hL (A.hom ⁻¹ᵁ U).ι N (s i) m.left e he α hα r j₀ (fun z => by
    rw [← Scheme.Hom.comp_apply r, hr, hy]; exact hj₀)
  choose a ha using key
  have : IsProper (m.left.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd m.left (A.left.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := A.left.residueField y) (m.left.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => r ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage r

theorem isFinite_mulA :
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → PolBaseChangeSt → (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left := by
  intro h _ _ S P n hn
  have H := h S P n
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have := P.isAb.proper
  exact isFinite_of_relAmple P.A P.L P.isLB P.ample _ (n ^ 2) (by positivity) α hα

end GlobalTheory.MulFinite
end
end

