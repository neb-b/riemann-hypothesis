module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDims
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleIsometriesCoisotropicKernels
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem nsmul_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] {n m : ℕ} (h : n ∣ m) (e : M) : ∃ e', m • e = n • e' := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k • e, mul_smul n k e⟩

theorem Cois.comp_isometry {y : D.La →ₗ[𝓞 E] X} {n : ℕ} (hy : Cois D y n) (G : D.La ≃ₗ[𝓞 E] D.La)
    (hG : ∀ a b, D.EF (G a) (G b) = D.EF a b) : Cois D (y.comp G.toLinearMap) n := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨a, e, he⟩ := hy.1 x
    exact ⟨G.symm a, e, by simpa using he⟩
  · have := hy.2 (G a) fun b hb => by
      have h1 := ha (G.symm b) (by simpa using hb)
      rwa [← hG a (G.symm b), G.apply_symm_apply] at h1
    exact this

theorem ker_iff_of_congr {f f' : D.La →ₗ[𝓞 E] X} {n : ℕ} (h : ∀ a, ∃ e, f' a = f a + n • e) (a : D.La) :
    (∃ e, f a = n • e) ↔ ∃ e, f' a = n • e := by
  obtain ⟨e₀, he₀⟩ := h a
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e + e₀, by rw [he₀, he, smul_add]⟩
  · rintro ⟨e, he⟩
    exact ⟨e - e₀, by rw [smul_sub, ← he, he₀]; abel⟩

theorem KerIs.of_dvd {f : D.La →ₗ[𝓞 E] X} {Z : Submodule (𝓞 E) D.La} {n n' : ℕ} (hk : KerIs D f Z n')
    (hon : ∀ x, ∃ a e, f a = x + n' • e) (hd : n ∣ n') : KerIs D f Z n := by
  intro a
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨c, e', hc⟩ := hon x
    have h1 : ∃ e, f (a - n • c) = n' • e := ⟨-(n • e'), by
      rw [map_sub, map_nsmul, hx, hc, smul_add, smul_neg, smul_comm n' n e']; abel⟩
    obtain ⟨b, hb, e, he⟩ := (hk _).1 h1
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e
    refine ⟨b, hb, c + e'', ?_⟩
    rw [sub_eq_iff_eq_add] at he
    rw [he, smul_add, ← he'']; abel
  · rintro ⟨b, hb, e, rfl⟩
    obtain ⟨e', he'⟩ := (hk b).2 ⟨b, hb, 0, by simp⟩
    obtain ⟨e'', he''⟩ := nsmul_eq_nsmul_of_dvd hd e'
    exact ⟨e'' + f e, by rw [map_add (f := _), map_nsmul, he', he'', smul_add]⟩

theorem exists_step [Module.Free ℤ X] [Module.Finite ℤ X] {Z FinalForm : Submodule (𝓞 E) D.La} (hop : IsOpp D Z FinalForm)
    (hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (f : D.La →ₗ[𝓞 E] X) {n N' : ℕ} (hn : 0 < n)
    (hd : N' ∣ n) (hc : Cois D f n) (hk : KerIs D f Z N') :
    ∃ h : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (h a) (h b) = D.EF a b) ∧ (∀ a, ∃ e, h a = a + N' • e) ∧
      KerIs D (f.comp h.toLinearMap) Z n := by
  obtain ⟨Z'', hop'', hon⟩ := _root_.GlobalTheory.LowFilt.exists_opp_transv D f n hn hc Z FinalForm hop hrk
  obtain ⟨h, hi, hN, hk'⟩ := _root_.GlobalTheory.LowFilt.exists_isometry_kerIs D f n N' hn hd hc Z Z'' hop'' hrk hk hon
  exact ⟨h, hi, hN, hk'⟩

def levelSeq (N j : ℕ) : ℕ := N * (j + 1).factorial

theorem levelSeq_pos {N : ℕ} (hN : 0 < N) (j : ℕ) : 0 < levelSeq N j := Nat.mul_pos hN (Nat.factorial_pos _)

theorem levelSeq_succ (N j : ℕ) : levelSeq N (j + 1) = levelSeq N j * (j + 2) := by
  unfold levelSeq; rw [Nat.factorial_succ (j + 1)]; ring

theorem levelSeq_dvd (N : ℕ) {i j : ℕ} (h : i ≤ j) : levelSeq N i ∣ levelSeq N j :=
  Nat.mul_dvd_mul_left N (Nat.factorial_dvd_factorial (by omega))

theorem dvd_levelSeq (N : ℕ) {n : ℕ} (hn : 0 < n) : n ∣ levelSeq N n :=
  Dvd.dvd.mul_left (Nat.dvd_factorial hn (Nat.le_succ n)) N

theorem levelSeq_zero (N : ℕ) : levelSeq N 0 = N := by simp [levelSeq]

def GoodAt (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (N n : ℕ) (G : D.La ≃ₗ[𝓞 E] D.La) : Prop :=
  (∀ a b, D.EF (G a) (G b) = D.EF a b) ∧ (∀ a, ∃ e, G a = a + N • e) ∧ KerIs D (y.comp G.toLinearMap) Z n

def iterSeq {α : Type} (x₀ : α) (f : ℕ → α → α) (j : ℕ) : α := Nat.rec (motive := fun _ => α) x₀ f j

theorem exists_compatible_isometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : ℕ → D.La →ₗ[𝓞 E] X), (∀ n, 0 < n → Cois D (y n) n) →
    (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, y (n * m) a = y n a + n • e) →
    Module.finrank (𝓞 E) X ≤ min D.p D.q → ∀ N, 0 < N →
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X ∧
      ∃ g : ℕ → D.La ≃ₗ[𝓞 E] D.La, (∀ n a b, D.EF (g n a) (g n b) = D.EF a b) ∧
        (∀ n m, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧ (∀ n a, ∃ e, g n a = a + N • e) ∧
        ∀ n, 0 < n → ∀ a, (∃ e, y n (g n a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y hc hy hr N hN
  classical
  obtain ⟨Z₀, hZ₀, hrk₀⟩ := _root_.GlobalTheory.LowFilt.exists_isIsoSat_finrank D _ hr
  obtain ⟨Z₀', hop₀⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z₀ hZ₀
  obtain ⟨Z₁', hop₁, hon₁⟩ := _root_.GlobalTheory.LowFilt.exists_opp_transv D (y N) N hN (hc N hN) Z₀ Z₀' hop₀ hrk₀
  obtain ⟨g₀, hg₀, -, hk₀⟩ := _root_.GlobalTheory.LowFilt.exists_isometry_kerIs D (y N) N 1 hN (one_dvd N) (hc N hN) Z₀ Z₁' hop₁ hrk₀
    (fun a => ⟨fun _ => ⟨0, zero_mem _, a, by simp⟩, fun _ => ⟨y N a, by simp⟩⟩) hon₁
  set Z := Z₀.map (g₀ : D.La →ₗ[𝓞 E] D.La) with hZdef
  have memZ : ∀ x, x ∈ Z ↔ g₀.symm x ∈ Z₀ := fun x => Submodule.mem_map_equiv Z₀
  have memP : ∀ x, x ∈ perp D Z ↔ g₀.symm x ∈ perp D Z₀ := by
    intro x
    rw [mem_perp, mem_perp]
    constructor
    · intro hx z hz
      have := hx (g₀ z) ((memZ _).2 (by simpa using hz))
      rwa [← hg₀ (g₀.symm x) z, g₀.apply_symm_apply]
    · intro hx z hz
      have := hx _ ((memZ z).1 hz)
      rwa [← hg₀ (g₀.symm x) (g₀.symm z), g₀.apply_symm_apply, g₀.apply_symm_apply] at this
  have hZ : IsIsoSat D Z := by
    refine ⟨fun z hz => (memP z).2 (hZ₀.1 ((memZ z).1 hz)), fun n x hn hx => (memZ x).2 ?_⟩
    have := (memZ _).1 hx
    rw [map_nsmul] at this
    exact hZ₀.2 n _ hn this
  have hrk : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X := by
    rw [← hrk₀]; exact (g₀.submoduleMap Z₀).finrank_eq.symm
  obtain ⟨FinalForm, hop⟩ := GlobalTheory.T.exists_oppositeIsotropicPair D Z hZ
  have hbase : KerIs D (y N) Z N := by
    intro a
    have h1 := hk₀ (g₀.symm a)
    rw [g₀.apply_symm_apply] at h1
    rw [h1]
    constructor
    · rintro ⟨b, hb, e, he⟩
      refine ⟨g₀ b, (memP _).2 (by rwa [g₀.symm_apply_apply]), g₀ e, ?_⟩
      conv_lhs => rw [← g₀.apply_symm_apply a, he]
      rw [map_add (f := _), map_nsmul]
    · rintro ⟨b, hb, e, rfl⟩
      exact ⟨g₀.symm b, (memP b).1 hb, g₀.symm e, by rw [map_add (f := _), map_nsmul]⟩
  have hstep : ∀ j (G : D.La ≃ₗ[𝓞 E] D.La), GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) G →
      ∃ G' : D.La ≃ₗ[𝓞 E] D.La, GoodAt D (y (levelSeq N (j + 1))) Z N (levelSeq N (j + 1)) G' ∧
        ∀ a, ∃ e, G' a = G a + levelSeq N j • e := by
    rintro j G ⟨hGi, hGN, hGk⟩
    have hcong : ∀ a, ∃ e, ((y (levelSeq N (j + 1))).comp G.toLinearMap) a =
        ((y (levelSeq N j)).comp G.toLinearMap) a + levelSeq N j • e := by
      intro a
      rw [levelSeq_succ]
      exact hy (levelSeq N j) (j + 2) (levelSeq_pos hN j) (by omega) (G a)
    have hk : KerIs D ((y (levelSeq N (j + 1))).comp G.toLinearMap) Z (levelSeq N j) := fun a =>
      (ker_iff_of_congr hcong a).symm.trans (hGk a)
    obtain ⟨h, hi, hN', hk'⟩ := exists_step hop hrk ((y (levelSeq N (j + 1))).comp G.toLinearMap)
      (levelSeq_pos hN (j + 1)) (levelSeq_dvd N (Nat.le_succ j)) ((hc _ (levelSeq_pos hN _)).comp_isometry G hGi) hk
    refine ⟨h.trans G, ⟨fun a b => ?_, fun a => ?_, fun a => hk' a⟩, fun a => ?_⟩
    · simp only [LinearEquiv.trans_apply]; rw [hGi, hi]
    · obtain ⟨e, he⟩ := hN' a
      obtain ⟨e₁, he₁⟩ := hGN a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (Dvd.intro _ rfl : N ∣ levelSeq N j) (G e)
      exact ⟨e₁ + e₂, by rw [LinearEquiv.trans_apply, he, map_add (f := _), map_nsmul, he₁, he₂, smul_add, add_assoc]⟩
    · obtain ⟨e, he⟩ := hN' a
      exact ⟨G e, by rw [LinearEquiv.trans_apply, he, map_add (f := _), map_nsmul]⟩
  choose! F hF hFc using hstep
  obtain ⟨S, hS0, hSs⟩ : ∃ S : ℕ → D.La ≃ₗ[𝓞 E] D.La, S 0 = LinearEquiv.refl _ _ ∧ ∀ j, S (j + 1) = F j (S j) :=
    ⟨iterSeq (LinearEquiv.refl _ _) F, rfl, fun _ => rfl⟩
  have hgood : ∀ j, GoodAt D (y (levelSeq N j)) Z N (levelSeq N j) (S j) := by
    intro j
    induction j with
    | zero =>
      rw [hS0, levelSeq_zero]
      exact ⟨fun _ _ => rfl, fun a => ⟨0, by simp⟩, fun a => hbase a⟩
    | succ j ih => rw [hSs]; exact hF j (S j) ih
  have hc1 : ∀ j a, ∃ e, S (j + 1) a = S j a + levelSeq N j • e := fun j a => by
    rw [hSs]; exact hFc j (S j) (hgood j) a
  have hck : ∀ i k a, ∃ e, S (i + k) a = S i a + levelSeq N i • e := by
    intro i k
    induction k with
    | zero => intro a; exact ⟨0, by simp⟩
    | succ k ih =>
      intro a
      obtain ⟨e, he⟩ := ih a
      obtain ⟨e₁, he₁⟩ := hc1 (i + k) a
      obtain ⟨e₂, he₂⟩ := nsmul_eq_nsmul_of_dvd (levelSeq_dvd N (Nat.le_add_right i k)) e₁
      exact ⟨e + e₂, by rw [← Nat.add_assoc, he₁, he, he₂, smul_add, add_assoc]⟩
  refine ⟨Z, hZ, hrk, S, fun n => (hgood n).1, fun n m hn hm a => ?_, fun n => (hgood n).2.1, fun n hn a => ?_⟩
  · have hle : n ≤ n * m := Nat.le_mul_of_pos_right n hm
    rw [← Nat.add_sub_of_le hle]
    obtain ⟨e, he⟩ := hck n (n * m - n) a
    obtain ⟨e', he'⟩ := nsmul_eq_nsmul_of_dvd (dvd_levelSeq N hn) e
    exact ⟨e', by rw [he, he']⟩
  · have hg := hgood n
    have hon := ((hc _ (levelSeq_pos hN n)).comp_isometry (S n) hg.1).1
    have hkn := hg.2.2.of_dvd hon (dvd_levelSeq N hn)
    obtain ⟨k, hk⟩ := dvd_levelSeq N hn
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk; exact absurd hk (levelSeq_pos hN n).ne'
      · exact h0
    have hcong : ∀ a, ∃ e, ((y (levelSeq N n)).comp (S n).toLinearMap) a =
        ((y n).comp (S n).toLinearMap) a + n • e := by
      intro a
      rw [hk]
      exact hy n k hn hkpos (S n a)
    exact (ker_iff_of_congr hcong a).trans (hkn a)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorMulIntegralUnitFiniteAdelesAwayPStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP : ∀ (p : ℕ) [Fact p.Prime] (a b : AfP p) (K : ℕ), 0 < K → K.Coprime p → IsIntAf a → IsIntAf b → a * b = (K : AfP p) → ∃ (c : ℕ) (ε ε' : AfP p), c.Coprime p ∧ c ∣ K ∧ IsIntAf ε ∧ IsIntAf ε' ∧ ε * ε' = 1 ∧ a = (c : AfP p) * ε := by
  first | (exact @GlobalTheory.AfUnitSplit.exists_dvd_mul_unit) | (exact GlobalTheory.AfUnitSplit.exists_dvd_mul_unit) | (intros; apply GlobalTheory.AfUnitSplit.exists_dvd_mul_unit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualExist

theorem hasRep_of_iso {S : Scheme.{0}} {A : Over S} [GrpObj A] {g : ℕ} {S₁ S₂ : Over S} (e : S₁ ≅ S₂)
    (h : HasRep A g S₁) : HasRep A g S₂ := by
  obtain ⟨B, b, P, hR, hG⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, fun T t N hN => ?_⟩, ?_⟩
  · obtain ⟨x, ⟨hx, hxN⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨by rw [← Category.assoc, hx, Category.assoc, e.inv_hom_id, Category.comp_id], hxN⟩,
      fun y ⟨hy, hyN⟩ => hu y ⟨?_, hyN⟩⟩
    rw [← hy, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]
  · have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).inv)
    have sq : IsPullback (𝟙 B.left) (b.left ≫ e.hom.left) b.left e.inv.left :=
      IsPullback.of_horiz_isIso ⟨by
        rw [Category.id_comp, Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.comp_id]⟩
    have hp := hG.proper
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    rw [Over.comp_left]
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) sq hp, MorphismProperty.of_isPullback sq hG.smooth,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq hG.conn⟩

theorem hasRep_affineOpen {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {V : S.Opens}
    (hV : IsAffineOpen V) (g : ℕ) (hg : SmoothOfRelativeDimension g (pullback.snd A.hom V.ι)) :
    HasRep A g (Over.mk V.ι) := by
  let A' : Over (Sp Γ(S, V)) := (Over.pullback hV.fromSpec).obj A
  letI : GrpObj A' := Functor.grpObjObj
  have hpb : IsGrpPullback A' A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hg' : SmoothOfRelativeDimension g A'.hom := by
    have sq : IsPullback (pullback.lift (pullback.fst A.hom hV.fromSpec)
        (pullback.snd A.hom hV.fromSpec ≫ hV.isoSpec.inv)
        (by rw [pullback.condition, Category.assoc, IsAffineOpen.isoSpec_inv_ι]))
        (pullback.snd A.hom hV.fromSpec) (pullback.snd A.hom V.ι) hV.isoSpec.inv :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact IsPullback.of_hasPullback A.hom hV.fromSpec)
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback A.hom V.ι)
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback sq hg
  have h1 := ((_root_.GlobalTheory.DualCon.hasRep_baseChange_iff _ _ hV.fromSpec A A' _ hpb g (𝟙_ _)).1).1 (_root_.GlobalTheory.DualCon.hasRep_affine _ A' g hA' hg')
  refine hasRep_of_iso (Over.isoMk hV.isoSpec.symm ?_) h1
  show hV.isoSpec.inv ≫ V.ι = 𝟙 _ ≫ hV.fromSpec
  rw [Category.id_comp, IsAffineOpen.isoSpec_inv_ι]

theorem exists_dual : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∃ (B : Over S) (_ : GrpObj B) (P : LB (A ⊗ B).left), IsAbelianScheme B ∧ DimLe A B ∧ IsDual A B P := by
  intro S A _ hA
  choose V g hV hsV hgV using _root_.GlobalTheory.DualCon.abelianScheme_locally_relDim S A hA
  have cov : ∀ s : S, ∃ i, s ∈ V i := fun s => ⟨s, hsV s⟩
  obtain ⟨B, P, hR, hGood⟩ :=
    _root_.GlobalTheory.DualCon.ZarGlue.zariski_glue S A hA S V g cov (fun i => hasRep_affineOpen A hA (hV i) (g i) (hgV i))
  obtain ⟨inst, hcomm, hD, -⟩ := _root_.GlobalTheory.DualCon.rep_isDual S A B P hR
  refine ⟨B, inst, P, ?_, ?_, hD⟩
  · have hU : iSup V = ⊤ := eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsV s⟩
    have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
    have sq := fun i => IsPullback.of_hasPullback B.hom (V i).ι
    exact
      { comm := hcomm
        smooth := GlobalTheory.CoverGlue.of_isPullback_cover @Smooth hU sq fun i => by
          haveI := (hGood i).smooth; exact SmoothOfRelativeDimension.smooth (g i) _
        proper := GlobalTheory.CoverGlue.of_isPullback_cover @IsProper hU sq fun i => (hGood i).proper
        geomConnected := GlobalTheory.CoverGlue.of_isPullback_cover @GeometricallyConnected hU sq fun i => (hGood i).conn }
  · have : GeometricallyConnected A.hom := hA.geomConnected
    exact _root_.GlobalTheory.DualCon.dimLe_of_local S A B inferInstance S V g cov hgV fun i => (hGood i).smooth

end GlobalTheory.DualExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtOfMinAt5
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MinExt

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G k ψ) (e : g ≫ f = k) :
    ∃ φ', IsGrpPullback G'' G' g φ' := by
  subst e
  have w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [n.1.w, Category.assoc]
  exact ⟨h.1.lift ψ (G''.hom ≫ g) w, h.cancel (n.congr rfl (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩

theorem exists_ext_of_minAt5 : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left), IsGenFibre F y α₁ → ∀ b : cycAway n →+* R, y ≫ F.s = jK R ≫ spMap b → ∃ a : Sp R ⟶ Z, jK R ≫ a = y ≫ i := by
  intro g n F Z z i OZ h R _ _ _ _ _ _ G₁ _ _ hG₁ y α₁ hα₁ b hyb
  obtain ⟨o', _, β, S', s', U, c, π, G, _, e, _, N, ⟨-, hz, -, hiz, -, hOZ, hamp⟩,
    ⟨-, -, -, -, -, hcfin, hcsurj, hUπ, -, -, hπp, -⟩, ⟨hGsa, hGsm, he⟩, ⟨-, hL⟩⟩ := h
  haveI := hcfin
  haveI := hcsurj
  haveI := hπp
  haveI : IsProper z := by
    obtain ⟨m, j, hj, rfl⟩ := hz
    have := isProper_str (cycAway n) m
    infer_instance
  obtain ⟨K', _, _, _, y', hy'⟩ := _root_.GlobalTheory.FinLift.lift_fieldPoint U.toScheme F.X c (FractionRing R) y
  obtain ⟨R', _, _, _, _, _, ρ, eR, -, hinj, hcomp, hmeet⟩ := _root_.GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension R K'
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  let gam : FractionRing R →+* FractionRing R' := (eR.symm : K' →+* FractionRing R').comp (algebraMap (FractionRing R) K')
  have E1 : spMap gam = spMap (eR.symm : K' →+* FractionRing R') ≫ spMap (algebraMap (FractionRing R) K') :=
    spMap_comp_eq _ _
  have E2 : spMap gam ≫ jK R = jK R' ≫ spMap ρ := by
    change spMap gam ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
    rw [← spMap_comp_eq, ← spMap_comp_eq]
    congr 1
    ext r
    simp only [RingHom.comp_apply, gam]
    rw [← hcomp r]
    simp
  let yy : Sp (FractionRing R') ⟶ S' := spMap (eR.symm : K' →+* FractionRing R') ≫ y' ≫ U.ι
  have E4 : spMap gam ≫ y = (spMap (eR.symm : K' →+* FractionRing R') ≫ y') ≫ c := by
    rw [Category.assoc, hy', E1, Category.assoc]
  have E3 : yy ≫ π = spMap gam ≫ y ≫ i := by
    simp only [yy, Category.assoc]
    rw [hUπ, ← Category.assoc y' c i, hy', E1]
    simp only [Category.assoc]
  let G₁' := (Over.pullback (spMap ρ)).obj G₁
  have hG₁' : IsSemiAbelian G₁' := IsSemiAbelian.pullback (spMap ρ) G₁ hG₁
  haveI : IsCommMonObj G₁' := hG₁'.comm
  have h1 := ((isGrpPullback_pullback G₁' (jK R')).comp (isGrpPullback_pullback G₁ (spMap ρ))).congr E2.symm rfl
  obtain ⟨φ1, hφ1⟩ := exists_factor (isGrpPullback_pullback G₁ (jK R)) h1 rfl
  have h2 := (hφ1.comp hα₁).congr E4 rfl
  obtain ⟨φ2, hφ2⟩ := exists_factor (isGrpPullback_pullback F.univ.A c) h2 rfl
  have h3 := (hφ2.comp he).congr (Category.assoc _ _ _) rfl
  have hyz : yy ≫ π ≫ z = jK R' ≫ spMap (ρ.comp b) := by
    rw [← Category.assoc, E3, Category.assoc, Category.assoc, hiz, hyb, ← Category.assoc, E2, spMap_comp_eq,
      Category.assoc]
  obtain ⟨a', ha'⟩ := _root_.GlobalTheory.TozCore.exists_extension_of_cover_hodge (cycAway n) g Z S' z π OZ hOZ hamp G N hGsa hGsm hL R' (ρ.comp b) G₁' hG₁' yy _ h3 hyz
  have hmeet' : ∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x :=
    fun x w hw => hmeet x w (by rw [hw]; simp [gam])
  exact _root_.GlobalTheory.TorDown.ext_of_fraction_meet Z R R' gam hmeet' (y ≫ i) a' (ha'.trans E3)

end GlobalTheory.MinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectAbelianPartTateIsometryStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerObject_abelianPart_tateIsometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (Z : Submodule (𝓞 E) Dw.La) (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → GlobalTheory.LowDat.IsLower Dw D' Z f →
  Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X →
  D'.p = Dw.p - Module.finrank (𝓞 E) Z → D'.q = Dw.q - Module.finrank (𝓞 E) Z →
  ∀ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
  (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I) →
  ∃ (o' : Obj D' (GlobalTheory.LowDat.lowLevel l) (baseKA (GlobalTheory.LowDat.lowLevel l)) (GlobalTheory.LowDat.lowS C))
    (φB : o'.t.G.left ⟶ C.P.D.toPre.P.A.left),
    IsGrpPullback o'.t.G C.P.D.toPre.P.A (𝟙 _) φB ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (o'.t.act.act x).left ≫ φB = φB ≫ (C.P.oD.onB.act x).left) ∧
    (∃ w : LB.Iso o'.t.PP.L (C.P.D.toPre.P.L.pull φB), w.IsGen) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)),
      GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.FiltGraded C Z F I →
      ∃ I' : GlobalTheory.LowDat.LowTate C D' o' F, GlobalTheory.LowDat.LowGraded C Z D' f o' φB F I I' := by
  first | exact @GlobalTheory.LowDat.LowObj.exists_lowObj | exact GlobalTheory.LowDat.LowObj.exists_lowObj | (intros; apply GlobalTheory.LowDat.LowObj.exists_lowObj <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsDividingLabelGroupMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem exists_terms_single : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : (Fin 8 → Y1) → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ m t δ 𝔪 a ha
  obtain ⟨u, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hT⟩, -, -⟩ :=
    _root_.GlobalTheory.Poinc.IntTerm.exists_terms g n F W Z i X₁ z₁ act x₀ hdiv V ev Y m t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val Subtype.range_coe
  exact ⟨fun mu _ => u mu ⟨a, ha⟩ * mono W t δ mu, x, fr, th, w₀, s, fun _ => g' ⟨a, ha⟩, fun _ => w ⟨a, ha⟩, hx, hfr, hth,
    hw₀, hs, fun _ => hc ⟨a, ha⟩, fun mu _ => hT mu ⟨a, ha⟩⟩

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolZeroEqConnectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_symbolZero_eq_connection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ (κ : ℕ → (DualNumber k)ˣ) (ℓ : ℕ → P.D.toPre.X →+ k), ∀ (e : ℕ), 1 ≤ e → ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) → ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val = gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom ((κ e).val * (1 + TrivSqZeroExt.inr (ℓ e α)))) * (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  first | exact @GlobalTheory.HeatUConn.uconn | exact GlobalTheory.HeatUConn.uconn | (intros; apply GlobalTheory.HeatUConn.uconn <;> assumption)
end

