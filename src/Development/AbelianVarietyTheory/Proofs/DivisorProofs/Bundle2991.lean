module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1269
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2968
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcObjIsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRepresentingSchemePinchedBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOffVarietyMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem dvd_pair (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k n : ℕ) (hk0 : k ≠ 0) (hck : c ∣ k ^ 2)
    (hkn : (k : ℤ) ^ 2 ∣ n) (hsim : ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ x, ∃ y z, h n y = k • x + n • z) (x v : D.La) :
    (k : ℤ) ∣ ((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v := by
  obtain ⟨y, z, hyz⟩ := hon v
  have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast Nat.div_mul_cancel hck
  have h1 : D.EF (h n x) (h n y) = (k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z := by
    rw [hyz, map_add (f := _), map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have h2 := hsim x y
  rw [h1] at h2

  have h3 : (k : ℤ) ^ 2 ∣ (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v) := by
    have e1 : (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v)
        = ((k ^ 2 / c : ℕ) : ℤ) * ((k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z - c * u n * D.EF x y)
          - ((k ^ 2 / c : ℕ) : ℤ) * n * D.EF (h n x) z + (k : ℤ) ^ 2 * (u n * D.EF x y) := by
      rw [← hmZ]; ring
    rw [e1]
    refine dvd_add (dvd_sub (Dvd.dvd.mul_left (hkn.trans h2) _) ?_) (dvd_mul_right _ _)
    exact (hkn.trans (dvd_mul_left _ _)).mul_right _
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
  rw [pow_two] at h3
  exact (mul_dvd_mul_iff_left hkZ).1 h3

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem sqrt_hecke_point_weil_orthogonal (I : TateIsoO D K Q act e) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ)
    (c k N : ℕ) (hk : k.Coprime p) (hN : 0 < N) (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) (x : D.La) :
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
      (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  have hp : p.Prime := Fact.out
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hL : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
  have gen : ∀ M j t : ℕ, 0 < M → k ∣ M → (N * k * M).Coprime p → 2 * j = M + t * (k * M) →
      ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
        (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
    intro M j t hM hkM hcop hj
    have hn' : 0 < N * k * M := Nat.mul_pos hL hM
    obtain ⟨M', rfl⟩ := hkM
    have hkn : (k : ℤ) ^ 2 ∣ ((N * k * (k * M') : ℕ) : ℤ) := ⟨N * M', by push_cast; ring⟩
    refine ⟨N * k * (k * M'), I.ev (N * k * (k * M')) (j • N • h (N * k * (k * M')) x), hn', hcop, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (hcomp (N * k) (k * M') hL hM hcop).1 x
      have e1 : 2 • j • N • h (N * k * (k * M')) x
          = (k * M') • (N • h (N * k * (k * M')) x) + (N * k * (k * M')) • (t • h (N * k * (k * M')) x) := by
        simp only [smul_smul, ← add_smul]
        congr 1
        calc 2 * (j * N) = (2 * j) * N := by ring
          _ = _ := by rw [hj]; ring
      rw [← ev_nsmul, e1, I.add, (I.ker _ hn' hcop _).2 ⟨_, rfl⟩, _root_.mul_one, ev_nsmul,
        I.tower (N * k) (k * M') hL hM hcop, hz, smul_add, I.add, smul_comm N (N * k) z,
        (I.ker _ hL (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop) _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [← ev_nsmul]
      refine pair_one I _ hn' hcop _ (fun v => ?_)
      obtain ⟨a, ha⟩ := dvd_pair h u c k _ hk0 hck hkn ((hsim _ hn' hcop).2) (hon _ hn' hcop) x v
      have e2 : 2 * D.EF ((k ^ 2 / c) • j • N • h (N * k * (k * M')) x) v
          = (2 * j : ℕ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h (N * k * (k * M')) x) v) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast; ring
      rw [e2, ha, hj]
      exact ⟨(1 + t * k) * a, by push_cast; ring⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
        rw [hk] at h2; omega
      · exact h0
    obtain ⟨r, hr⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
    refine gen k (k * (r + 1)) 1 (Nat.pos_of_ne_zero hk0) dvd_rfl (Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) hk) ?_
    rw [hr]; ring
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h0 => hp2 h0.symm)
    refine gen (k * 2) k 0 (by positivity) (dvd_mul_right _ _)
      (Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) (Nat.Coprime.mul_left hk h2p)) ?_
    ring

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.HeckeAd

theorem fibre_triv (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hk : k.Coprime p) (hN : 3 ≤ N) (hNp : N.Coprime p)
    (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (g : 𝟙_ (Over S) ⟶ o.A)
    (hg : g ∈ heckeSubA o (h (N * k)) N) (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) :
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).pull
      (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.UPel.HT.HeckeRootA.sqrt_hecke_point_weil_orthogonal I h u c k N hk (by omega) hNp hck hcomp hsim hon x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := GlobalTheory.HeckeFibre.transl_triv o.A o.ab _ (pull_isLB o.isLB _)
    (GlobalTheory.HeckeFibre.rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.PicBilin.triv_pow_of_translDiff o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y)
    (GlobalTheory.HeckeFibre.pic_field_eq_zero K) (o.eta (N • h (N * k) x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.UPel.HT.HeckeAd.KerPol

section Main
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ g)).left).Gen, t.IsGen) := by
  intro p _ D R _ b h u c k N hc hk hN hNp hck hlin hcomp hsim hon S s o g hg
  have hfib := fibre_triv p D R b h u c k N hk hN hNp hck hcomp hsim hon S s o g hg
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  set th : o.A ⟶ o.A := toUnit o.A ≫ g with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, GlobalTheory.UPel.HT.HeckeAd.pow_eq_one_of_mem o (h (N * k)) g hg, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.HeckeAd.KerPol
end Main
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointDescendsAlgClosedSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgClosedDescent

theorem grpPullback_point_descends : ∀ (K : Type) [Field K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] (G : Over (Sp K)) [GrpObj G] (π : G.left ⟶ B₀.left), IsAbelianScheme B₀ → IsGrpPullback G B₀ (spMap k₀.subtype) π → ∀ (n : ℕ), 0 < n → ∀ (y : 𝟙_ (Over (Sp K)) ⟶ G) (z₀ : Sp k₀ ⟶ B₀.left), (y ^ n).left ≫ π = spMap k₀.subtype ≫ z₀ → ∃ y₀ : Sp k₀ ⟶ B₀.left, y.left ≫ π = spMap k₀.subtype ≫ y₀ := by
  intro K _ _ k₀ hk B₀ _ G _ π hB hG n hn y z₀ hz
  haveI : IsAlgClosed k₀ := hk
  have hs : spMap (algebraMap k₀ K) = spMap k₀.subtype := rfl
  have hst := isGrpPullback_pullback B₀ (spMap (algebraMap k₀ K))
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hG (hst.congr hs rfl)
  haveI := he
  have hepi : Epi (spMap (algebraMap k₀ K)) := Flat.epi_of_flat_of_surjective _
  have hn' : (n : k₀) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap k₀ K) h
    rw [map_natCast, map_zero] at h2
    exact (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) h2
  have hz0 : z₀ ≫ B₀.hom = 𝟙 _ := by
    rw [← cancel_epi (spMap (algebraMap k₀ K))]
    have h1 : (y ^ n).left ≫ G.hom = 𝟙 _ := Over.w (y ^ n)
    have h2 := hG.1.w
    calc spMap (algebraMap k₀ K) ≫ z₀ ≫ B₀.hom = (y ^ n).left ≫ π ≫ B₀.hom := by
          rw [← Category.assoc, ← Category.assoc, hs, hz]
      _ = (y ^ n).left ≫ G.hom ≫ spMap k₀.subtype := by rw [h2]
      _ = spMap (algebraMap k₀ K) ≫ 𝟙 _ := by
          rw [← Category.assoc, h1, Category.id_comp, Category.comp_id]; rfl
  let z₀' : 𝟙_ (Over (Sp k₀)) ⟶ B₀ := Over.homMk z₀ hz0
  let y' := y ≫ e.hom
  have hpow : ∀ m : ℕ, (y ≫ e.hom) ^ m = (y ^ m) ≫ e.hom := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ k ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]
  have hy'n : y' ^ n = (y ^ n) ≫ e.hom := hpow n
  have hz' : (y' ^ n).left ≫ pullback.fst B₀.hom (spMap (algebraMap k₀ K)) =
      spMap (algebraMap k₀ K) ≫ z₀'.left := by
    rw [hy'n, Over.comp_left, Category.assoc, heφ]
    exact hz
  obtain ⟨y₀, -, hy₀⟩ := (point_descent B₀ hB n hn' y' z₀' hz').exists
  refine ⟨y₀.left, ?_⟩
  rw [← heφ, ← Category.assoc]
  exact hy₀

end GlobalTheory.AlgClosedDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliObjectPotentiallyGoodReduction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTPotGood

theorem potGood : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro p _ D R _ b N V K _ _ _ _ _ _ _ _ β o h
  rcases h with h | ⟨hdiv, hn⟩
  · let Ω := AlgebraicClosure K
    have hx : spMap (algebraMap K Ω) ≫ spMap β = spMap ((algebraMap K Ω).comp β) := by
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.HTLie.exists_lieMult_zero p D R b N (Sp K) (spMap β) o h Ω (spMap (algebraMap K Ω))
      ((algebraMap K Ω).comp β) hx
    exact _root_.GlobalTheory.PotGoodLie.potGood_of_lieMult_zero V K o.A o.ab D.F (o.act.toF D) Ω (algebraMap K Ω) σ hσ
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K o.A o.ab
    have h2g := _root_.GlobalTheory.UPel.HT.two_mul_relDim_eq_finrank p D R b N K β o g hg
    rw [D.rankLa] at h2g
    haveI := D.freeO
    haveI := D.finO
    have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    have hm := D.m_pos
    have hlt : g < Module.finrank ℤ D.O := by
      rw [D.rankO]
      have h1 : D.m * D.n * Module.finrank ℚ D.F < D.m * (2 * D.m) * Module.finrank ℚ D.F := by
        apply Nat.mul_lt_mul_of_pos_right _ hd
        exact Nat.mul_lt_mul_of_pos_left hn hm
      have h2 : D.m * (2 * D.m) * Module.finrank ℚ D.F = 2 * (D.m ^ 2 * Module.finrank ℚ D.F) := by ring
      omega
    exact _root_.GlobalTheory.potModel_of_intDivOrder_leftAction V K o.A g o.ab hg D.O o.act.act o.act.hom o.act.one o.act.mul o.act.add hdiv hlt

end GlobalTheory.HTPotGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeNoetherianInduc
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualConStep

def conductor (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] : Ideal R where
  carrier := {x | ∀ r : R', ∃ y : R, algebraMap R R' y = algebraMap R R' x * r}
  add_mem' {x x'} hx hx' r := by
    obtain ⟨y, hy⟩ := hx r
    obtain ⟨y', hy'⟩ := hx' r
    exact ⟨y + y', by rw [map_add (f := _), map_add (f := _), hy, hy', add_mul]⟩
  zero_mem' r := ⟨0, by simp⟩
  smul_mem' b {x} hx r := by
    obtain ⟨y, hy⟩ := hx r
    exact ⟨b * y, by rw [smul_eq_mul, map_mul, map_mul, hy, _root_.mul_assoc]⟩

theorem conductor_mul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] :
    ∀ x ∈ conductor R R', ∀ r : R', ∃ y ∈ conductor R R', algebraMap R R' y = algebraMap R R' x * r := by
  intro x hx r
  obtain ⟨y, hy⟩ := hx r
  refine ⟨y, fun r' ↦ ?_, hy⟩
  obtain ⟨z, hz⟩ := hx (r * r')
  exact ⟨z, by rw [hz, hy, _root_.mul_assoc]⟩

theorem hasRepAF_factor (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (V : A.left.Opens) (hV : IsAffineOpen V)
    (hVs : ∀ s : Sp R, ∃ x ∈ V, A.hom x = s) (D : Type) [CommRing D] [Algebra R D] [IsNoetherianRing D]
    [IsDomain D] [IsIntegrallyClosed D] :
    HasRepAF A g (Over.mk (spMap (algebraMap R D))) := by
  set f := algebraMap R D
  have hP := isGrpPullback_pullback A (spMap f)
  obtain ⟨hA', hg'⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A
    ((Over.pullback (spMap f)).obj A) _ g hP hA hg
  haveI : IsAffineHom (pullback.fst A.hom (spMap f)) :=
    (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.{0}).of_isPullback (IsPullback.of_hasPullback _ _).flip
      (inferInstance : IsAffineHom (spMap f))
  have hV' : IsAffineOpen (pullback.fst A.hom (spMap f) ⁻¹ᵁ V) := hV.preimage _
  have hVs' : ∀ s : Sp D, ∃ x ∈ pullback.fst A.hom (spMap f) ⁻¹ᵁ V,
      ((Over.pullback (spMap f)).obj A).hom x = s := by
    intro s
    obtain ⟨x, hx, hxs⟩ := hVs (spMap f s)
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x s hxs
    exact ⟨z, by simpa [hz1] using hx, hz2⟩
  obtain ⟨L, hL, hLa⟩ := _root_.GlobalTheory.ProjNormal.exists_relAmple_of_affine D _ hA' _ hV' hVs'
  have h1 := _root_.GlobalTheory.DualPol.hasRepAF_of_relAmple D _ g hA' hg' L hL hLa
  have h2 := ((_root_.GlobalTheory.DualCon.hasRep_baseChange_iff _ _ (spMap f) A _ _ hP g (𝟙_ _)).2).1 h1
  simpa using h2

theorem step : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → (∀ J : Ideal R, J ≠ ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J)))) → HasRep A g (𝟙_ _) := by
  intro R _ _ _ A _ g hA hg V hV hVs hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : IsEmpty (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsEmpty (PrimeSpectrum R))
    obtain ⟨B, b, P, hP, hG, -⟩ := _root_.GlobalTheory.DualCon.hasRepAF_of_isEmpty _ A (𝟙_ _) g this
    exact ⟨B, b, P, hP, hG⟩
  obtain ⟨n, D, iR, iA, hD, hinj, a, ha0, ha⟩ := _root_.GlobalTheory.ReducedNormalisation.exists_finiteIndex_prod_normalDomains R
  have hfac : ∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i)))) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hD i
    haveI : IsNoetherianRing (D i) := by
      haveI : Algebra.FiniteType R (D i) := inferInstance
      exact Algebra.FiniteType.isNoetherianRing R (D i)
    exact hasRepAF_factor R A g hA hg V hV hVs (D i)
  haveI : ∀ i, Module.Finite R (D i) := fun i ↦ (hD i).2.2
  have hprod := _root_.GlobalTheory.DualCon.ProdGlue.hasRepAF_pi R A g hA n D hfac
  have hac : a ∈ conductor R (∀ i, D i) := ha
  have hc : conductor R (∀ i, D i) ≠ ⊥ := fun h ↦ ha0 (by rw [h] at hac; exact (Submodule.mem_bot R).1 hac)
  exact _root_.GlobalTheory.Pinch.hasRep_pinched R A g hA hg (∀ i, D i) hinj _ conductor_mul hprod (hJ _ hc)

end GlobalTheory.DualConStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTraitsP
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.USep

open GlobalTheory.Poinc.Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

section

variable {A : Type} [CommRing A] [IsLocalRing A] (ζ : Sp A ⟶ pullback C.z (spMap C.b))
  (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] A)

def HasTraitsP : Prop :=
  ∀ (T : UTrait Xo c) (ev : A →+* T.V), IsLocalHom ev → jK T.V ≫ spMap ev ≫ ζ = T.y ≫ C.iF →
    ∃ (y : Φ.Y) (f : T.V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] T.P.D.toPre.X), Φ.m y = 1 ∧ IsPrincipalIdealRing (Φ.V y) ∧
      Function.Injective f ∧ IsLocalHom f ∧ f.comp ev = Φ.ev y ∧
      ∀ k, Φ.t y k ^ 2 = f T.ϖ ∧ ∀ a b, Φ.δ y k a b = T.be (e a) (e b)

def IsMemberP (N₁ : ℕ) {φ : InvFun (𝓞 E)} {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (Cm : GlobalTheory.UChart.MonoFam Xo c φ V) (ξ : Sp V ⟶ pullback C.z (spMap C.b)) (y : Φ.Y) (ρ : V →+* Φ.V y)
    (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) : Prop :=
  Function.Injective ρ ∧ ρ.Finite ∧ spMap (Φ.ev y) ≫ ζ = spMap ρ ≫ ξ ∧
    (∀ k, Φ.t y k ^ 2 = ρ (Cm.s (h k)) ∧ ∀ a b, Φ.δ y k a b = ((l.M' : ℤ) • Cm.δ (h k)) (e a) (e b)) ∧
    ∃ (D : DegPre (Φ.V y)) (p : IsPullDeg ρ Cm.P.D.toPre D),
      IsThetaTerms₀ D N₁ p.xe.symm fun mu c => Φ.term y (fun _ => e.symm mu) c

end

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfLbIsoFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.lbIso_of_lbIso_fieldExt : ∀ (k₀ K : Type) [Field k₀] [Field K] (i₀ : k₀ →+* K) (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ L L' : LB B.left, L.IsLB → L'.IsLB → LBIso (L.pull (pullback.fst B.hom (spMap i₀))) (L'.pull (pullback.fst B.hom (spMap i₀))) → LBIso L L' := by
  intro k₀ K _ _ i₀ B _ hB L L' hL hL' h
  exact GlobalTheory.PolIsoDescent.lbIso_descend GlobalTheory.globalFns_holds (spMap i₀) B hB hL hL' h
end

