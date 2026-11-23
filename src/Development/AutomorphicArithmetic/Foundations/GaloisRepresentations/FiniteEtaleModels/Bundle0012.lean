module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ANumSplit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem natCast_gcd_mem {A : Type} [CommRing A] {I : Ideal A} {x y : ℕ} (hx : (x : A) ∈ I) (hy : (y : A) ∈ I) :
    ((Nat.gcd x y : ℕ) : A) ∈ I := by
  have h : ((Nat.gcd x y : ℕ) : A) = (x : A) * (Nat.gcdA x y : A) + (y : A) * (Nat.gcdB x y : A) := by
    have := congrArg (Int.cast : ℤ → A) (Nat.gcd_eq_gcd_ab x y)
    push_cast at this
    exact this
  rw [h]
  exact I.add_mem (I.mul_mem_right _ hx) (I.mul_mem_right _ hy)

private theorem natCast_mem_of_isGen {A : Type} [CommRing A] {a : A} {N : ℕ} {𝔞 : Ideal A} (h : IsGen a N 𝔞) :
    (N : A) ∈ 𝔞 := by
  unfold IsGen at h
  have hN : (N : A) ∈ Ideal.span {(N : A)} := Ideal.mem_span_singleton_self _
  rw [← h] at hN
  have hle : (Ideal.span {a} ⊔ Ideal.span {(N : A)}) * 𝔞 ≤ 𝔞 := Ideal.mul_le_right
  exact hle hN

theorem UpperTheory.Gal.FiniteEtaleModels.numSplit_holds :
    NumSplit := by
  intro A _ _ _ 𝔟₁ 𝔟₂ M₁ M₂ Q a₁ a₂ hM₁ hM₂ hle h₁ h₂ hQ
  have hgM₁ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₁ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgM₂ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ M₂ := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hgQ : Nat.gcd Q (Nat.gcd M₁ M₂) ∣ Q := Nat.gcd_dvd_left _ _
  have hg_mem : ((Nat.gcd Q (Nat.gcd M₁ M₂) : ℕ) : A) ∈ 𝔟₂ :=
    natCast_gcd_mem (hle hQ) (natCast_gcd_mem (hle (natCast_mem_of_isGen h₁)) (natCast_mem_of_isGen h₂))
  have hgpos : 0 < Nat.gcd Q (Nat.gcd M₁ M₂) := Nat.pos_of_dvd_of_pos hgM₂ hM₂
  generalize Nat.gcd Q (Nat.gcd M₁ M₂) = g at hgM₁ hgM₂ hgQ hg_mem hgpos
  obtain ⟨m₁, hm₁⟩ := hgM₁
  obtain ⟨m₂, hm₂⟩ := hgM₂
  have h1 : a₂ * (g : A) ∈ Ideal.span {(M₂ : A)} := by
    rw [← h₂]
    exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a₂)) hg_mem
  rw [Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have hg0 : (g : A) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hm₂pos : 0 < m₂ := by
    rcases Nat.eq_zero_or_pos m₂ with h | h
    · subst h; omega
    · exact h
  have hm₂0 : (m₂ : A) ≠ 0 := by exact_mod_cast hm₂pos.ne'
  have hM₂c : (M₂ : A) = (g : A) * (m₂ : A) := by rw [hm₂]; push_cast; ring
  have ha : a₂ = (m₂ : A) * c := by
    apply mul_right_cancel₀ hg0
    rw [hc, hM₂c]; ring
  refine ⟨g, m₁, m₂, c, hgQ, hm₁, hm₂, ha, ?_⟩
  unfold IsGen at h₂ ⊢
  have hs : Ideal.span {(m₂ : A)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm₂0
  apply mul_left_cancel₀ hs
  calc Ideal.span {(m₂ : A)} * ((Ideal.span {c} ⊔ Ideal.span {(g : A)}) * 𝔟₂)
      = (Ideal.span {(m₂ : A)} * Ideal.span {c} ⊔ Ideal.span {(m₂ : A)} * Ideal.span {(g : A)}) * 𝔟₂ := by
        rw [← _root_.mul_assoc, Ideal.mul_sup]
    _ = (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) * 𝔟₂ := by
        rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton, ← ha, hM₂c,
          _root_.mul_comm (m₂ : A)]
    _ = Ideal.span {(M₂ : A)} := h₂
    _ = Ideal.span {(m₂ : A)} * Ideal.span {(g : A)} := by
        rw [Ideal.span_singleton_mul_span_singleton, hM₂c, _root_.mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrEtaK
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.trEtaK_holds :
    TrEtaK := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ c₂ hM1 hM2 x y hxy
  obtain ⟨v, hv, hxv⟩ := hxy
  haveI : IsMonHom ψ := hT.1
  obtain ⟨hM13, hM1c⟩ := M₁.2
  obtain ⟨hM23, hM2c⟩ := M₂.2
  have hne1 : (M₁ : ℕ) ≠ 0 := by omega
  have hne2 : (M₂ : ℕ) ≠ 0 := by omega
  have hne1' := hne1
  have hne2' := hne2
  rw [hM1] at hne1 hM1c
  rw [hM2] at hne2 hM2c
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc10 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne1 (by simp [h0]))
  have hc20 : 0 < c₂ := Nat.pos_of_ne_zero (fun h0 => hne2 (by simp [h0]))
  have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₂, rfl⟩ hM2c
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hM1c
  have hpc : ∀ (f : 𝟙_ (Over X) ⟶ o'.A) (k : ℕ), (f ^ k) ≫ ψ = (f ≫ ψ) ^ k := by
    intro f k
    induction k with
    | zero => rw [_root_.pow_zero, _root_.pow_zero, MonObj.one_comp]
    | succ k ih => rw [_root_.pow_succ, _root_.pow_succ, MonObj.mul_comp, ih]
  set a := o'.eta (c₁ • x) ≫ ψ with ha
  set b := o.eta (c₂ • y) with hb
  have haN : a ^ (M₁ : ℕ) = 1 := by
    rw [ha, ← hpc]
    exact (congrArg (· ≫ ψ) ((GObj.eta_nsmul o' _ _).symm.trans (GObj.eta_ker o' _))).trans
      (MonObj.one_comp ψ)
  have hbN : b ^ (M₂ : ℕ) = 1 := (GObj.eta_nsmul o _ _).symm.trans (GObj.eta_ker o _)
  have hunit : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : Γ(X, ⊤)) := by
    have hR : IsUnit (((M₁ : ℕ) * (M₂ : ℕ) : ℕ) : R) := by
      rw [← map_natCast (algebraMap ℚ R)]
      refine IsUnit.map (algebraMap ℚ R) (IsUnit.mk0 _ ?_)
      exact_mod_cast Nat.mul_ne_zero hne1' hne2'
    have := hR.map ((s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using this
  rw [← _root_.mul_inv_eq_one]
  have hpow : (a * b⁻¹) ^ ((M₁ : ℕ) * (M₂ : ℕ)) = 1 := by
    rw [mul_pow, _root_.inv_pow, _root_.pow_mul, haN, _root_.mul_comm (M₁ : ℕ), _root_.pow_mul, hbN,
      _root_.one_pow, _root_.one_pow, inv_one, _root_.mul_one]
  have := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points X o.A o.ab _ hunit _ (a * b⁻¹) hpow 1 ?_
  · simpa using this
  intro k _ _ ξ
  rw [_root_.pow_one, MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_inv_eq_one]
  rw [show Over.homMk ξ _ = toUnit (Over.mk (ξ ≫ (𝟙_ (Over X)).hom)) from Subsingleton.elim _ _]
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap ((ξ ≫ (𝟙_ (Over X)).hom) ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 k (ξ ≫ (𝟙_ (Over X)).hom) β hβ
  have e1 : I'.ev (M₁ : ℕ) (c₁ • x) = I'.ev (n * κ) x :=
    (KerBy.ev_nsmul _ (I'.add _) c₁ x).trans
      ((congrArg (fun m => I'.ev m x ^ c₁) hM1).trans (I'.tower (n * κ) c₁ (Nat.mul_pos hn0 hκ0) hc10 x))
  have e2 : I''.ev (M₂ : ℕ) (c₂ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) c₂ y).trans
      ((congrArg (fun m => I''.ev m y ^ c₂) hM2).trans (I''.tower n c₂ hn0 hc20 y))
  have e3 : I''.ev (n * κ) (κ • y) = I''.ev n y :=
    (KerBy.ev_nsmul _ (I''.add _) κ y).trans (I''.tower n κ hn0 hκ0 y)
  have e4 : I'.ev (n * κ) x ≫ ψ = I''.ev (n * κ) (κ • y) :=
    (hev (n * κ) (Nat.mul_pos hn0 hκ0) hnκc x (κ • y)).mpr
      ⟨v, hv, by rw [GlobalTheory.HeckeApprox.inAf_nsmul]; exact hxv⟩
  rw [ha, hb, ← Category.assoc]
  exact (congrArg (· ≫ ψ) ((h1 _).trans e1)).trans (e4.trans (e3.trans (e2.symm.trans (h2 _).symm)))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_eq {Λ Q : Type} [AddCommGroup Λ] [Group Q] (E : ℕ → Λ → Q)
    (add : ∀ n x y, E n (x + y) = E n x * E n y) (ker : ∀ n, 0 < n → ∀ x, E n x = 1 ↔ ∃ y, x = n • y)
    (tower : ∀ n m, 0 < n → 0 < m → ∀ x, E (n * m) x ^ m = E n x) {κ m N : ℕ} (hN : N = κ * m) (hκ : 0 < κ)
    (hm : 0 < m) {a b c : Λ} (h : a = b + κ • c) : E κ a = E N (m • b) := by
  have hz : ∀ n, E n 0 = 1 := by
    intro n
    have h0 := add n 0 0
    rw [_root_.add_zero] at h0
    exact (_root_.mul_eq_left.mp h0.symm)
  have hpow : ∀ n (k : ℕ) x, E n (k • x) = E n x ^ k := by
    intro n k x
    induction k with
    | zero => simp [hz]
    | succ k ih => rw [succ_nsmul, add, ih, _root_.pow_succ]
  have hc : E κ (κ • c) = 1 := (ker κ hκ _).mpr ⟨c, rfl⟩
  rw [h, add, hc, _root_.mul_one, hN, hpow, tower κ m hκ hm]

theorem UpperTheory.Gal.FiniteEtaleModels.trKer_holds :
    TrKer := by
  intro p _ D G L R _ _ gb h X s M₁ M₂ o' o ψ hT n κ c₁ hM hsurj f hf Ω _ _ z g hg hgk
  obtain ⟨hM3, hMc⟩ := M₁.2
  have hne : (M₁ : ℕ) ≠ 0 := by omega
  rw [hM] at hne hMc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκ0 : 0 < κ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hc0 : 0 < c₁ := Nat.pos_of_ne_zero (fun h0 => hne (by simp [h0]))
  have hκc : κ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n * c₁, by ring⟩ hMc
  have hnκc : (n * κ).Coprime p := Nat.Coprime.coprime_dvd_left ⟨c₁, rfl⟩ hMc
  obtain ⟨β, hβ⟩ := GlobalTheory.UPel.HT.GenCmp.exists_spMap (z ≫ s)
  obtain ⟨I', I'', h1, h2, hev⟩ := hT.2.2.2.2 Ω z β hβ
  obtain ⟨a, ha⟩ := (I'.onto κ hκ0 g).mp hgk
  have h0 : I''.ev κ 0 = 1 := (I''.ker κ hκ0 0).mpr ⟨0, by simp⟩
  have hψ : I'.ev κ a ≫ ψ = I''.ev κ 0 := by rw [ha, hg, h0]
  obtain ⟨v, hv, hav⟩ := (hev κ hκ0 hκc a 0).mp hψ
  have hin0 : inAf D 0 = 0 := by
    have := GlobalTheory.HeckeApprox.inAf_sub D 0 0
    rw [_root_.sub_zero, _root_.sub_self] at this
    exact this
  rw [hin0, _root_.zero_add] at hav
  have hinv : ∀ y, L.actG h⁻¹ (L.actG h y) = y := by
    intro y
    rw [← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel, map_one, Module.End.one_apply]
  obtain ⟨x, w, hw, hvx⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D (n * κ) (Nat.mul_pos hn0 hκ0) hnκc v hv
  obtain ⟨w', hw', hfx⟩ := hf x
  obtain ⟨w'', hw'', hw''e⟩ := hsurj w hw
  have e2 : κ • L.actG h⁻¹ w = w'' := by rw [← map_nsmul, ← hw''e, hinv]
  have key : inAf D ((show D.La from a) - f x) = κ • (n • (w' + w'')) := by
    have e1 : inAf D a = L.actG h⁻¹ (κ • v) := by rw [← hav, hinv]
    rw [GlobalTheory.HeckeApprox.inAf_sub, e1, hvx, map_nsmul, map_add (f := _), map_nsmul, _root_.smul_add, hfx,
      smul_comm κ (n * κ), e2, smul_smul κ n, mul_comm κ n, _root_.smul_add]
    abel
  have hmem : n • (w' + w'') ∈ LaHat D := AddSubgroup.nsmul_mem _ (AddSubgroup.add_mem _ hw' hw'') n
  obtain ⟨y, hy⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ κ hκ0 hκc _ hmem key
  have hay : (show D.La from a) = f x + κ • y := by rw [← hy]; abel
  refine ⟨x, ?_⟩
  calc g = I'.ev κ a := ha.symm
    _ = I'.ev (M₁ : ℕ) ((n * c₁) • f x) :=
        ev_eq I'.ev I'.add I'.ker I'.tower (by rw [hM]; ring) hκ0 (Nat.mul_pos hn0 hc0) hay
    _ = I'.ev (M₁ : ℕ) (c₁ • n • f x) := by rw [smul_smul, mul_comm n c₁]
    _ = _ := (h1 _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrPull
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open GlobalTheory.UPel.HT.Hecke.PullHecke
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA mem_heckeSubA)

attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Gal.FiniteEtaleModels

theorem trPull : TrPull := by
  intro q _ D R _ b f c k N S S' s s' j o o' ψ o₁ o₁' m m' hT
  obtain ⟨hmon, hact, heta, hgal, ⟨hlb⟩, hck⟩ := hT
  have hc1 : m.φ ≫ o.A.hom = o₁.A.hom ≫ j := m.cart.1.w
  have hc2 : m'.φ ≫ o'.A.hom = o₁'.A.hom ≫ j := m'.cart.1.w
  have hψw : ψ.left ≫ o'.A.hom = o.A.hom := Over.w ψ
  let l : o₁.A.left ⟶ o₁'.A.left := m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, hψw, hc1])
  have hl1 : l ≫ m'.φ = m.φ ≫ ψ.left := m'.cart.1.lift_fst _ _ _
  have hl2 : l ≫ o₁'.A.hom = o₁.A.hom := m'.cart.1.lift_snd _ _ _
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk l hl2
  have hψ₁ : ψ₁.left = l := rfl
  have hext : ∀ {Z : Scheme} (u v : Z ⟶ o₁'.A.left), u ≫ m'.φ = v ≫ m'.φ →
      u ≫ o₁'.A.hom = v ≫ o₁'.A.hom → u = v := fun u v h1 h2 => m'.cart.1.hom_ext h1 h2
  have hl1' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ m'.φ = u ≫ m.φ ≫ ψ.left := by
    intro Z u
    rw [hl1]
  have hl2' : ∀ {Z : Scheme} (u : Z ⟶ o₁.A.left), u ≫ l ≫ o₁'.A.hom = u ≫ o₁.A.hom := by
    intro Z u
    rw [hl2]
  refine ⟨ψ₁, ⟨?_, ?_, ?_, ?_, ?_, hck⟩, hl1⟩
  · apply isMonHom_of_mul
    intro T x y
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · have h1 := m.cart.2 T x y (pushPt hc1 x) (pushPt hc1 y) rfl rfl
      have h2 := m'.cart.2 T (x ≫ ψ₁) (y ≫ ψ₁) (pushPt hc1 x ≫ ψ) (pushPt hc1 y ≫ ψ)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
        (by simp only [Over.comp_left, hψ₁, Category.assoc, hl1]; rfl)
      rw [Category.assoc, hl1', ← h2, ← MonObj.mul_comp, Over.comp_left, h1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · intro a
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    have hA : (o.act.act a).left ≫ ψ.left = ψ.left ≫ (o'.act.act a).left := by
      rw [← Over.comp_left, hact a, Over.comp_left]
    apply hext
    · rw [Category.assoc, hl1', ← Category.assoc, m.act a, Category.assoc, hA,
        Category.assoc, m'.act a, ← Category.assoc l, hl1, Category.assoc]
    · simp only [Category.assoc, hl2', Over.w, hl2]
  · intro x
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, hψ₁]
    apply hext
    · rw [m'.eta x, heta x, Over.comp_left, Category.assoc, hl1', ← Category.assoc (o₁.eta (f x)).left,
        m.eta (f x), Category.assoc]
    · simp only [Category.assoc, hl2', Over.w]
  · have hkey : ∀ y : D.La, (transl (o₁.eta y)).left ≫ m.φ = m.φ ≫ (transl (o.eta y)).left := by
      intro y
      let e : Over.mk (o₁.A.hom ≫ j) ⟶ o.A := pushPt hc1 (𝟙 o₁.A)
      have he : e.left = m.φ := by simp [e, pushPt]
      have h1 := m.cart.2 o₁.A (𝟙 o₁.A) (toUnit o₁.A ≫ o₁.eta y) e (toUnit _ ≫ o.eta y) rfl
        (by simp [m.eta])
      have h2 : e ≫ transl (o.eta y) = e * (toUnit _ ≫ o.eta y) := by
        simp only [transl, MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
      calc (transl (o₁.eta y)).left ≫ m.φ = (e * (toUnit _ ≫ o.eta y)).left := by unfold transl; exact h1.symm
        _ = (e ≫ transl (o.eta y)).left := by rw [h2]
        _ = m.φ ≫ (transl (o.eta y)).left := by rw [Over.comp_left, he]
    have hpb : IsPullback m.φ ψ₁.left ψ.left m'.φ :=
      IsPullback.of_bot (by rw [hψ₁, hl2, hψw]; exact m.cart.1) hl1.symm m'.cart.1
    refine isGaloisCover_of_isPullback hgal hpb ?_ ?_ ?_ ?_ ?_ ?_
    · show (transl (1 : 𝟙_ (Over S') ⟶ o₁.A)).left = _
      rw [transl_one]
      rfl
    · intro a a'
      simp only [Subgroup.coe_mul, transl_mul, Over.comp_left]
    · intro a a' h
      exact Subtype.ext (transl_injective h)
    · rintro ⟨h, x, rfl⟩
      simp only [hψ₁]
      apply hext
      · rw [Category.assoc, hl1', ← Category.assoc, hkey, Category.assoc,
          hgal.inv ⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hl1]
      · simp only [Category.assoc, hl2', Over.w, hl2]
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o.eta (N • f x), mem_heckeSubA o f N x⟩, hkey _⟩
    · rintro ⟨h, x, rfl⟩
      exact ⟨⟨o₁.eta (N • f x), mem_heckeSubA o₁ f N x⟩, hkey _⟩
  · have hsq : sq2 ψ₁ ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply grpScheme_square_hom_ext
      · have e1 : m'.φ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.1
        have e2 : m.φ₂ ≫ (fst o.A o.A).left = (fst o₁.A o₁.A).left ≫ m.φ := m.sq.1
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (fst o'.A o'.A).left
            = (sq2 ψ₁ ≫ (fst o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (fst o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_fst, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (fst o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_fst]
      · have e1 : m'.φ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ m'.φ := m'.sq.2
        have e2 : m.φ₂ ≫ (snd o.A o.A).left = (snd o₁.A o₁.A).left ≫ m.φ := m.sq.2
        calc (sq2 ψ₁ ≫ m'.φ₂) ≫ (snd o'.A o'.A).left
            = (sq2 ψ₁ ≫ (snd o₁'.A o₁'.A).left) ≫ m'.φ := by
              rw [Category.assoc, e1, Category.assoc]
          _ = (snd o₁.A o₁.A).left ≫ m.φ ≫ ψ.left := by
              rw [grpSchemeSquareProductMap_comp_snd, Category.assoc, hψ₁, hl1]
          _ = (m.φ₂ ≫ (snd o.A o.A).left) ≫ ψ.left := by
              rw [e2, Category.assoc]
          _ = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left := by
              rw [Category.assoc, Category.assoc, grpSchemeSquareProductMap_comp_snd]
    have hL1 : (Hecke.lbPow o₁.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hL0 : (Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hL1 (pull_isLB o₁'.isLB (sq2 ψ₁))).1 ?_⟩
    rw [cls_heckePow o₁.isLB, GlobalTheory.CechPic.cls_pull o₁'.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol, GlobalTheory.CechPic.cls_pull o.isLB,
      (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o'.isLB m'.φ₂)).2 m'.pol, GlobalTheory.CechPic.cls_pull o'.isLB,
      ← GlobalTheory.CechPic.pull_comp, hsq, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
      ← (GlobalTheory.CechPic.cls_eq_iff hL0 (pull_isLB o'.isLB (sq2 ψ))).2 hlb,
      cls_heckePow o.isLB, map_nsmul]

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrSame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open GlobalTheory.UPel.HT.HeckeAd (IsTranslA heckeSubA)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.Comp

theorem UpperTheory.Gal.FiniteEtaleModels.trSame_holds :
    TrSame := by
  intro q _ D R _ b f c k N S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨m₁, a₁, e₁, g₁, l₁, -⟩ := h₁
  obtain ⟨m₂, a₂, e₂, g₂, l₂, -⟩ := h₂
  have ep₁ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₁
  have ep₂ := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover g₂
  have kill : ∀ {X : Over S} [GrpObj X] (ψ : o.A ⟶ X), IsMonHom ψ →
      GlobalTheory.ZM.IsGaloisCover (↥(heckeSubA o f N)) (fun h ↦ Over.Hom.left (transl h.1)) (Over.Hom.left ψ) →
      ∀ h ∈ heckeSubA o f N, h ≫ ψ = 1 := by
    intro X _ ψ hψ g h hh
    exact comp_eq_one_of_transl ψ h (g.inv ⟨h, hh⟩)
  obtain ⟨φ, hφ, hφc⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o₂.A _ ψ₁ m₁ g₁ ψ₂ m₂ (kill ψ₂ m₂ g₂)
  obtain ⟨φ', hφ', hφ'c⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₂.A o₁.A _ ψ₂ m₂ g₂ ψ₁ m₁ (kill ψ₁ m₁ g₁)
  have canc : ∀ {X Y : Over S} (π : X ⟶ Y) [Epi π.left] {Z : Over S} (u v : Y ⟶ Z), π ≫ u = π ≫ v → u = v := by
    intro X Y π _ Z u v h
    ext1
    rw [← cancel_epi π.left, ← Over.comp_left, h, Over.comp_left]
  let e : o₁.A ≅ o₂.A :=
    { hom := φ, inv := φ',
      hom_inv_id := canc ψ₁ _ _ (by rw [reassoc_of% hφc, hφ'c, Category.comp_id])
      inv_hom_id := canc ψ₂ _ _ (by rw [reassoc_of% hφ'c, hφc, Category.comp_id]) }
  haveI : IsMonHom e.hom := hφ
  haveI : IsMonHom ψ₁ := m₁
  haveI : IsMonHom ψ₂ := m₂
  have hc : ψ₁.left ≫ φ.left = ψ₂.left := by rw [← Over.comp_left, hφc]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, ?_, ?_⟩, hc⟩
  · intro a
    have t₁ := congrArg Over.Hom.left (a₁ a)
    have t₂ := congrArg Over.Hom.left (a₂ a)
    simp only [Over.comp_left] at t₁ t₂
    rw [← cancel_epi ψ₁.left, ← Category.assoc, ← t₁, Category.assoc, hc, reassoc_of% hc, ← t₂]
  · have hP := o₂.isLB
    have Z : ∀ (u : o₁.A.left ⟶ (G2 o₁.A).left) (v : o₂.A.left ⟶ (G2 o₂.A).left),
        u ≫ sq2 φ = φ.left ≫ v → (∃ t : (o₂.P.pull v).Gen, t.IsGen) →
        ∃ t : ((o₂.P.pull (sq2 φ)).pull u).Gen, t.IsGen := by
      intro u v huv hv
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp, huv,
        GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP v (pull_isLB hP v),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hv, map_zero]
    obtain ⟨l₁⟩ := l₁
    obtain ⟨l₂⟩ := l₂
    have lA := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb o.isLB (fun _ : Fin (k ^ 2 / c) ↦ 𝟙 _) (fun _ ↦ (1 : ℤ))
    have Y : LBIso (o₂.P.pull (sq2 ψ₂)) ((o₂.P.pull (sq2 φ)).pull (sq2 ψ₁)) := by
      rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _),
        GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφc]
    refine _root_.GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt S o.A o₁.A _ ψ₁ o.ab o₁.ab m₁ g₁ o₁.P (o₂.P.pull (sq2 φ)) o₁.isLB
      (pull_isLB o₂.isLB _) o₁.rig₁ o₁.rig₂ ?_ ?_ ?_
    · exact Z _ _ (lift_one_id_grpSchemeSquareProductMap φ) o₂.rig₁
    · exact Z _ _ (lift_id_one_grpSchemeSquareProductMap φ) o₂.rig₂
    · exact LBIso.trans (pull_isLB o₁.isLB _) lA (pull_isLB (pull_isLB hP _) _) (LBIso.symm l₁)
        (LBIso.trans lA (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) l₂ Y)
  · intro y
    rw [e₁ y, e₂ y, Over.comp_left, Over.comp_left, Category.assoc, hc, Category.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPtAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem lev_pow {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : IsEtLevOver o (𝔞 ^ r) 1 l ↔ IsEtLevOver o 𝔞 r l := by
  unfold IsEtLevOver wSub
  simp only [pow_one]

private theorem lev_top {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} :
    IsEtLevOver o (⊤ : Ideal (𝓞 D.F)) 1 (fun _ : D.La => (1 : T ⟶ o.A)) := by
  have hw : ∀ y : D.La, y ∈ wSub D (⊤ : Ideal (𝓞 D.F)) 1 := by
    intro y
    refine Submodule.subset_span ⟨1, by simp, y, ?_⟩
    simp
  refine ⟨fun _ _ => (_root_.mul_one _).symm, fun c _ => ?_, fun _ _ => rfl, fun k _ _ x => ⟨fun y _ => hw y, fun g hg => ⟨0, ?_⟩⟩⟩
  · haveI := o.act.hom c
    exact (MonObj.one_comp _).symm
  · have h1 := hg 1 (by simp)
    rw [map_one, o.act.one, Category.comp_id] at h1
    rw [h1]
    exact MonObj.comp_one _

theorem UpperTheory.Gal.FiniteEtaleModels.ptAll_holds :
    IdealInd → CrtMul → PtAll := by
  intro hI hC p _ D R _ b N 𝔞 r hc he S s o k _ _ x
  have key : ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o (𝔞 ^ r) 1 l := by
    refine hI (𝓞 D.F) (IsEtPlace b)
      (fun 𝔠 => ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o 𝔠 1 l) ?_ ?_ ?_ (𝔞 ^ r)
      (pow_ne_zero _ he.1) ?_
    · exact ⟨_, lev_top o⟩
    · intro w e _ hw
      obtain ⟨l, hl⟩ := GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint p D R b N w e hc hw S s o k x
      exact ⟨l, (lev_pow o w e l).2 hl⟩
    · rintro 𝔟 𝔠 hbc ⟨l₁, h₁⟩ ⟨l₂, h₂⟩
      exact ⟨_, hC p D R b N S s o 𝔟 𝔠 hbc _ l₁ l₂ h₁ h₂⟩
    · intro w hw hle
      exact he.2 w hw (hw.isPrime.le_of_pow_le hle)
  obtain ⟨l, hl⟩ := key
  exact ⟨l, (lev_pow o 𝔞 r l).1 hl⟩
end

