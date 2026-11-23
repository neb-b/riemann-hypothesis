module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0048

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultBasic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem dvd_of_mult {p : ℕ} [Fact p.Prime] {m n : ℕ} (hm : m.Coprime p) {s t t' : AfP p}
    (hs : IsIntAf s) (ht' : IsIntAf t') (e : t * t' = 1) (h : (n : AfP p) * t = (m : AfP p) * s) : m ∣ n := by
  have hpos : 0 < m := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hm)
  refine Int.natCast_dvd_natCast.1 (GlobalTheory.IntDvdAdele.dvd_of_eq_mul_int p m hpos hm (n : ℤ) (s * t')
    (GlobalTheory.HeckeApprox.isInt_mul hs ht') ?_)
  rw [Int.cast_natCast, ← _root_.mul_assoc, ← h, _root_.mul_assoc, e, _root_.mul_one]

theorem UpperTheory.Gal.G3.pMultBasic :
    NuInt → MultBasic := by
  intro hNu p _
  refine ⟨?_, ?_, ?_⟩
  · rintro a c c' hc hc' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    have h : (c : AfP p) * t = (c' : AfP p) * s := ha.symm.trans ha'
    exact Nat.dvd_antisymm (dvd_of_mult hc ht hs' e' h.symm) (dvd_of_mult hc' hs ht' e h)
  · rintro a a' c c' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    refine ⟨t * s, t' * s', GlobalTheory.HeckeApprox.isInt_mul ht hs, GlobalTheory.HeckeApprox.isInt_mul ht' hs', ?_, ?_⟩
    · rw [_root_.mul_mul_mul_comm, e, e', _root_.one_mul]
    · rw [ha, ha', Nat.cast_mul, _root_.mul_mul_mul_comm]
  · intro D G L u hu
    refine ⟨UpperTheory.Gal.G3.mul u, UpperTheory.Gal.G3.mul u⁻¹, hNu p D G L u (UpperTheory.Gal.Int.Geo.integ_of_mem hu),
      hNu p D G L u⁻¹ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hu)),
      Units.mul_inv ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2), ?_⟩
    rw [Nat.cast_one, _root_.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PNuInt
section
set_option autoImplicit false

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Integ)
open scoped TensorProduct

namespace UpperTheory.Gal.G3

variable {p : ℕ} [Fact p.Prime]

private def DvdInt (g : ℤ) (a : AfP p) : Prop := ∃ t : AfP p, IsIntAf t ∧ a = (g : AfP p) * t

private theorem DvdInt.zero (g : ℤ) : DvdInt g (0 : AfP p) :=
  ⟨0, by simpa using isInt_intCast (p := p) 0, by simp⟩

private theorem DvdInt.add {g : ℤ} {a b : AfP p} (ha : DvdInt g a) (hb : DvdInt g b) : DvdInt g (a + b) := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact ⟨s + t, isInt_add hs ht, by ring⟩

private theorem DvdInt.neg {g : ℤ} {a : AfP p} (ha : DvdInt g a) : DvdInt g (-a) := by
  obtain ⟨s, hs, rfl⟩ := ha
  refine ⟨(-1 : ℤ) * s, isInt_mul (isInt_intCast _) hs, ?_⟩
  push_cast; ring

private theorem dvdInt_form (D : Datum p) (g : ℤ) (hg : ∀ x y, g ∣ D.EF x y) (v w : AfP p ⊗[ℚ] VQ D)
    (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : DvdInt g (fAf D v w) := by
  have hgen : ∀ z ∈ {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)},
      ∀ w ∈ LaHat D, DvdInt g (fAf D z w) := by
    rintro z ⟨a, x, ha, rfl⟩ w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      obtain ⟨c, hc⟩ := hg x y
      refine ⟨(c : AfP p) * (a * a'), isInt_mul (isInt_intCast c) (isInt_mul ha ha'), ?_⟩
      simp only [fAf, LinearMap.BilinForm.baseChange_tmul, hc]
      simp [Algebra.smul_def]
      ring
    | zero => rw [map_zero]; exact DvdInt.zero g
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add (f := _)]; exact h₁.add h₂
    | neg w _ h => rw [map_neg]; exact h.neg
  induction hv using AddSubgroup.closure_induction with
  | mem z hz => exact hgen z hz w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact DvdInt.zero g
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact h₁.add h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact h.neg

private theorem exists_form_ne (D : Datum p) : ∃ x y, D.EF x y ≠ 0 := by
  have := D.freeLa
  have := D.finLa
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := ℤ) hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : D.La)
  have h1 : D.EF x ≠ 0 := fun h => hx (D.nondeg (by rw [h, map_zero]))
  obtain ⟨y, hy⟩ := not_forall.1 fun h => h1 (LinearMap.ext h)
  exact ⟨x, y, by simpa using hy⟩

theorem pNuInt : NuInt := by
  intro p _ D G L h hh
  classical
  set I : Ideal ℤ := Ideal.span (Set.range fun q : D.La × D.La => D.EF q.1 q.2) with hI
  set g : ℤ := Submodule.IsPrincipal.generator I with hgdef
  have hspan : I = Ideal.span {g} := (Ideal.span_singleton_generator I).symm
  have hdvd : ∀ x y, g ∣ D.EF x y := fun x y => by
    have : D.EF x y ∈ I := Ideal.subset_span ⟨(x, y), rfl⟩
    rw [hspan] at this
    exact Ideal.mem_span_singleton.1 this
  have hg0 : g ≠ 0 := by
    obtain ⟨x, y, hxy⟩ := exists_form_ne D
    rintro h0
    exact hxy (by simpa [h0] using hdvd x y)
  have key : ∀ z ∈ I, DvdInt g (mul h * (z : AfP p)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hz
      have e := GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L h (inAf D x) (inAf D y)
      have e' : mul h * ((D.EF x y : ℤ) : AfP p) = fAf D (L.actG h (inAf D x)) (L.actG h (inAf D y)) := by
        rw [← form_inAf]; exact e.symm
      simp only [e']
      exact dvdInt_form D g hdvd _ _ (hh _ (inAf_mem D x)) (hh _ (inAf_mem D y))
    | zero => simpa using DvdInt.zero g
    | add a b _ _ ha hb =>
      push_cast
      rw [mul_add]
      exact ha.add hb
    | smul a b _ hb =>
      obtain ⟨t, ht, e⟩ := hb
      refine ⟨(a : AfP p) * t, isInt_mul (isInt_intCast a) ht, ?_⟩
      simp only [smul_eq_mul]
      push_cast
      linear_combination (a : AfP p) * e
  obtain ⟨w, hw, e⟩ := key g (by rw [hspan]; exact Ideal.mem_span_singleton_self g)
  have hu : IsUnit ((g : ℤ) : AfP p) := by
    have : ((g : ℚ)) ≠ 0 := by exact_mod_cast hg0
    have h2 : IsUnit (algebraMap ℚ (AfP p) (g : ℚ)) := (IsUnit.mk0 _ this).map _
    simpa using h2
  have : mul h = w := hu.mul_left_cancel (by rw [mul_comm]; exact e)
  rw [this]
  exact hw

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelArith
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem nsmul_cancel' {V : Type} [AddCommGroup V] [Module ℚ V] {c : ℕ} (hc : c ≠ 0) {a b : V}
    (h : c • a = c • b) : a = b := by
  have h' : (c : ℚ) • a = (c : ℚ) • b := by
    rw [Nat.cast_smul_eq_nsmul ℚ, Nat.cast_smul_eq_nsmul ℚ]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hc) h'

private theorem rel_core {p : ℕ} [Fact p.Prime] {D : Datum p} (F : D.La →+ AfP p ⊗[ℚ] VQ D)
    (hFmem : ∀ z, F z ∈ LaHat D) {Q Q' : Type} [Group Q] [Group Q'] (Φ : Q →* Q')
    (eI : ℕ → D.La → Q) (eJ : ℕ → D.La → Q')
    (addI : ∀ n a b, eI n (a + b) = eI n a * eI n b) (addJ : ∀ n a b, eJ n (a + b) = eJ n a * eJ n b)
    (kerI : ∀ n, 0 < n → ∀ x, eI n x = 1 ↔ ∃ y, x = n • y)
    (kerJ : ∀ n, 0 < n → ∀ x, eJ n x = 1 ↔ ∃ y, x = n • y)
    (towerI : ∀ n m, 0 < n → 0 < m → ∀ x, eI (n * m) x ^ m = eI n x)
    (f : ℕ → D.La →+ D.La) (k : ℕ) (hk0 : 0 < k) (hk : k.Coprime p)
    (honto : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, f n y = k • x + n • z)
    (hrel : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, F (f n x) = k • inAf D x + n • w)
    (hev : ∀ n, 0 < n → n.Coprime p → ∀ x, eJ n x = Φ (eI (n * k) (f (n * k) x)))
    (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (x y : D.La) :
    Φ (eI n x) = eJ n y ↔ ∃ v ∈ LaHat D, F x = inAf D y + n • v := by
  have hpowI : ∀ N, 0 < N → ∀ (m : ℕ) a, eI N (m • a) = eI N a ^ m := by
    intro N hN m a
    induction m with
    | zero =>
      rw [zero_nsmul, pow_zero]
      exact (kerI N hN 0).mpr ⟨0, by simp⟩
    | succ m ih => rw [succ_nsmul, addI, ih, pow_succ]
  have hinAf : ∀ a : D.La, inAf D (n • a) = n • inAf D a := fun a =>
    map_nsmul (GlobalTheory.HeckeApprox.inAfH D) n a
  have hNpos : 0 < n * k := Nat.mul_pos hn hk0
  have hNp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hk
  obtain ⟨y', z, hy'⟩ := honto (n * k) hNpos hNp x
  have hL : Φ (eI n x) = eJ n y' := by
    rw [← towerI n k hn hk0 x, hev n hn hnp y', hy', addI, (kerI (n * k) hNpos ((n * k) • z)).mpr ⟨z, rfl⟩,
      _root_.mul_one, hpowI (n * k) hNpos]
  obtain ⟨v0, hv0, hv0eq⟩ : ∃ v0 ∈ LaHat D, F x = inAf D y' + n • v0 := by
    obtain ⟨w, hw, hFw⟩ := hrel (n * k) hNpos hNp y'
    rw [hy', map_add (f := _), map_nsmul, map_nsmul] at hFw
    refine ⟨w - F z, (LaHat D).sub_mem hw (hFmem z), ?_⟩
    apply nsmul_cancel' (c := k) (Nat.pos_iff_ne_zero.mp hk0)
    have e : k • F x = k • inAf D y' + (n * k) • w - (n * k) • F z := by
      rw [← hFw]
      abel
    rw [e, smul_add, smul_smul, mul_comm k n, smul_sub, add_sub_assoc]
  have hdiff : eJ n y' = eJ n y ↔ eJ n (y' - y) = 1 := by
    have hsplit : eJ n y' = eJ n (y' - y) * eJ n y := by rw [← addJ, sub_add_cancel]
    constructor
    · intro h
      rw [hsplit] at h
      exact mul_right_cancel (h.trans (_root_.one_mul _).symm)
    · intro h
      rw [hsplit, h, _root_.one_mul]
  rw [hL, hdiff, kerJ n hn (y' - y)]
  constructor
  · rintro ⟨z', hz'⟩
    refine ⟨v0 + inAf D z', (LaHat D).add_mem hv0 (GlobalTheory.HeckeApprox.inAf_mem D z'), ?_⟩
    have h1 : inAf D y' - inAf D y = n • inAf D z' := by
      rw [← GlobalTheory.HeckeApprox.inAf_sub, hz', hinAf]
    rw [hv0eq, smul_add, ← h1]
    abel
  · rintro ⟨v, hv, hFv⟩
    apply GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (y' - y) n hn hnp (v - v0) ((LaHat D).sub_mem hv hv0)
    have h2 := hv0eq.symm.trans hFv
    rw [GlobalTheory.HeckeApprox.inAf_sub, smul_sub, sub_eq_sub_iff_add_eq_add, h2, add_comm]

theorem UpperTheory.Gal.G3.pRelArith :
    RelArith := by
  unfold UpperTheory.Gal.G3.RelArith UpperTheory.Gal.G3.Rel
  intro p _ D G L R _ _ gb S s N N' o' o K _ t I J ψ h f u c k hψ hint hsys hrel hev n hn hnp x y
  haveI := hψ
  have hk : k.Coprime p := hsys.2.1
  have hk0 : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    rw [hk0, Nat.coprime_zero_left] at hk
    exact (Fact.out : p.Prime).one_lt.ne' hk
  let Φ : (Over.mk t ⟶ o'.A) →* (Over.mk t ⟶ o.A) :=
    MonoidHom.mk' (fun g => g ≫ ψ) (fun a b => MonObj.mul_comp a b ψ)
  exact rel_core ((L.actG h).toAddMonoidHom.comp (GlobalTheory.HeckeApprox.inAfH D))
    (fun z => hint _ (GlobalTheory.HeckeApprox.inAf_mem D z)) Φ I.ev J.ev I.add J.add I.ker J.ker I.tower f k hk0 hk
    hsys.2.2.2.2.2.2 hrel hev n hn hnp x y
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSysOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open GlobalTheory GlobalTheory.LKMid GlobalTheory.LKRes GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pSysOf :
    NuInt → SysOf := by
  intro hNu p _ D G L g hI
  classical
  set A := L.actG g with hA
  set B := L.actG g⁻¹ with hB
  have hBA : ∀ v, B (A v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hAB : ∀ v, A (B v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hAint : ∀ v ∈ LaHat D, A v ∈ LaHat D := hI
  obtain ⟨j₁, hj₁, hj₁p, hj₁B⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D B
  set ν : AfP p := UpperTheory.Gal.G3.mul g with hν
  set ν' : AfP p := ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) with hν'
  have hνν' : ν * ν' = 1 := Units.mul_inv _
  have hνint : IsIntAf ν := hNu p D G L g hI
  obtain ⟨j₃, hj₃, hj₃p, hj₃ν⟩ := GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p ν'
  set k := j₁ * j₃ with hk
  have hkp : k.Coprime p := Nat.Coprime.mul_left hj₁p hj₃p
  have hk0 : 0 < k := Nat.mul_pos hj₁ hj₃
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := k • B with hh₀
  have hh₀v : ∀ v, h₀ v = k • B v := fun v => rfl
  have hh₀int : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := fun v hv => by
    rw [hh₀v, hk, mul_comm, mul_smul]; exact nsmul_mem (hj₁B v hv) _
  have hh₀A : ∀ v, h₀ (A v) = k • v := fun v => by
    rw [hh₀v, hBA]
  have hAh₀ : ∀ v, A (h₀ v) = k • v := fun v => by
    rw [hh₀v, map_nsmul, hAB]
  have hh₀O : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := fun c v => by
    rw [hh₀v, hh₀v, hB, actG_actAf, map_nsmul]
  set mu : AfP p := (k : AfP p) ^ 2 * ν' with hmu
  have hh₀sim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w := fun v w => by
    simp only [hh₀v, map_nsmul, LinearMap.smul_apply]
    rw [hB, GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L g⁻¹ v w]
    simp only [nsmul_eq_mul, hmu, hν']
    rw [show (((g⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) =
      ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) from rfl]
    ring
  have hmuint : IsIntAf mu := by
    have e : mu = ((j₁ : AfP p) ^ 2 * j₃) * ((j₃ : AfP p) * ν') := by rw [hmu, hk]; push_cast; ring
    rw [e]; exact isInt_mul (isInt_mul (by rw [sq]; exact isInt_mul (isInt_natCast _) (isInt_natCast _))
      (isInt_natCast _)) hj₃ν
  have hmuν : mu * ν = ((k ^ 2 : ℕ) : AfP p) := by
    rw [hmu]; push_cast; linear_combination ((k : AfP p) ^ 2) * hνν'
  obtain ⟨c, ε, ε', hcp, hck, hε, hε', hεε', hmuε⟩ :=
    GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ν (k ^ 2) (pow_pos hk0 2) (Nat.Coprime.pow_left 2 hkp) hmuint hνint hmuν
  obtain ⟨u, hut, hu⟩ := GlobalTheory.T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε'
  obtain ⟨f, hf⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ hh₀int
  have hfe : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, inAf D (f n x) = h₀ (inAf D x) - n • w :=
    fun n hn hnp x => by
      obtain ⟨w, hw, e⟩ := hf n hn hnp x
      exact ⟨w, hw, by rw [e]; abel⟩
  have hmult : IsMult ν (k ^ 2 / c) := by
    refine ⟨ε', ε, hε', hε, by rw [mul_comm]; exact hεε', ?_⟩
    have hc0 : c ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at hck
      exact (pow_pos hk0 2).ne' hck
    have hcu : IsUnit (c : AfP p) := by
      have : IsUnit (algebraMap ℚ (AfP p) (c : ℚ)) :=
        (IsUnit.mk0 (c : ℚ) (Nat.cast_ne_zero.mpr hc0)).map _
      simpa using this
    have e1 : ((k ^ 2 : ℕ) : AfP p) = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hck]
    apply hcu.mul_left_cancel
    have e2 : (c : AfP p) * ε * ν = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← hmuε, hmuν, e1]
    linear_combination ε' * e2 - ((c : AfP p) * ν) * hεε'
  refine ⟨f, u, c, k, ⟨hcp, hkp, hck, ?_, ?_, ?_, ?_⟩, hmult, fun v hv => hh₀int v hv, ?_⟩
  ·
    intro n hn hnp a x
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp (a • x)
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n (a • x) - a • f n x) n hn hnp
      (actAf D a w₂ - w₁) (sub_mem (actAf_mem_laHat D a hw₂) hw₁) (by
        rw [inAf_sub, ← actAf_inAf, e₁, e₂, ← actAf_inAf, hh₀O, map_sub, map_nsmul, smul_sub]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    refine ⟨fun x => ?_, hut n m hn hm hnm⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe (n * m) (Nat.mul_pos hn hm) hnm x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f (n * m) x - f n x) n hn hnp
      (w₂ - m • w₁) (sub_mem hw₂ (nsmul_mem hw₁ m)) (by
        rw [inAf_sub, e₁, e₂, smul_sub, smul_smul]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp
    obtain ⟨hco, β, hβ, hεβ⟩ := hu n hn hnp
    refine ⟨hco, fun x y => ?_⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp y
    have hX := hh₀int _ (inAf_mem D x)
    have hY := hh₀int _ (inAf_mem D y)
    refine IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _
      ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w₂ - fAf D w₁ (h₀ (inAf D y)) +
        (n : AfP p) * fAf D w₁ w₂)
      (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _))
        (formInt_laHat p D _ _ hX hw₂)) (formInt_laHat p D _ _ hw₁ hY))
        (isInt_mul (isInt_natCast n) (formInt_laHat p D _ _ hw₁ hw₂))) ?_
    have e : ((D.EF (f n x) (f n y) : ℤ) : AfP p) = fAf D (inAf D (f n x)) (inAf D (f n y)) :=
      (form_inAf D _ _).symm
    push_cast
    rw [e, e₁, e₂]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    rw [hh₀sim, hmuε, hεβ, form_inAf]
    ring
  ·
    intro n hn hnp x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (A (inAf D x))
      (hAint _ (inAf_mem D x))
    obtain ⟨w', hw', e'⟩ := hfe n hn hnp y
    have e2 : h₀ (inAf D y) = k • inAf D x - n • h₀ w := by
      rw [← hh₀A, e, map_add (f := _), map_nsmul]; abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n y - k • x) n hn hnp
      (-(w' + h₀ w)) (neg_mem (add_mem hw' (hh₀int w hw))) (by
        rw [inAf_sub, e', e2, inAf_nsmul, smul_neg, smul_add]; abel)
    exact ⟨y, z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp x
    obtain ⟨w, hw, e⟩ := hfe n hn hnp x
    refine ⟨-(A w), neg_mem (hAint w hw), ?_⟩
    rw [e, map_sub, map_nsmul, hAh₀, smul_neg]
    abel
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateTwist :
    GSimOf → TateTwist := by
  unfold GSimOf TateTwist
  intro hG p _ D G L R _ _ gb S s N o k _ t I hI u hu
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have hNcop : (N : ℕ).Coprime p := N.2.2
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have hui1 : u⁻¹ ∈ L.KN 1 := inv_mem hu1
  obtain ⟨g, hg⟩ := hG p D G L u⁻¹ hui1
  obtain ⟨J, hJ⟩ := UpperTheory.exists_gTateIso_twist_of_similitude I g
  have intU := UpperTheory.Gal.Int.Geo.integ_of_mem hu1
  have intUi := UpperTheory.Gal.Int.Geo.integ_of_mem hui1
  unfold UpperTheory.Gal.Int.Geo.Integ at intU intUi
  have hcong : L.CongOne (N : ℕ) u⁻¹ := by
    unfold GlobalTheory.LKGeo.Link.KN at hu
    simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
    exact hu.2
  unfold GlobalTheory.LKGeo.Link.CongOne at hcong
  have inv_act : ∀ v, L.actG u⁻¹ (L.actG u v) = v := by
    intro v
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have act_inv : ∀ v, L.actG u (L.actG u⁻¹ v) = v := by
    intro v
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  refine ⟨J, ?_, ?_⟩
  · unfold UpperTheory.Gal.G3.Ind at hI ⊢
    intro y
    rw [hI y, hJ _ hNpos y]
    symm
    refine (HeckeRestrict.ev_eq_iff I _ hNpos (g.f N y) y).mpr ?_
    obtain ⟨w, hw, hgw⟩ := hg N hNpos hNcop y
    obtain ⟨w', hw', hcw⟩ := hcong (inAf D y) (GlobalTheory.HeckeApprox.inAf_mem D y)
    apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ N hNpos hNcop (w' - w) (sub_mem hw' hw)
    have e := hgw.symm.trans hcw
    rw [show inAf D (g.f N y - y) = inAf D (g.f N y) - inAf D y from GlobalTheory.HeckeApprox.inAf_sub D _ _, smul_sub]
    calc inAf D (g.f N y) - inAf D y = (inAf D (g.f N y) + (N : ℕ) • w) - (N : ℕ) • w - inAf D y := by abel
      _ = (inAf D y + (N : ℕ) • w') - (N : ℕ) • w - inAf D y := by rw [e]
      _ = (N : ℕ) • w' - (N : ℕ) • w := by abel
  · unfold UpperTheory.Gal.G3.Rel
    intro n hn hnp x y
    rw [Category.comp_id, hJ n hn y]
    refine (HeckeRestrict.ev_eq_iff I n hn x (g.f n y)).trans ?_
    obtain ⟨w, hw, hgw⟩ := hg n hn hnp y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨L.actG u (inAf D z - w), intU _ (sub_mem (GlobalTheory.HeckeApprox.inAf_mem D z) hw), ?_⟩
      have h1 := GlobalTheory.HeckeApprox.inAf_add D (g.f n y) (n • z)
      have h2 := GlobalTheory.HeckeApprox.inAf_nsmul D n z
      have hx : inAf D x = inAf D (g.f n y) + n • inAf D z :=
        (congrArg (inAf D) (sub_eq_iff_eq_add'.mp hz)).trans (h1.trans (congrArg (inAf D (g.f n y) + ·) h2))
      have e1 : inAf D (g.f n y) = L.actG u⁻¹ (inAf D y) - n • w := by
        rw [hgw]
        abel
      rw [hx, e1, map_add (f := _), map_sub, map_nsmul, map_nsmul, act_inv, map_sub, smul_sub]
      abel
    · rintro ⟨v, hv, hxv⟩
      apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp (w + L.actG u⁻¹ v) (add_mem hw (intUi _ hv))
      have hx : inAf D x = L.actG u⁻¹ (inAf D y) + n • L.actG u⁻¹ v := by
        rw [← map_nsmul, ← map_add (f := _), ← hxv, inv_act]
      refine (GlobalTheory.HeckeApprox.inAf_sub D x (g.f n y)).trans ?_
      rw [hx, hgw, smul_add]
      abel
end

