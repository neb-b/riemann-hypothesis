module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Mathlib
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HFundinv
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

private theorem sum_shift_mul_neg_indicator_eq_ite (N : ℕ) (m n : Fin N) :
    ∑ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = if n = m then 1 else 0 := by
  have e1 : ∀ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = (if k = m then (if n ≤ k then (1:ℤ) else 0) else 0) - (if (k:ℕ) + 1 = m then (if n ≤ k then (1:ℤ) else 0) else 0) := by
    intro k
    by_cases h1 : (k:ℕ) + 1 = m
    · have : k ≠ m := by intro h; subst h; omega
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero =>
    have : ∀ k : Fin N, ¬ ((k:ℕ) + 1 = 0) := fun k => by omega
    simp only [this, if_false, Finset.sum_const_zero, sub_zero, Fin.le_def, Fin.mk.injEq]
    split_ifs <;> omega
  | succ m =>
    rw [Finset.sum_eq_single ⟨m, by omega⟩]
    · simp only [Fin.le_def, Fin.mk.injEq]
      split_ifs <;> omega
    · intro b _ hb
      have hb' : (b:ℕ) ≠ m := fun h => hb (Fin.ext h)
      have : ¬ ((b:ℕ) + 1 = ((⟨m + 1, hm⟩ : Fin N) : ℕ)) := by simp only [Fin.val_mk]; omega
      rw [if_neg this]
    · simp

theorem h_fundinv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  intro Ψ _ _ N r r'
  refine ⟨?_, fun π => ?_⟩
  · obtain ⟨p, m⟩ := r
    obtain ⟨q, n⟩ := r'
    rw [Fintype.sum_prod_type]
    simp only [rootOnFund, fundOnRoot]
    rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
    by_cases hq : q = p
    · subst hq
      simp only [if_true, true_and, Prod.mk.injEq]
      rw [sum_shift_mul_neg_indicator_eq_ite N m n]
      by_cases h : n = m
      · simp [h]
      · simp [h, Ne.symm h]
    · have : ¬ (p = q) := fun h => hq h.symm
      simp [hq, this]
  · simp [rootOnFund, fundOnRoot, π.injective.eq_iff]

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HSamesing
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

theorem same_orbit_log_height_difference {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A B : HermLine ι)
    (hab : B.a = A.a) (w z : (Σ k, ι k) → ℂ) (r : ℝ) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hs : SameOrbit w z)
    (h : Real.log (A.h w) = Real.log (B.h w) + r) :
    0 < A.h z ∧ 0 < B.h z ∧ Real.log (A.h z) = Real.log (B.h z) + r := by
  obtain ⟨c, hc, rfl⟩ := hs
  have hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw k
    exact ⟨i, fun h0 => hi (by simp [h0])⟩
  have hA := A.pos z hz
  have hB := B.pos z hz
  refine ⟨hA, hB, ?_⟩
  have hC : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [A.smul c z hc, B.smul c z hc, hab, Real.log_mul hC hA.ne', Real.log_mul hC hB.ne'] at h
  linarith

theorem h_samesing_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (hP : P.IsPrime) (f g : MRing ι) (hu : UnitRatio P f g) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (u v : MRing ι) (huv : u * f - v * g ∈ P) (hu0 : evC z u ≠ 0) : evC z v ≠ 0 := by
  intro hv0
  obtain ⟨hf, -, hW⟩ := hu
  let φ : MRing ι →+* ℂ := (MvPolynomial.eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hφ : ∀ h, φ h = evC z h := fun h => rfl
  have hWp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPW : P ≤ RingHom.ker φ := fun h hh => (RingHom.mem_ker).2 (by rw [hφ]; exact hz.2 h hh)
  have hrel : IsRelevant (RingHom.ker φ) := by
    intro k
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun h => hi ?_⟩
    have := (RingHom.mem_ker).1 h
    simpa [φ] using this
  obtain ⟨u', v', -, hv', h'⟩ := hW _ hWp hPW hrel
  have hmem : (u * v' - v * u') * f ∈ P := by
    have e : (u * v' - v * u') * f = v' * (u * f - v * g) - v * (u' * f - v' * g) := by ring
    rw [e]
    exact P.sub_mem (P.mul_mem_left _ huv) (P.mul_mem_left _ h')
  have hin : u * v' - v * u' ∈ P := (hP.mem_or_mem hmem).resolve_right hf
  have h0 : φ (u * v' - v * u') = 0 := by rw [hφ]; exact hz.2 _ hin
  rw [map_sub, map_mul, map_mul, hφ v, hv0, zero_mul, sub_zero] at h0
  have hv'' : φ v' ≠ 0 := fun h => hv' (RingHom.mem_ker.2 h)
  exact mul_ne_zero (by rw [hφ]; exact hu0) hv'' h0

theorem h_samesing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ := by
  intro K _ ι _ K₁ _ ι₁ _ K₂ _ ι₂ _ κ₁ v₁ κ₂ v₂ P P₁ P₂ D σ₁ σ₂ S₁ S₂ Re₁ Re₂ β a₁ a₂ A₁ A₂ A₁' A₂'
    hb₁ hb₂ hp₁ hp₂ ha₁ ha₂ hφ₁ hφ₂ hP hiso
  obtain ⟨f, g, hfg, hdef⟩ := hiso
  refine ⟨f, g, ?_, ?_⟩
  · rw [ha₁, ha₂, ← hp₁.1, ← hp₂.1]
    exact hfg
  · intro z hz hβ x₁ x₂ hs₁ hs₂ hb₁' hb₂' u v huv hu
    have hw₁ := (Re₁.R.mem x₁ x₁ (Re₁.R.mem_U x₁)).1
    have hw₂ := (Re₂.R.mem x₂ x₂ (Re₂.R.mem_U x₂)).1
    obtain ⟨q₁, r₁, e₁⟩ := same_orbit_log_height_difference A₁ (Re₁.ref a₁) ha₁ _ _ _ hw₁ hs₁ (hφ₁ x₁ hb₁')
    obtain ⟨q₂, r₂, e₂⟩ := same_orbit_log_height_difference A₂ (Re₂.ref a₂) ha₂ _ _ _ hw₂ hs₂ (hφ₂ x₂ hb₂')
    have hv := h_samesing_ne P hP.1 f g hfg.2 z hz u v huv hu
    have hd := hdef z ⟨hz, hβ⟩ u v huv hu
    rw [← hp₁.2 z] at q₁ e₁
    rw [← hp₂.2 z] at q₂ e₂
    have hu' : 0 < ‖evC z v‖ / ‖evC z u‖ := div_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 hu)
    rw [Real.log_div (mul_pos hu' q₂).ne' q₁.ne', Real.log_mul hu'.ne' q₂.ne'] at hd
    rw [Real.log_div (mul_pos hu' r₂).ne' r₁.ne', Real.log_mul hu'.ne' r₂.ne']
    linarith

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.IcLineIsoIff
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

set_option linter.unusedSectionVars false

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def icEv (z : (Σ k, ι k) → ℂ) : MRing ι →+* ℂ :=
  (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))

theorem icEv_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) : evC z f = icEv z f := rfl

def IcGood (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)) (d : K → ℤ) (r : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∃ f g : MRing ι, IsLineIso P d 0 f g ∧ ∀ z ∈ Xo, ∃ u v : MRing ι, u * f - v * g ∈ P ∧ icEv z u ≠ 0 ∧
    icEv z v ≠ 0 ∧ ‖icEv z v‖ * r z = ‖icEv z u‖

theorem ic_lineIso_iff (P : Ideal (MRing ι)) (a b : K → ℤ) (f g : MRing ι) :
    IsLineIso P a b f g ↔ IsLineIso P (a - b) 0 f g := by
  simp [IsLineIso]

theorem ic_iff {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) (hX : Xo ⊆ mcPts P)
    (A B : HermLine ι) : IsoLineOn P Xo A B ↔ IcGood P Xo (A.a - B.a) (fun z => B.h z / A.h z) := by
  constructor
  · rintro ⟨f, g, h, hd⟩
    refine ⟨f, g, (ic_lineIso_iff _ _ _ _ _).1 h, fun z hz => ?_⟩
    have hz' := hX hz
    obtain ⟨u, v, hu, hv, huv⟩ := h.2.2.2 (RingHom.ker (icEv z)) (RingHom.ker_isPrime _)
      (fun s hs => hz'.2 s hs) (fun k => by
        obtain ⟨i, hi⟩ := hz'.1 k
        refine ⟨i, fun hh => hi ?_⟩
        simpa [icEv, RingHom.mem_ker] using hh)
    rw [RingHom.mem_ker] at hu hv
    refine ⟨u, v, huv, hu, hv, ?_⟩
    have h0 := hd z hz u v huv hu
    simp only [icEv_eq] at h0
    have hA := A.pos z hz'.1
    have hB := B.pos z hz'.1
    have hu' : 0 < ‖icEv z u‖ := norm_pos_iff.2 hu
    have hv' : 0 < ‖icEv z v‖ := norm_pos_iff.2 hv
    have h1 := Real.eq_one_of_pos_of_log_eq_zero (by positivity) h0.symm
    field_simp at h1 ⊢
    linarith
  · rintro ⟨f, g, h, hd⟩
    refine ⟨f, g, (ic_lineIso_iff _ _ _ _ _).2 h, fun z hz u' v' huv' hu' => ?_⟩
    have hz' := hX hz
    obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
    have h1 : (u * v' - u' * v) * g ∈ P := by
      have := P.sub_mem (P.mul_mem_left u' huv) (P.mul_mem_left u huv')
      convert this using 1
      ring
    have h2 : u * v' - u' * v ∈ P := (hP.1.mem_or_mem h1).resolve_right h.2.2.1
    have h3 : icEv z (u * v' - u' * v) = 0 := hz'.2 _ h2
    rw [map_sub, map_mul, map_mul, sub_eq_zero] at h3
    have h4 : ‖icEv z u‖ * ‖icEv z v'‖ = ‖icEv z u'‖ * ‖icEv z v‖ := by
      rw [← norm_mul, ← norm_mul, h3]
    simp only [icEv_eq] at hu' ⊢
    have hA := A.pos z hz'.1
    have hB := B.pos z hz'.1
    have hu1 : 0 < ‖icEv z u‖ := norm_pos_iff.2 hu
    have hu2 : 0 < ‖icEv z u'‖ := norm_pos_iff.2 hu'
    have hv1 : 0 < ‖icEv z v‖ := norm_pos_iff.2 hv
    have h5 : ‖icEv z v'‖ / ‖icEv z u'‖ = ‖icEv z v‖ / ‖icEv z u‖ := by
      rw [div_eq_div_iff hu2.ne' hu1.ne']
      linarith
    have h6 : ‖icEv z v'‖ / ‖icEv z u'‖ * B.h z / A.h z = 1 := by
      rw [h5, ← he]
      field_simp
    rw [h6, Real.log_one]

theorem ic_one {P : Ideal (MRing ι)} (Xo : Set ((Σ k, ι k) → ℂ)) (hP : IsMultiProjPrime P) :
    IcGood P Xo 0 1 :=
  ⟨1, 1, (i_algebra K ι P hP).1 0, fun z _ => ⟨1, 1, by simp, by simp, by simp, by simp⟩⟩

theorem ic_mul {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d d' : K → ℤ}
    {r r' : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (h' : IcGood P Xo d' r') :
    IcGood P Xo (d + d') (r * r') := by
  obtain ⟨f, g, h, hd⟩ := h
  obtain ⟨f', g', h', hd'⟩ := h'
  refine ⟨f * f', g * g', by simpa using (i_algebra K ι P hP).2.2.2.1 _ _ _ _ _ _ _ _ h h', fun z hz => ?_⟩
  obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
  obtain ⟨u', v', huv', hu', hv', he'⟩ := hd' z hz
  refine ⟨u * u', v * v', ?_, by simp [hu, hu'], by simp [hv, hv'], ?_⟩
  · have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  · rw [map_mul, map_mul, norm_mul, norm_mul, ← he, ← he', Pi.mul_apply]
    ring

theorem ic_inv {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) : IcGood P Xo (-d) r⁻¹ := by
  obtain ⟨f, g, h, hd⟩ := h
  refine ⟨g, f, ?_, fun z hz => ?_⟩
  · have := (ic_lineIso_iff _ _ _ _ _).1 ((i_algebra K ι P hP).2.1 _ _ _ _ h)
    simpa using this
  obtain ⟨u, v, huv, hu, hv, he⟩ := hd z hz
  refine ⟨v, u, by simpa using P.neg_mem huv, hv, hu, ?_⟩
  have hr : r z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he
    exact hu (norm_eq_zero.1 he.symm)
  rw [← he, Pi.inv_apply]
  field_simp

theorem ic_congr {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} {d d' : K → ℤ}
    {r r' : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (hd : d = d') (hr : ∀ z ∈ Xo, r z = r' z) :
    IcGood P Xo d' r' := by
  subst hd
  obtain ⟨f, g, h, hd⟩ := h
  refine ⟨f, g, h, fun z hz => ?_⟩
  rw [← hr z hz]
  exact hd z hz

theorem ic_pow {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (n : ℕ) : IcGood P Xo (n • d) (r ^ n) := by
  induction n with
  | zero => simpa using ic_one Xo hP
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ic_mul hP ih h

theorem ic_zpow {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {d : K → ℤ}
    {r : ((Σ k, ι k) → ℂ) → ℝ} (h : IcGood P Xo d r) (n : ℤ) : IcGood P Xo (n • d) (r ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using ic_pow hP h m
  · simpa using ic_inv hP (ic_pow hP h m)

theorem ic_prod {P : Ideal (MRing ι)} {Xo : Set ((Σ k, ι k) → ℂ)} (hP : IsMultiProjPrime P) {J : Type}
    (s : Finset J) (d : J → K → ℤ) (r : J → ((Σ k, ι k) → ℂ) → ℝ) (h : ∀ j, IcGood P Xo (d j) (r j)) :
    IcGood P Xo (∑ j ∈ s, d j) (∏ j ∈ s, r j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ic_one Xo hP
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact ic_mul hP (h j) ih

end

theorem i_comb : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Xo : Set ((Σ k, ι k) → ℂ)), IsMultiProjPrime P → Xo ⊆ mcPts P → (∀ (J : Type) [Fintype J] (ℓ ℓ' : J → HermLine ι) (n : J → ℤ), (∀ j, IsoLineOn P Xo (ℓ j) (ℓ' j)) → IsoLineOn P Xo (Top.combLine ℓ n) (Top.combLine ℓ' n)) ∧ (∀ A B C : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B C → IsoLineOn P Xo A C) ∧ (∀ A B : HermLine ι, IsoLineOn P Xo A B → IsoLineOn P Xo B A) ∧ ∀ (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (κ : K₁ → K) (v : (Σ k, ι₁ k) → Σ k, ι k) (J : Type) [Fintype J] (ℓ : J → HermLine ι₁) (ℓ' : J → HermLine ι) (n : J → ℤ), IsBlockMap κ v → (∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) → IsPullHerm κ v (Top.combLine ℓ n) (Top.combLine ℓ' n) := by
  intro K _ ι _ P Xo hP hX
  refine ⟨fun J _ ℓ ℓ' n h => ?_, fun A B C h h' => ?_, fun A B h => ?_, ?_⟩
  · rw [ic_iff hP hX]
    refine ic_congr (ic_prod hP Finset.univ _ _ fun j => ic_zpow hP ((ic_iff hP hX _ _).1 (h j)) (n j)) ?_ ?_
    · simp [Top.combLine, smul_sub, Finset.sum_sub_distrib]
    · intro z _
      simp [Top.combLine, div_zpow, Finset.prod_div_distrib]
  · rw [ic_iff hP hX] at h h' ⊢
    refine ic_congr (ic_mul hP h h') (by abel) fun z hz => ?_
    have hB := (B.pos z (hX hz).1).ne'
    have hA := (A.pos z (hX hz).1).ne'
    simp only [Pi.mul_apply]
    field_simp
  · rw [ic_iff hP hX] at h ⊢
    refine ic_congr (ic_inv hP h) (by abel) fun z _ => ?_
    simp
  · intro K₁ _ ι₁ _ κ v J _ ℓ ℓ' n hv h
    refine ⟨?_, fun z' => ?_⟩
    · funext k
      simp only [Top.combLine, Finset.sum_apply, Pi.smul_apply, fun j => (h j).1, pullDeg]
      by_cases hk : ∃ k₁, κ k₁ = k
      · obtain ⟨k₁, rfl⟩ := hk
        simp only [hv.1.extend_apply, Finset.sum_apply, Pi.smul_apply]
      · simp [Function.extend_apply' _ _ _ hk]
    · simp only [Top.combLine, fun j => (h j).2 z']

end PositivityTheory.UnitarySelfGeneration
end

