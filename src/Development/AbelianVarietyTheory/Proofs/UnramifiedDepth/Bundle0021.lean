module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0029
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBtOfTangentOfSeries
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

namespace BtAssembly

variable {R₀ : Type} [CommRing R₀]

private lemma chi_congr {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) {x y : B.G R} (hx : B.map ρ x = 0) (hy : B.map ρ y = 0)
    (h : x = y) : ch.χ ρ hρ ⟨x, hx⟩ = ch.χ ρ hρ ⟨y, hy⟩ := by
  subst h; rfl

private lemma chi_zero {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (h0 : B.map ρ 0 = 0) (k : Fin g) :
    ((ch.χ ρ hρ ⟨0, h0⟩ k : maximalIdeal (R : Type)) : (R : Type)) = 0 := by
  have hsq : (LHom.id R).SqZero := by
    refine ⟨fun a => ⟨a, rfl⟩, ?_⟩
    have : RingHom.ker (LHom.id R).1 = ⊥ := by
      ext a; simp [RingHom.mem_ker, LHom.id]
    rw [this]; simp
  have h := ch.χ_tg ρ hρ (LHom.id R) hsq ρ rfl 0 0 k
  rw [chi_congr ch ρ hρ _ h0 (by simp)] at h
  simpa using h

private lemma chi_nsmul {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (x : B.G R) (hx : B.map ρ x = 0) (n : ℕ)
    (hn : B.map ρ (n • x) = 0) :
    (fun k => ((ch.χ ρ hρ ⟨n • x, hn⟩ k : maximalIdeal (R : Type)) : (R : Type))) =
      nsmulF ch.F (fun k => ((ch.χ ρ hρ ⟨x, hx⟩ k : maximalIdeal (R : Type)) : (R : Type))) n := by
  induction n with
  | zero =>
    funext k
    rw [chi_congr ch ρ hρ hn (map_zero _) (zero_nsmul x), chi_zero]
    rfl
  | succ n ih =>
    have hn' : B.map ρ (n • x) = 0 := by rw [map_nsmul, hx, nsmul_zero]
    have h := ch.χ_add ρ hρ ⟨n • x, hn'⟩ ⟨x, hx⟩
    rw [ih hn'] at h
    rw [chi_congr ch ρ hρ hn (map_add_ker B ρ ⟨n • x, hn'⟩ ⟨x, hx⟩) (succ_nsmul x n)]
    exact h

private lemma nil_of_mem {R K : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ)
    (hK : maximalIdeal (K : Type) = ⊥) (a : maximalIdeal (R : Type)) :
    IsNilpotent (a : (R : Type)) := by
  apply hρ.2
  rw [RingHom.mem_ker]
  have : ρ.1 a ∈ maximalIdeal (K : Type) := fun hu => a.2 (ρ.2.map_nonunit _ hu)
  rw [hK] at this
  exact this

private lemma exists_pow_zero {S : Type} [CommRing S] {g : ℕ} (Y : Fin g → S)
    (h : ∀ l, IsNilpotent (Y l)) : ∃ N : ℕ, ∀ l, Y l ^ N = 0 := by
  choose n hn using h
  refine ⟨∑ l, n l, fun l => pow_eq_zero_of_le ?_ (hn l)⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

private lemma comp_app {R S T : LAlg R₀} (f : LHom R S) (f' : LHom S T) (e : LHom R T)
    (h : f'.comp f = e) (a : (R : Type)) : f'.1 (f.1 a) = e.1 a := by
  subst h; rfl

end BtAssembly


open BtAssembly in
theorem evBt_of_tangent_of_series :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff (Γ k) m ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀} (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvBtStatement D) := by
  intro hTAN hGAM hLAM hWF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  obtain ⟨hK, hρ1, hL⟩ := hLAM D (Fin.pos k)
  have key : ∀ i : D.fin.ι, ∃ F : (D.fin.AAx i : Type), ∀ φ : LHom (D.fin.AAx i) Tw.O,
      φ.comp (D.fin.sO i) = LHom.id Tw.O → ∀ t : TT p g,
      B.map φ (D.fin.y i) = ptOf B D.L.τ (red p g t) →
      (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) = (Tw.q 0).1 (φ.1 F) := by
    intro i
    obtain ⟨Λ, μ, j, ρΛ, hΛ, hμ, hj, -, hψ⟩ := hL i
    obtain ⟨x, hx⟩ := D.sm.onto (B.map ρΛ (B.map μ (D.fin.y i)))
    have hc : B.map D.wd.ρW (p • x) = 0 := by
      rw [map_nsmul, hx, ← map_nsmul, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    have hz : B.map ρΛ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) = 0 := by
      rw [map_sub, ← B.map_comp j ρΛ, hj, ← B.map_comp D.wd.πW, D.wd.ρW_eq, hx, sub_self]
    obtain ⟨N, hN⟩ := exists_pow_zero
      (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)))
      (fun l => nil_of_mem ρΛ hΛ hK _)
    obtain ⟨Γ, hΓ, hΓe⟩ := hGAM p D.ch (D.wd.W : Type)
      (fun l => ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hc⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)))
      (fun l => nil_of_mem D.wd.ρW D.sm.nil hK _) (N * 2)
    obtain ⟨Q, hQ⟩ := hWF D.wd g (Γ k) (hΓ k)
    obtain ⟨F, hF⟩ := hμ (j.1 (D.wd.πW.1 ((D.wd.b⁻¹ : (D.wd.W : Type)ˣ) : (D.wd.W : Type))) *
      MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q)
    refine ⟨F, fun φ hφ t ht => ?_⟩
    obtain ⟨ψ, hψμ, hψj, hψρ⟩ := hψ φ hφ
    obtain ⟨t', ht', h, hw⟩ := hTAN D t
    obtain ⟨w, hw1, hw2⟩ := hw k
    have e1 : B.map D.wd.πW t' = B.map ψ (B.map μ (D.fin.y i)) := by
      rw [ht', ← ht, ← B.map_comp, ← B.map_comp, hψμ]
    have hu : B.map D.wd.ρW (t' - x) = 0 := by
      rw [map_sub, hx, ← D.wd.ρW_eq, B.map_comp, e1, ← B.map_comp ψ, hψρ, sub_self]
    have e2 : B.map D.wd.πW (t' - x) =
        B.map ψ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) := by
      rw [map_sub, map_sub, e1, ← B.map_comp j ψ, hψj, B.map_id]
    have e3 : ∀ l, D.wd.πW.1
        ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) =
        ψ.1 ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)) := by
      intro l
      rw [← D.ch.χ_nat D.wd.ρW D.wd.ρ1 D.sm.nil hρ1 D.wd.πW D.wd.ρW_eq ⟨_, hu⟩ l,
        ← D.ch.χ_nat ρΛ D.wd.ρ1 hΛ hρ1 ψ hψρ ⟨_, hz⟩ l]
      rw [chi_congr D.ch D.wd.ρ1 hρ1 _ _ e2]
    have e4 : ∀ l, ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
        (D.wd.W : Type)) ^ (N * 2) = 0 := by
      intro l
      have : ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
          (D.wd.W : Type)) ^ N ∈ RingHom.ker D.wd.πW.1 := by
        rw [RingHom.mem_ker, map_pow, e3, ← map_pow, hN, map_zero]
      rw [D.wd.ker_πW, Ideal.mem_span_singleton'] at this
      obtain ⟨a, ha⟩ := this
      rw [pow_mul, ← ha, mul_pow, D.wd.p_sq, mul_zero]
    have hpu : B.map D.wd.ρW (p • (t' - x)) = 0 := by rw [map_nsmul, hu, nsmul_zero]
    have e5 := D.ch.χ_add D.wd.ρW D.sm.nil ⟨_, hc⟩ ⟨_, hpu⟩
    rw [chi_nsmul D.ch D.wd.ρW D.sm.nil _ hu p hpu, hΓe _ e4,
      chi_congr D.ch D.wd.ρW D.sm.nil _ h
        (show p • x + p • (t' - x) = p • t' by rw [← nsmul_add, add_sub_cancel])] at e5
    have e6 := congrFun e5 k
    rw [hw2] at e6
    obtain ⟨a, ha⟩ := D.wd.πW_surj (MvPolynomial.eval (fun l => D.wd.πW.1
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type))) Q)
    have e7 := hQ _ (by
      rw [← e6, mul_assoc]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) a ha
    rw [← e6] at e7
    have e8 : D.wd.πW.1 ((D.wd.b : (D.wd.W : Type)) * w - a) = 0 := by
      rw [← D.wd.ann_p, mul_sub, ← mul_assoc, e7, sub_self]
    rw [map_sub, sub_eq_zero] at e8
    have e9 : ψ.1 (MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q) =
        D.wd.πW.1 a := by
      rw [ha]
      have hid : (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type)).comp
          (j.1 : (Tw.R 0 : Type) →+* (Λ : Type)) = RingHom.id _ :=
        RingHom.ext fun b => comp_app j ψ _ hψj b
      have := MvPolynomial.eval₂_comp_left (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type))
        (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q
      rw [hid] at this
      refine this.trans ?_
      rw [MvPolynomial.eval₂_id]
      congr 2
      funext l
      exact (e3 l).symm
    have e10 : (Tw.q 0).1 (φ.1 F) = ψ.1 (μ.1 F) := (comp_app μ ψ _ hψμ F).symm
    rw [e10, hF, map_mul, e9, comp_app j ψ _ hψj, ← hw1, ← e8]
    change _ = D.wd.πW.1 _ * _
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  choose F hF using key
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  have hs := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  have h := hF (D.ptIdx (red p g t)) (D.ptMap (red p g t)) hs.1 t hs.2.1
  have hm : (D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hm
  obtain ⟨r, hr⟩ := hm
  refine ⟨r, ?_⟩
  rw [mul_comm, hr, map_sub]
  rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsBXOfFactorSystems
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section GroupIdentities
variable {M : Type} [CommGroup M]

private lemma mul_rearrange_five {u u' u'' a b c d : M} (h : b * a = d * c) :
    u * u' * a * u'' * b = u * (u' * u'' * c) * d := by
  calc _ = u * u' * u'' * (b * a) := by ac_rfl
    _ = u * u' * u'' * (d * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero {u a b : M} (h : b * a = b * b) : a⁻¹ * u * b = u := by
  rw [← mul_left_cancel h, mul_right_comm, inv_mul_cancel, _root_.one_mul]

private lemma fs_inter {u u' w w' a b c d e f : M} (h : a * b * c = d * e * f) :
    u * u' * e * (w * w' * f) * d = u * w * b * (u' * w' * c) * a := by
  calc _ = u * u' * w * w' * (d * e * f) := by ac_rfl
    _ = u * u' * w * w' * (a * b * c) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_nat {u u' a b c d e : M} (h : a * b = c * d * e) :
    u * u' * a * b = u * c * (u' * d) * e := by
  calc _ = u * u' * (a * b) := by ac_rfl
    _ = u * u' * (c * d * e) := by rw [h]
    _ = _ := by ac_rfl

private lemma fs_zero_nat {a b c : M} (h : a * b = b * b * c) : a⁻¹ * b = c⁻¹ := by
  have h' : a = b * c := by
    apply mul_right_cancel (b := b)
    rw [h]; ac_rfl
  rw [h', mul_inv, mul_right_comm, inv_mul_cancel, _root_.one_mul]

end GroupIdentities

private lemma fs_sigma_eq {A U : Type} {x x' y y' : A} {u u' : U} :
    (⟨x, y, u⟩ : Σ _ : A, Σ _ : A, U) = ⟨x', y', u'⟩ ↔ x = x' ∧ y = y' ∧ u = u' := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma fs_units_fibre {R₀ : Type} [CommRing R₀] {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁}
    {p₂ : LHom F R₂} {f₁ : LHom R₁ R} {f₂ : LHom R₂ R} (h : IsFibreSq p₁ p₂ f₁ f₂)
    (a : (R₁ : Type)ˣ) (b : (R₂ : Type)ˣ)
    (hab : Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) a =
      Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) b) :
    ∃! c : (F : Type)ˣ, Units.map (p₁.1 : (F : Type) →* (R₁ : Type)) c = a ∧
      Units.map (p₂.1 : (F : Type) →* (R₂ : Type)) c = b := by
  obtain ⟨c, ⟨h1, h2⟩, hu⟩ := h.2.2.2 (a : R₁.carrier) (b : R₂.carrier) (congrArg Units.val hab)
  have hc : IsUnit c := p₁.2.map_nonunit c (by
    have : (p₁.1 : F.carrier →+* R₁.carrier) c = a := h1
    rw [this]; exact a.isUnit)
  refine ⟨hc.unit, ⟨Units.ext h1, Units.ext h2⟩, ?_⟩
  rintro c' ⟨e1, e2⟩
  exact Units.ext (hu c' ⟨congrArg Units.val e1, congrArg Units.val e2⟩)

theorem exists_BX_of_factorSystems :
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) := by
  intro R₀ _ B₀ δ t₁ t₂ w hid hcomp h1a h1c h2a h2c hint h1n h2n hww hw1 hwn
  let B : BX R₀ :=
    { B₀ with
      P := fun R _ _ => (R : Type)ˣ
      smul := fun l u => l * u
      one_smul := fun u => _root_.one_mul u
      mul_smul := fun l l' u => _root_.mul_assoc l l' u
      nonempty := fun _ _ _ => ⟨1⟩
      trans := fun u v => ⟨v * u⁻¹, by simp, fun l hl => by rw [← hl]; simp⟩
      pmap := fun {R S} f {x y} u => Units.map (f.1 : (R : Type) →* (S : Type)) u * δ f x y
      pmap_smul := fun f _ _ l u => by rw [map_mul, _root_.mul_assoc]
      pmap_id := fun {R x y} u => heq_of_eq (by rw [hid, _root_.mul_one]; rfl)
      pmap_comp := fun f g _ _ u => heq_of_eq (by rw [hcomp, map_mul, ← _root_.mul_assoc]; rfl)
      add1 := fun {R x x' y} u u' => u * u' * t₁ R x x' y
      add2 := fun {R x y y'} u u' => u * u' * t₂ R x y y'
      zero1 := fun {R} y => (t₁ R 0 0 y)⁻¹
      zero2 := fun {R} x => (t₂ R x 0 0)⁻¹
      addFst_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h1a _ _ _ _ _))
      addSnd_assoc := fun u u' u'' => heq_of_eq (mul_rearrange_five (h2a _ _ _ _ _))
      addFst_comm := fun u u' => heq_of_eq (by rw [h1c, _root_.mul_comm u])
      addSnd_comm := fun u u' => heq_of_eq (by rw [h2c, _root_.mul_comm u])
      zeroFst_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h1a R 0 0 x y))
      zeroSnd_add := fun {R x y} u => heq_of_eq (fs_zero (by
        simpa only [add_zero, zero_add] using h2a R x 0 0 y))
      addFst_smul := fun l l' u u' => by ac_rfl
      addSnd_smul := fun l l' u u' => by ac_rfl
      interchange := fun u u' v v' => fs_inter (hint _ _ _ _ _)
      addFst_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h1n _ _ _ _))
      addSnd_nat := fun f _ _ _ u u' => heq_of_eq (by
        rw [map_mul, map_mul]; exact fs_nat (h2n _ _ _ _))
      zeroFst_nat := fun f y => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h1n f 0 0 y))
      zeroSnd_nat := fun f x => heq_of_eq (by
        rw [map_inv]
        exact fs_zero_nat (by simpa only [add_zero, map_zero] using h2n f x 0 0))
      sw := fun {R x y} u => u * w R x y
      sw_smul := fun l u => _root_.mul_assoc _ _ _
      sw_nat := fun f _ _ u => by rw [map_mul, _root_.mul_assoc, _root_.mul_assoc, hwn]
      swap_addFst := fun u u' => fs_nat (hw1 _ _ _ _)
      sw_sw := fun u => by rw [_root_.mul_assoc, hww, _root_.mul_one]
      fibre_P := by
        intro F R₁ R₂ R p₁ p₂ f₁ f₂ h
        rintro ⟨x₁, y₁, u₁⟩ ⟨x₂, y₂, u₂⟩ e
        obtain ⟨ex, ey, eu⟩ := fs_sigma_eq.1 e
        obtain ⟨x, ⟨rfl, rfl⟩, hx⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h x₁ x₂ ex
        obtain ⟨y, ⟨rfl, rfl⟩, hy⟩ := B₀.fibre_G p₁ p₂ f₁ f₂ h y₁ y₂ ey
        have hsq : f₁.comp p₁ = f₂.comp p₂ := Subtype.ext h.1
        have hδ := (hcomp p₁ f₁ x y).symm.trans (hsq ▸ hcomp p₂ f₂ x y)
        obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := fs_units_fibre h (u₁ / δ p₁ x y) (u₂ / δ p₂ x y) (by
          rw [map_div, map_div, div_eq_div_iff_mul_eq_mul]
          apply mul_right_cancel (b := δ f₁ (B₀.map p₁ x) (B₀.map p₁ y) *
            δ f₂ (B₀.map p₂ x) (B₀.map p₂ y))
          dsimp only at eu
          calc _ = (Units.map (f₁.1 : (R₁ : Type) →* (R : Type)) u₁ *
                δ f₁ (B₀.map p₁ x) (B₀.map p₁ y)) *
                (Units.map (f₂.1 : (R₂ : Type) →* (R : Type)) (δ p₂ x y) *
                δ f₂ (B₀.map p₂ x) (B₀.map p₂ y)) := by ac_rfl
            _ = _ := by rw [eu, ← hδ]; ac_rfl)
        refine ⟨⟨x, y, u⟩, ⟨fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩, fs_sigma_eq.2 ⟨rfl, rfl, ?_⟩⟩, ?_⟩
        · dsimp only
          rw [hu1, div_mul_cancel]
        · dsimp only
          rw [hu2, div_mul_cancel]
        · rintro ⟨x', y', u'⟩ ⟨e1, e2⟩
          obtain ⟨a1, b1, c1⟩ := fs_sigma_eq.1 e1
          obtain ⟨a2, b2, c2⟩ := fs_sigma_eq.1 e2
          obtain rfl := hx x' ⟨a1, a2⟩
          obtain rfl := hy y' ⟨b1, b2⟩
          exact fs_sigma_eq.2 ⟨rfl, rfl, hu u' ⟨eq_div_iff_mul_eq'.2 c1, eq_div_iff_mul_eq'.2 c2⟩⟩ }
  refine ⟨B, fun R => AddEquiv.refl _, fun R _ _ => (1 : (R : Type)ˣ), fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro R x x' y
    exact show (1 : (R : Type)ˣ) * 1 * t₁ R x x' y = t₁ R x x' y * 1 by simp
  · intro R x y y'
    exact show (1 : (R : Type)ˣ) * 1 * t₂ R x y y' = t₂ R x y y' * 1 by simp
  · intro R S f x y
    exact show Units.map (f.1 : (R : Type) →* (S : Type)) 1 * δ f x y = δ f x y * 1 by simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothNilLift

theorem exists_lift_of_nil {R A W K : Type} [CommRing R] [CommRing A] [CommRing W] [CommRing K]
    [Algebra R A] [Algebra R W] [Algebra R K] [Algebra.Smooth R A] (ρ : W →ₐ[R] K)
    (hρ : Function.Surjective ρ) (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (φ : A →ₐ[R] K) :
    ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose w hw using fun i : Fin n => hρ (φ (f (MvPolynomial.X i)))
  let g : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hg : ρ.comp g = φ.comp f := by
    ext i
    simp [g, hw]
  have hg' : ∀ p, ρ (g p) = φ (f p) := fun p => AlgHom.congr_fun hg p
  let J : Ideal W := (RingHom.ker f.toRingHom).map g.toRingHom
  have hJ : J ≤ RingHom.ker ρ := by
    refine Ideal.map_le_iff_le_comap.mpr fun p hp => ?_
    have hp' : f p = 0 := hp
    change ρ (g p) = 0
    rw [hg', hp', map_zero]
  have hJfg : J.FG := hker.map _
  have hJn : IsNilpotent J :=
    (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).mpr fun a ha => hn a (hJ ha)
  let g₀ : (MvPolynomial (Fin n) R ⧸ RingHom.ker f) →ₐ[R] W ⧸ J :=
    Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp g) fun p hp =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.toRingHom hp)
  let E := Ideal.quotientKerAlgEquivOfSurjective hf
  let ψ₀ : A →ₐ[R] W ⧸ J := g₀.comp E.symm.toAlgHom
  have hψ₀ : ∀ p, ψ₀ (f p) = Ideal.Quotient.mk J (g p) := by
    intro p
    have h1 : E.symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change g₀ (E.symm (f p)) = _
    rw [h1]
    rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift J hJn ψ₀
  refine ⟨ψ, AlgHom.ext fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hf a
  have h2 : Ideal.Quotient.mk J (ψ (f p)) = Ideal.Quotient.mk J (g p) :=
    (AlgHom.congr_fun hψ (f p)).trans (hψ₀ p)
  have h3 : ρ (ψ (f p) - g p) = 0 := hJ (Ideal.Quotient.eq.mp h2)
  rw [map_sub, sub_eq_zero] at h3
  change ρ (ψ (f p)) = _
  rw [h3, hg']

theorem exists_point_lift {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀)))
    [Smooth X.hom] {W K : Type} [CommRing W] [CommRing K] [Algebra R₀ W] [Algebra R₀ K]
    [IsLocalRing K] (ρ : W →ₐ[R₀] K) (hρ : Function.Surjective ρ)
    (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (z : sp (R₀ := R₀) K ⟶ X) :
    ∃ y : sp (R₀ := R₀) W ⟶ X, spMap ρ ≫ y = z := by
  let x : Spec (CommRingCat.of K) ⟶ X.left := z.left
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint K))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum K) ⤳ IsLocalRing.closedPoint K :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum K).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hmem
  let a0 : R₀ →+* Γ(X.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ X.hom.appLE ⊤ U le_top).hom
  letI : Algebra R₀ Γ(X.left, U) := a0.toAlgebra
  have hover : hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom a0) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of R₀))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, CommRingCat.ofHom_hom, Spec.map_comp]
  haveI : Algebra.Smooth R₀ Γ(X.left, U) := by
    have h1 : RingHom.Smooth (X.hom.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Smooth) X.hom inferInstance
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R₀))⟩ ⟨U, hU⟩ le_top
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom :=
      RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv.bijective
    exact h2.comp h1
  let φ := x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hφx : Spec.map φ ≫ hU.fromSpec = x := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
      (isAffineOpen_top (Spec (CommRingCat.of K))) hx
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hφ : φ.hom.comp a0 = algebraMap R₀ K := by
    have e : Spec.map (CommRingCat.ofHom (φ.hom.comp a0)) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
      calc Spec.map (CommRingCat.ofHom (φ.hom.comp a0))
          = Spec.map φ ≫ Spec.map (CommRingCat.ofHom a0) := by
            rw [← Spec.map_comp]; rfl
        _ = Spec.map φ ≫ hU.fromSpec ≫ X.hom := by rw [hover]
        _ = x ≫ X.hom := by rw [← Category.assoc, hφx]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := Over.w z
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let φ' : Γ(X.left, U) →ₐ[R₀] K := ⟨φ.hom, fun r => RingHom.congr_fun hφ r⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_of_nil ρ hρ hn φ'
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec) ?_, ?_⟩
  · simp only [sp, Over.mk_hom]
    rw [Category.assoc, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec = x
    rw [← hφx, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact AlgHom.congr_fun hψ a

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    Smooth G.hom → ∀ (K W : LAlg R₀) (ρW : LHom W K), IsNilOver ρW → SM B K W ρW) := by
  intro R₀ _ G _ _ B e hb _ hnat hsm K W ρW hρ
  refine ⟨hρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_point_lift G ρW.1 hρ.1 hρ.2 (e K x)
  obtain ⟨y', rfl⟩ := (hb W).2 y
  exact ⟨y', (hb K).1 (by rw [hnat, hy])⟩

end GlobalTheory.SmoothNilLift
end

