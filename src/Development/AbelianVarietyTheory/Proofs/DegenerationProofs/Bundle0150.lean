module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsProportionalSeriesMatchTorsio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.LabelMatch
section
variable {O : Type} [CommRing O] {N : NumD O}

theorem qEq_mul {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.QEq (p * q) (p' * q') := by
  obtain ⟨z, h1, h2⟩ := h
  obtain ⟨w, h3, h4⟩ := h'
  refine ⟨z + w, ?_, ?_⟩
  · change p'.1.1.toAdd + q'.1.1.toAdd = p.1.1.toAdd + q.1.1.toAdd + _
    rw [h1, h3, smul_add]; abel
  · change p'.1.2 * q'.1.2 = p.1.2 * q.1.2 * _
    rw [h2, h4, N.io_add]; exact mul_mul_mul_comm _ _ _ _

theorem qEq_incl {k k' : ℕ} (p p' : N.QT k) (q q' : N.QT (k * k')) (hk : k' ≠ 0)
    (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) (c : q'.1.1 = p'.1.1 ^ k') (d : q'.1.2 = p'.1.2) :
    N.QEq p p' ↔ N.QEq q q' := by
  refine exists_congr fun z => ?_
  rw [a, b, c, d, toAdd_pow, toAdd_pow, mul_comm k, mul_smul, ← smul_add]
  simp only [← natCast_zsmul]
  exact and_congr_left' (smul_right_inj (Int.natCast_ne_zero.2 hk)).symm

theorem tx_congr [TopologicalSpace O] {m : ℕ} (hm : Odd m) {p p' : N.QT (m ^ 2)} (h : N.QEq p p') :
    N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  exact (tsum_congr fun χ => (_root_.GlobalTheory.Ex.txT_shift O N m hm p p' χ).1 z h1 h2).trans
    ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (h : N.QEq p p') (h' : N.QEq q q') : N.wp p q = N.wp p' q' := by
  rw [WpPairing.wp_congr_left N h, N.wp_swap q p', WpPairing.wp_congr_left N h', ← N.wp_swap]

variable {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La} {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k}

theorem lab_pow (H : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x : La) (m : ℕ) :
    N.QEq (lab k x ^ (m + 1)) (lab k ((m + 1) • x)) := by
  have equiv : ∀ k, Equivalence (N.QEq (k := k)) := by
    intro k
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have E := equiv k
  induction m with
  | zero => rw [zero_add, pow_one, one_smul]; exact E.refl _
  | succ m ih =>
    rw [pow_succ, succ_nsmul x (m + 1)]
    exact E.trans (qEq_mul ih (E.refl _)) (H.1 k hk _ _)

theorem lab_incl (H : Labels N EF ζ lab) {k k' : ℕ} (hk : 0 < k) (hk' : k' ≠ 0) (x : La) (p : N.QT k)
    (q : N.QT (k * k')) (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) :
    N.QEq (lab k x) p ↔ N.QEq (lab (k * k') (k' • x)) q := by
  have hk0 : 0 < k' := Nat.pos_of_ne_zero hk'
  have equiv : ∀ k, Equivalence (N.QEq (k := k)) := by
    intro k
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have E := equiv k
  have E' := equiv (k * k')
  let p₀ : N.QT k := ⟨((lab (k * k') x).1.1, (lab (k * k') x).1.2 ^ k'), by
    have h : (lab (k * k') x).1.2 ^ (k * k') = _ := N.mem_QT.1 (lab (k * k') x).2
    rw [NumD.mem_QT, ← pow_mul, ← h, mul_comm k' k]⟩
  have h0 : N.QEq p₀ (lab k x) := H.2.2.2.1 k k' hk hk0 x p₀ rfl rfl
  have h1 : N.QEq (lab (k * k') x ^ k') (lab (k * k') (k' • x)) := by
    have := lab_pow H (Nat.mul_pos hk hk0) x (k' - 1)
    rwa [Nat.sub_add_cancel hk0] at this
  have h2 := qEq_incl p₀ p (lab (k * k') x ^ k') q hk' rfl rfl a b
  exact ⟨fun h => E'.trans (E'.symm h1) (h2.1 (E.trans h0 h)), fun h => E.trans (E.symm h0) (h2.2 (E'.trans h1 h))⟩

theorem zeta_shift (H : Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x e y : La) :
    ζ k ^ EF (x + k • e) y = ζ k ^ EF x y := by
  rw [← H.2.2.2.2 k hk, ← H.2.2.2.2 k hk]
  exact WpPairing.wp_congr_left N ((H.2.1 k hk _ _).2 ⟨e, rfl⟩) _


omit N lab in
theorem zeta_tower {k k' : ℕ} (h : ζ (k * k') ^ k' = ζ k) (x y : La) :
    ζ (k * k') ^ EF (k' • x) y = ζ k ^ EF x y := by
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, h]
end

theorem exists_match : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), n.Prime → Odd n → (∀ (k : ℕ) (x : La), 0 < k → k • x = 0 → x = 0) → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ k m, 0 < k → 0 < m → ζ (k * m) ^ m = ζ k) → (∀ k m, 0 < k → 0 < m → ζ' (k * m) ^ m = ζ' k) → (∀ j, ζ' (n ^ j) = ζ (n ^ j)) → ∀ c₀ : C, c₀ ≠ 0 → (∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x)) → ∃ mt : GlobalTheory.Ex.Match N N' n, ∀ j p p', mt.r (n ^ j) p p' ↔ ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p' := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n _ hn _ H H' hζ hζ' hζn c₀ hc htx
  have E : ∀ k, Equivalence (N.QEq (k := k)) := by
    intro k
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have E' : ∀ k, Equivalence (N'.QEq (k := k)) := by
    intro k
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N'.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N'.io_add, _root_.mul_assoc]⟩ }
  have hpos : ∀ j, 0 < n ^ j := fun j => pow_pos hn.pos j
  have tr : ∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ N'.QEq (lab' k a) (lab' k b) := fun k hk a b =>
    (H.2.1 k hk a b).trans (H'.2.1 k hk a b).symm
  refine ⟨{
    r := fun k p p' => 0 < k ∧ ∃ x, N.QEq (lab k x) p ∧ N'.QEq (lab' k x) p' ∧ ∀ y, ζ' k ^ EF x y = ζ k ^ EF x y
    tot := fun j p => ?_
    cotot := fun j p' => ?_
    mul := ?_
    eqv := ?_
    inj := ?_
    incl := ?_
    wp := ?_
    c₀ := c₀
    c₀_ne := hc
    tx := ?_ }, fun j p p' => ⟨fun ⟨_, x, a, b, _⟩ => ⟨x, a, b⟩,
      fun ⟨x, a, b⟩ => ⟨hpos j, x, a, b, fun y => by rw [hζn]⟩⟩⟩
  · obtain ⟨x, hx⟩ := H.2.2.1 _ (hpos j) p
    exact ⟨_, hpos j, x, hx, (E' _).refl _, fun y => by rw [hζn]⟩
  · obtain ⟨x, hx⟩ := H'.2.2.1 _ (hpos j) p'
    exact ⟨_, hpos j, x, (E _).refl _, hx, fun y => by rw [hζn]⟩
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', c'⟩
    refine ⟨hk, x + y, (E _).trans ((E _).symm (H.1 k hk x y)) (qEq_mul a a'),
      (E' _).trans ((E' _).symm (H'.1 k hk x y)) (qEq_mul b b'), fun w => ?_⟩
    rw [map_add (f := _), LinearMap.add_apply, zpow_add, zpow_add, c, c']
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ h
    refine ⟨?_, fun h' => ⟨hk, x, (E _).trans a h, (E' _).trans b h', c⟩⟩
    rintro ⟨-, y, a', b', -⟩
    exact (E' _).trans ((E' _).symm b) ((E' _).trans
      ((tr k hk x y).1 ((E _).trans a ((E _).trans h ((E _).symm a')))) b')
  · rintro k p q p' ⟨hk, x, a, b, -⟩ ⟨-, y, a', b', -⟩
    exact (E _).trans ((E _).symm a) ((E _).trans ((tr k hk x y).2 ((E' _).trans b ((E' _).symm b'))) a')
  · intro k k' p p' q q' hk' a b c d
    have hk0 : 0 < k' := Nat.pos_of_ne_zero hk'
    constructor
    · rintro ⟨hk, x, h1, h2, h3⟩
      refine ⟨Nat.mul_pos hk hk0, k' • x, (lab_incl H hk hk' x p q a b).1 h1,
        (lab_incl H' hk hk' x p' q' c d).1 h2, fun y => ?_⟩
      rw [zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0), h3]
    · rintro ⟨hkk, y, h1, h2, h3⟩
      have hk : 0 < k := Nat.pos_of_mul_pos_right hkk
      obtain ⟨x, hx⟩ := H.2.2.1 k hk p
      have h4 : N.QEq (lab _ y) (lab (k * k') (k' • x)) :=
        (E _).trans h1 ((E _).symm ((lab_incl H hk hk' x p q a b).1 hx))
      refine ⟨hk, x, hx, (lab_incl H' hk hk' x p' q' c d).2
        ((E' _).trans ((E' _).symm ((tr _ hkk _ _).1 h4)) h2), fun w => ?_⟩
      obtain ⟨e, rfl⟩ := (H.2.1 _ hkk _ _).1 h4
      have := h3 w
      rwa [zeta_shift H hkk, zeta_shift H' hkk, zeta_tower (hζ k k' hk hk0), zeta_tower (hζ' k k' hk hk0)] at this
  · rintro k p q p' q' ⟨hk, x, a, b, c⟩ ⟨-, y, a', b', -⟩
    rw [← wp_congr a a', ← wp_congr b b', H.2.2.2.2 k hk, H'.2.2.2.2 k hk, c]
  · rintro j p p' ⟨-, x, a, b, -⟩
    rw [tx_congr hn.pow a, tx_congr hn.pow b, htx]

end GlobalTheory.ModelData.LabelMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TraceEqSumFinrank
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.Ex.Arch

variable {E : Type} [Field E] [NumberField E]

theorem exists_types (m : (E →+* ℂ) → ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)),
    (∀ φ, Nat.card {i // ty i = φ} = m φ) ∧ ∀ a : E, ∑ i, ty i a = ∑ φ : E →+* ℂ, (m φ : ℂ) * φ a := by
  classical
  let e := (Fintype.equivFin (Σ φ : E →+* ℂ, Fin (m φ))).symm
  refine ⟨_, fun i => (e i).1, fun φ => ?_, fun a => ?_⟩
  · rw [Nat.card_congr (e.subtypeEquiv (q := fun k => k.1 = φ) fun _ => Iff.rfl),
      Nat.card_congr (Equiv.sigmaSubtype φ)]
    simp
  · rw [e.sum_comp fun k => k.1 a, Fintype.sum_sigma]
    simp

theorem trace_eq_sum_finrank {g : ℕ} (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (a : 𝓞 E) :
    LinearMap.trace ℂ _ (ρ a) = ∑ φ : E →+* ℂ,
      (Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E))) : ℂ) * φ (a : E) := by
  obtain ⟨g', ty, hc, hs⟩ :=
    exists_types fun φ : E →+* ℂ => Module.finrank ℂ (EigenSplit.eigenSub ρ (φ.comp (algebraMap (𝓞 E) E)))
  obtain ⟨h, hh⟩ := PointUnif.exists_equiv_of_finrank_eq (PointUnif.isSplitting_embeddings (E := E))
    (PointUnif.diagRep ty) ρ fun φ => by rw [PointUnif.finrank_eigenSub_diagRep, hc]
  have h1 : ρ a = h.conj (PointUnif.diagRep ty a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hh]
  have h2 : PointUnif.diagRep ty a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [PointUnif.diagRep_apply, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_conj', h2, ← hs]
  simp

theorem typeSt : TypeSt := by
  intro E _ _ _ H D
  let _ := H.starRing
  intro B hB
  classical
  obtain ⟨g, ty, hc, hs⟩ := exists_types fun φ : E →+* ℂ => if φ (H.rt : E) = H.rt0 then D.p else D.q
  have hbar : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, τ (H.bar a : E) = ∑ τ : E →+* ℂ, τ (a : E) := fun a => by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; exact Finset.mem_univ _
    · intro τ _; ext x; simp
    · intro τ _; ext x; simp
    · intro τ _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have := HomTrace.finite_hom B.X
  obtain ⟨h, hh⟩ := PeriodNonempty.exists_diag B.actV ty fun a => by
    let f : (B.X →+ ℂ) →ₗ[ℂ] (B.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ B.actV a ∘ₗ LinearMap.inl ℂ _ _
    have h1 : B.actV a = f.prodMap (B.F a) := LinearMap.ext fun v => rfl
    rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E B.X (H.bar a) f fun _ _ => rfl, hbar,
      trace_eq_sum_finrank, hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have h2 : Module.finrank ℂ (EigenSplit.eigenSub B.F (φ.comp (algebraMap (𝓞 E) E))) + Module.finrank (𝓞 E) B.X =
        if φ (H.rt : E) = H.rt0 then D.p else D.q := by
      have h3 := hB (φ.comp (algebraMap (𝓞 E) E))
      by_cases hφ : φ (H.rt : E) = H.rt0
      · rw [if_pos hφ]; exact h3.trans (if_pos hφ)
      · rw [if_neg hφ]; exact h3.trans (if_neg hφ)
    rw [← h2]
    push_cast
    ring
  exact ⟨g, ty, h, fun φ => ⟨fun hφ => (hc φ).trans (if_pos hφ), fun hφ => (hc φ).trans (if_neg hφ)⟩, hh⟩

end GlobalTheory.Ex.Arch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistIsoTorsionRepresentativeMulEquiv
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.Relabel.TwIso
variable {O : Type} [CommRing O] {N N' : NumD O} {k : ℕ} (β : N.Form k) (u : Oˣ)

def twP (r : Oˣ) (y : N.X) (g : N.Gt) : (N.twist β u).Gt :=
  ⟨g.b, fun z => g.s z * r ^ β.be y z, (N.twG β r g (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩

theorem twistMap_add_mul (r : Oˣ) (y y' : N.X) (g g' : N.Gt) :
    twP β u r (y + y') (g * g') = twP β u r y g * twP β u r y' g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * r ^ β.be (y + y') z =
      g.s z * r ^ β.be y z * (g'.s z * r ^ β.be y' z) / N.θ (N.c z) g.b g'.b
    rw [map_add (f := _), LinearMap.add_apply, zpow_add]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_mul_mul (r r' : Oˣ) (y : N.X) (g g' : N.Gt) :
    twP β u (r * r') y (g * g') = twP β u r y g * twP β u r' y g' :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * g'.s z / N.θ (N.c z) g.b g'.b * (r * r') ^ β.be y z =
      g.s z * r ^ β.be y z * (g'.s z * r' ^ β.be y z) / N.θ (N.c z) g.b g'.b
    rw [mul_zpow]
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel)

theorem twistMap_pow (r : Oˣ) (y : N.X) (g : N.Gt) (m : ℕ) : twP β u r y g ^ m = twP β u (r ^ m) y (g ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero]
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show (1 : Oˣ) = 1 * 1 ^ β.be y z
    simp
  | succ m ih =>
    rw [pow_succ (twP β u r y g) m, ih, ← twistMap_mul_mul, ← pow_succ, ← pow_succ]

theorem twistMap_io (y : N.X) : twP β u u y (N.io y) = (N.twist β u).io y :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show N.τ y z * u ^ β.be y z = (N.twist β u).τ y z
    rw [NumD.twist_τ])

theorem twistMap_nsmul (r : Oˣ) (j : ℕ) (y : N.X) (g : N.Gt) : twP β u r (j • y) g = twP β u (r ^ j) y g :=
  NumD.Gt.ext rfl (funext fun (z : N.X) => by
    show g.s z * r ^ β.be (j • y) z = g.s z * (r ^ j) ^ β.be y z
    rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast])

theorem twistMap_bijective₂ (r : Oˣ) (y : N.X) : Function.Bijective (twP β u r y) := by
  constructor
  · intro g g' h
    have hb : g.b = g'.b := congrArg (fun x => x.b) h
    have hs : ∀ z, g.s z * r ^ β.be y z = g'.s z * r ^ β.be y z :=
      fun z => congrFun (congrArg (fun x => x.s) h) z
    exact NumD.Gt.ext hb (funext fun z => mul_right_cancel (hs z))
  · intro h
    refine ⟨⟨h.b, fun z => h.s z * r⁻¹ ^ β.be y z,
      (N.twG β r⁻¹ ⟨h.b, h.s, h.mult⟩ (fun z => β.be y z) (fun _ _ => map_add _ _ _)).mult⟩, ?_⟩
    refine NumD.Gt.ext rfl (funext fun (z : N.X) => ?_)
    show h.s z * r⁻¹ ^ β.be y z * r ^ β.be y z = h.s z
    rw [inv_zpow, inv_mul_cancel_right]

def isoG {M M' : NumD O} (J : NumD.Iso M M') : M.Gt →* M'.Gt :=
  MonoidHom.mk' (NumD.Hom.ofIso J).img fun g h =>
    (((NumD.Hom.ofIso J).rel_iff _ _).1 (((NumD.Hom.ofIso J).rel_img g).mul ((NumD.Hom.ofIso J).rel_img h))).symm

theorem rel_iff_isoG {M M' : NumD O} (J : NumD.Iso M M') (g : M.Gt) (g' : M'.Gt) : J.Rel g g' ↔ g' = isoG J g := by
  rw [← NumD.Hom.ofIso_rel, NumD.Hom.rel_iff]
  exact Iff.rfl

theorem isoG_io {M M' : NumD O} (J : NumD.Iso M M') (y : M.X) : isoG J (M.io y) = M'.io (J.e y) :=
  (((NumD.Hom.ofIso J).rel_iff _ _).1 ((NumD.Hom.ofIso J).rel_io y)).symm

private theorem eq_of_div_eq_div_div {G : Type*} [CommGroup G] {a b c d x y : G} (h1 : a = b) (h2 : c = d)
    (h : x / y = a / b / (c / d)) : x = y := by
  rw [div_eq_one.mpr h1, div_eq_one.mpr h2, div_one] at h
  exact div_eq_one.mp h

theorem isoG_bijective {M M' : NumD O} (J : NumD.Iso M M') : Function.Bijective (isoG J) := by
  refine ⟨(injective_iff_map_eq_one (isoG J)).2 fun g hg => ?_, fun g' => ?_⟩
  · obtain ⟨hb, hs⟩ := (rel_iff_isoG J g 1).2 hg.symm
    have hgb : g.b = 1 := by
      have h1 : J.φ g.b = 1 := by rw [← hb]; rfl
      exact (MulEquiv.map_eq_one_iff J.φ).1 h1
    refine NumD.Gt.ext hgb (funext fun χ => ?_)
    have h2 := hs χ
    simp only [NumD.Gt.generator_inv_base, hgb, _root_.mul_one, J.h_one, _root_.one_mul] at h2
    show g.s χ = 1
    exact mul_right_cancel (h2.symm.trans (_root_.one_mul _).symm)
  · refine ⟨⟨J.φ.symm g'.b, fun χ => g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)), fun χ χ' => ?_⟩, ?_⟩
    · have hm := g'.mult (J.e χ) (J.e χ')
      have ht := J.θ_eq (M.c χ) (M.c χ') (J.φ.symm g'.b)
      rw [J.c_eq, J.c_eq, ← map_add J.e χ χ'] at hm
      rw [MulEquiv.apply_symm_apply] at ht
      rw [M.c_add]
      refine eq_of_div_eq_div_div hm ht ?_
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel
    · refine ((rel_iff_isoG J _ g').1 ⟨(J.φ.apply_symm_apply _).symm, fun χ => ?_⟩).symm
      show g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) = g'.s (J.e χ) * J.h (M.c χ * J.φ.symm g'.b) /
        (J.h (M.c χ) * J.h (J.φ.symm g'.b)) * J.h (M.c χ) * J.h (J.φ.symm g'.b)
      rw [mul_assoc _ (J.h (M.c χ)), div_mul_cancel]

variable {β u} (J : NumD.Iso (N.twist β u) N')

theorem twJ_elim {r : Oˣ} {j : ℕ} {q : N.QT j} {q' : N'.QT j} (h : TwJ β u r J q q') :
    q'.1.1.toAdd = J.e q.1.1.toAdd ∧ q'.1.2 = isoG J (twP β u r q.1.1.toAdd q.1.2) := by
  obtain ⟨p, ⟨h1, h2, h3⟩, e, hr⟩ := h
  have hp : p.1.2 = twP β u r q.1.1.toAdd q.1.2 := NumD.Gt.ext h2 (funext h3)
  refine ⟨e.trans (congrArg (fun x => J.e (Multiplicative.toAdd x)) h1), ?_⟩
  rw [← hp]
  exact (rel_iff_isoG J _ _).1 hr

def twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q : N.QT j) : (N.twist β u).QT j :=
  ⟨(q.1.1, twP β u r q.1.1.toAdd q.1.2), by
    change twP β u r q.1.1.toAdd q.1.2 ^ j = (N.twist β u).io q.1.1.toAdd
    rw [twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]⟩

def tauHom {r : Oˣ} {j : ℕ} (h : r ^ j = u) : N.QT j →* N'.QT j :=
  MonoidHom.mk' (fun q => ⟨(Multiplicative.ofAdd (J.e q.1.1.toAdd), isoG J (twP β u r q.1.1.toAdd q.1.2)), by
      change isoG J (twP β u r q.1.1.toAdd q.1.2) ^ j = N'.io (J.e q.1.1.toAdd)
      rw [← map_pow, twistMap_pow, h, N.mem_QT.1 q.2, twistMap_io]
      exact isoG_io J _⟩)
    fun q q' => Subtype.ext (Prod.ext (congrArg Multiplicative.ofAdd (map_add J.e q.1.1.toAdd q'.1.1.toAdd))
      ((congrArg (isoG J) (twistMap_add_mul β u r q.1.1.toAdd q'.1.1.toAdd q.1.2 q'.1.2)).trans (map_mul _ _ _)))

theorem tauHom_bijective {r : Oˣ} {j : ℕ} (h : r ^ j = u) : Function.Bijective (tauHom J h) := by
  constructor
  · intro q₁ q₂ hq
    have h1 : J.e q₁.1.1.toAdd = J.e q₂.1.1.toAdd := congrArg (fun q => q.1.1.toAdd) hq
    have h2 : isoG J (twP β u r q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r q₂.1.1.toAdd q₂.1.2) :=
      congrArg (fun q => q.1.2) hq
    have e1 : q₁.1.1.toAdd = q₂.1.1.toAdd := J.e.injective h1
    rw [e1] at h2
    have e2 := (twistMap_bijective₂ β u r _).1 ((isoG_bijective J).1 h2)
    exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective e1) e2)
  · intro q'
    obtain ⟨g', hg'⟩ := (isoG_bijective J).2 q'.1.2
    obtain ⟨g, hg⟩ := (twistMap_bijective₂ β u r (J.e.symm q'.1.1.toAdd)).2 g'
    refine ⟨⟨(Multiplicative.ofAdd (J.e.symm q'.1.1.toAdd), g), ?_⟩, ?_⟩
    · have hq := N'.mem_QT.1 q'.2
      have e0 : twP β u r (J.e.symm q'.1.1.toAdd) g ^ j = twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j) :=
        (twistMap_pow β u r (J.e.symm q'.1.1.toAdd) g j).trans
          (congrArg (fun s => twP β u s (J.e.symm q'.1.1.toAdd) (g ^ j)) h)
      have hq2 : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (g ^ j)) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) e0.symm).trans ((map_pow (isoG J) _ j).trans
          ((congrArg (fun t => isoG J t ^ j) hg).trans ((congrArg (· ^ j) hg').trans hq)))
      have hio : isoG J (twP β u u (J.e.symm q'.1.1.toAdd) (N.io (J.e.symm q'.1.1.toAdd))) = N'.io q'.1.1.toAdd :=
        (congrArg (isoG J) (twistMap_io β u (J.e.symm q'.1.1.toAdd))).trans
          ((isoG_io J _).trans (congrArg N'.io (J.e.apply_symm_apply _)))
      exact N.mem_QT.2 ((twistMap_bijective₂ β u u _).1 ((isoG_bijective J).1 (hq2.trans hio.symm)))
    · refine Subtype.ext (Prod.ext ?_ ?_)
      · show Multiplicative.ofAdd (J.e (J.e.symm q'.1.1.toAdd)) = q'.1.1
        rw [J.e.apply_symm_apply]
        rfl
      · exact (congrArg (isoG J) hg).trans hg'

theorem tauHom_qTriv {r : Oˣ} {j : ℕ} (h : r ^ j = u) (z : N.X) : tauHom J h (N.qTriv j z) = N'.qTriv j (J.e z) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congrArg Multiplicative.ofAdd (map_nsmul J.e j z)
  · exact (congrArg (isoG J) ((twistMap_nsmul β u r j z (N.io z)).trans
      (show twP β u (r ^ j) z (N.io z) = (N.twist β u).io z by rw [h, twistMap_io]))).trans (isoG_io J z)

theorem wp_twQ {r : Oˣ} {j : ℕ} (h : r ^ j = u) (q₁ q₂ : N.QT j) :
    (N.twist β u).wp (twQ (β := β) h q₁) (twQ h q₂) = N.wp q₁ q₂ := by
  show q₁.1.2.s q₂.1.1.toAdd * r ^ β.be q₁.1.1.toAdd q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * r ^ β.be q₂.1.1.toAdd q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b) =
    q₁.1.2.s q₂.1.1.toAdd * cubN N.θ j 1 q₂.1.2.b q₁.1.2.b /
      (q₂.1.2.s q₁.1.1.toAdd * cubN N.θ j 1 q₁.1.2.b q₂.1.2.b)
  rw [β.symm q₂.1.1.toAdd q₁.1.1.toAdd]
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_div]; abel

end GlobalTheory.Relabel.TwIso


open GlobalTheory.Relabel.TwIso in
theorem GlobalTheory.Relabel.twJ_mulEquiv : ∀ (O : Type) [CommRing O] (N N' : NumD O) (k : ℕ) (β : N.Form k) (u : Oˣ) (J : NumD.Iso (N.twist β u) N'), (∀ (r : Oˣ) (j : ℕ), r ^ j = u → ∃ τ : N.QT j ≃* N'.QT j, (∀ q q', τ q = q' ↔ TwJ β u r J q q') ∧ (∀ q₁ q₂, N.QEq q₁ q₂ ↔ N'.QEq (τ q₁) (τ q₂)) ∧ ∀ q₁ q₂, N'.wp (τ q₁) (τ q₂) = N.wp q₁ q₂) ∧ ∀ (r₁ r₂ : Oˣ) (n n' m : ℕ) (q₁ : N.QT n) (q₂ : N.QT n') (q₁' : N'.QT n) (q₂' : N'.QT n'), r₂ ^ m = r₁ → q₁.1.1 = q₂.1.1 → q₁.1.2 = q₂.1.2 ^ m → TwJ β u r₁ J q₁ q₁' → TwJ β u r₂ J q₂ q₂' → q₁'.1.1 = q₂'.1.1 ∧ q₁'.1.2 = q₂'.1.2 ^ m := by
  intro O _ N N' k β u J
  refine ⟨fun r j h => ?_, fun r₁ r₂ n n' m q₁ q₂ q₁' q₂' hr e1 e2 t1 t2 => ?_⟩
  · refine ⟨MulEquiv.ofBijective (tauHom J h) (tauHom_bijective J h), fun q q' => ?_,
      fun q₁ q₂ => ?_, fun q₁ q₂ => ?_⟩
    · show tauHom J h q = q' ↔ _
      constructor
      · rintro rfl
        exact ⟨twQ (β := β) h q, ⟨rfl, rfl, fun _ => rfl⟩, rfl, (rel_iff_isoG J _ _).2 rfl⟩
      · intro ht
        obtain ⟨e, he⟩ := twJ_elim J ht
        refine Subtype.ext (Prod.ext ?_ he.symm)
        exact (congrArg Multiplicative.ofAdd e).symm
    · rw [NumD.qEq_iff, NumD.qEq_iff]
      show (∃ z, q₂ = q₁ * N.qTriv j z) ↔ ∃ z, tauHom J h q₂ = tauHom J h q₁ * N'.qTriv j z
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨J.e z, (map_mul _ _ _).trans (congrArg _ (tauHom_qTriv J h z))⟩
      · rintro ⟨z, hz⟩
        refine ⟨J.e.symm z, (tauHom_bijective J h).1 ?_⟩
        exact hz.trans ((congrArg (tauHom J h q₁ * ·) ((tauHom_qTriv J h (J.e.symm z)).trans
          (congrArg (N'.qTriv j) (J.e.apply_symm_apply z))).symm).trans (map_mul (tauHom J h) q₁ _).symm)
    · have hrel : ∀ q : N.QT j, (NumD.Hom.ofIso J).Rel (twQ (β := β) h q).1.2 (tauHom J h q).1.2 :=
        fun q => (NumD.Hom.ofIso J).rel_img _
      have hw := NumD.Hom.wp_eq (NumD.Hom.ofIso J) (twQ (β := β) h q₁) (twQ (β := β) h q₂)
        (tauHom J h q₁) (tauHom J h q₂) rfl (hrel q₁) rfl (hrel q₂)
      rw [wp_twQ] at hw
      show N'.wp (tauHom J h q₁) (tauHom J h q₂) = _
      rw [hw]
      exact Units.ext rfl
  · obtain ⟨a1, b1⟩ := twJ_elim J t1
    obtain ⟨a2, b2⟩ := twJ_elim J t2
    refine ⟨?_, ?_⟩
    · exact Multiplicative.toAdd.injective
        (a1.trans ((congrArg (fun x => J.e (Multiplicative.toAdd x)) e1).trans a2.symm))
    · rw [b1, b2]
      calc isoG J (twP β u r₁ q₁.1.1.toAdd q₁.1.2) = isoG J (twP β u r₂ q₂.1.1.toAdd q₂.1.2 ^ m) := by
            rw [twistMap_pow, hr, e1, e2]
        _ = _ := map_pow _ _ _
end
end

