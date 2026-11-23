module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportModularFamilyGL2ZModWeierstrass
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.WpFam

namespace GlobalTheory.WpFamGL

theorem transport_GL : ∀ (g : ℂ ≃+* ℂ) (N N' w : ℕ) [NeZero N] (a : (ZMod N)ˣ) (A : GL (Fin 2) (ZMod N)) (F F' : GL (Fin 2) (ZMod N) → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N' → N ∣ N' → ZetaAct g N a → IsFam (gact N 1) w F → (∀ α, QConj g N' (F α) (F' (α * dg a))) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → (∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3) → ∀ α, g (F α τ₀ / ω₀ ^ w) = F' (α * A) τ₁ / ω₁ ^ w := by
  classical
  intro g N N' w _ a A F F' τ₀ τ₁ ω₀ ω₁ hN' hdiv hζ hF hFF' hω₀ h4 h6 hwp α
  let e : Fin 2 → Fin 2 → ZMod N := fun i => Pi.single i 1
  let m : Fin 2 × Bool → ℕ := fun s => if s.2 then 3 else 2
  let u : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β =>
    if s.2 then wpd N (vmul (e s.1) (β * 1)) else wp N (vmul (e s.1) (β * 1))
  let u' : Fin 2 × Bool → GL (Fin 2) (ZMod N) → ℍ → ℂ := fun s β => u s (β * dg a)
  have hact : ActBij (gact N 1) := (GlobalTheory.WpFam.Act.isRAct_gact N 1).actBij
  have hu : ∀ s, IsFam (gact N 1) (m s) (u s) := by
    rintro ⟨i, _ | _⟩
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).1
    · simpa [m, u] using (GlobalTheory.WpFamGL.main N 1 (e i)).2
  have huu' : ∀ s β, QConj g N' (u s β) (u' s β) := by
    rintro ⟨i, _ | _⟩ β
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
    · have h := (GlobalTheory.WpFam.ConjExp.qConj_torsion N g a hζ (vmul (e i) β)).2.1
      rw [GlobalTheory.WpFam.Act.vmul_vmul] at h
      simpa [u, u'] using h.of_dvd hN' hdiv
  have hsep : ∀ β, (∀ s, u s β τ₀ = u s α τ₀) → F β τ₀ = F α τ₀ := by
    intro β hβ
    have : β = α := GlobalTheory.WpFam.SepGL.main N τ₀ β α fun i =>
      ⟨by simpa [u] using hβ (i, false), by simpa [u] using hβ (i, true)⟩
    rw [this]
  have hα : α * A * (dg a)⁻¹ * dg a = α * A := by group
  have hval : ∀ s, g (u s α τ₀ / ω₀ ^ m s) = u' s (α * A * (dg a)⁻¹) τ₁ / ω₁ ^ m s := by
    rintro ⟨i, _ | _⟩
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).1
    · simpa [u, u', m, hα, GlobalTheory.WpFam.Act.vmul_vmul] using (hwp (vmul (e i) α)).2
  have key := GlobalTheory.QFam.transport_of_separating g (GL (Fin 2) (ZMod N)) (Fin 2 × Bool) (gact N 1) N' w
    m F (fun β => F' (β * dg a)) u u' τ₀ τ₁ ω₀ ω₁ hN' hact hF hu hFF' huu' hω₀ h4 h6 α
    (α * A * (dg a)⁻¹) hsep hval
  simpa [hα] using key

end GlobalTheory.WpFamGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeLiftSolvesModFrobXiMu
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WinLift

theorem lift_solves_div_frob_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V G0 hP hθ i m
  have ent : ∀ (c : Ainf p O) (i : Fin d ⊕ Fin k) (m : Fin h),
      (V * blk d k c 1 * G0.map WittVector.frobenius) i m =
        ∑ l, V i l * (Sum.elim (fun _ => c) (fun _ => (1 : Ainf p O)) l *
          WittVector.frobenius (G0 l m)) := by
    intro c i m
    rw [Matrix.mul_apply]
    simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h1 : ∀ l, ∃ w : Ainf p O,
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l *
        WittVector.frobenius (G0 l m) = WittVector.frobenius (xi ε) * w := by
    rintro (l | l)
    · exact ⟨_, rfl⟩
    · have hmem : G0 (Sum.inr l) m ∈ RingHom.ker (WittVector.fontaineTheta O p) := hθ l m
      rw [AinfXi.ker_theta hv ε (root_prim hε), Ideal.mem_span_singleton'] at hmem
      obtain ⟨w, hw⟩ := hmem
      exact ⟨WittVector.frobenius w, by rw [← hw, map_mul]; simp; ring⟩
  choose w hw using h1
  have hE : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
      WittVector.frobenius (xi ε) * G0 i m =
        WittVector.frobenius (xi ε) * ((∑ l, V i l * w l) - G0 i m) := by
    rw [ent]
    simp_rw [hw]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdiff : ∀ l : Fin d ⊕ Fin k, Sandwich.mu ε ∣
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
        Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l := by
    rintro (l | l)
    · exact mu_dvd_frob_xi_sub ε
    · simp
  have hmu : Sandwich.mu ε ∣
      (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m := by
    have hPim := hP i m
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPim
    have key : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m -
        ((V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius) i m - (p : Ainf p O) * G0 i m) =
        (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
          Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
            WittVector.frobenius (G0 l m))) -
        (WittVector.frobenius (xi ε) - p) * G0 i m := by
      rw [ent, ent]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    have hR : Sandwich.mu ε ∣ (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε))
        (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
          WittVector.frobenius (G0 l m))) - (WittVector.frobenius (xi ε) - p) * G0 i m :=
      dvd_sub (Finset.dvd_sum fun l _ => Dvd.dvd.mul_left ((hdiff l).mul_right _) _)
        ((mu_dvd_frob_xi_sub ε).mul_right _)
    rw [← key] at hR
    have := dvd_add hR hPim
    rwa [sub_add_cancel] at this
  rw [hE] at hmu ⊢
  exact mul_dvd_mul_left _ (mu_dvd_of_xi_mul F _ hmu)

end GlobalTheory.WinLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraIsotypicPartStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHarishChandra_isotypic_part : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ), IsChar ℂ ℂ A → IsChar ℂ ℂ B → Kills α A → Kills β B → Kills (hcTw t a b α β n) (hc a b A B n) := by
  first | (exact @GlobalTheory.Shin.HcIso.kills_hcTw) | (exact GlobalTheory.Shin.HcIso.kills_hcTw) | (intros; apply GlobalTheory.Shin.HcIso.kills_hcTw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_virtualCharacter_norm_one_support : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → Kills (fun δ => X (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (exact GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (intros; apply GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCocycleUniqueness
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_cocycle_uniqueness : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (E : ℕ → Q → Q → kˣ → Prop), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → ∃ c, E n a b c) → (∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c') → (∀ n m, 0 < n → 0 < m → ∀ (a b : Q) (c : kˣ), a ^ (n * m) = 1 → b ^ (n * m) = 1 → E (n * m) a b c → E n (a ^ m) (b ^ m) (c ^ m)) → ∀ (I : TateIsoO D k Q act E) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q), (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r, (∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) → (∀ r x, ev (r + 1) x ^ p = ev r x) → (∀ r x y, E (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) → ∃ J : GTateIso D.toG k Q act E, ∀ n, 0 < n → n.Coprime p → ∀ y : D.La, J.ev n y = I.ev n y := by
  first | (exact @GlobalTheory.TateGlue.exists_gTateIso) | (exact GlobalTheory.TateGlue.exists_gTateIso) | (intros; apply GlobalTheory.TateGlue.exists_gTateIso <;> assumption)
end

