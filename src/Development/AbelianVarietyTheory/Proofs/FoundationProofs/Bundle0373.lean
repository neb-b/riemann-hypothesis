module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOperatorUpperULCommuteScaleOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0022
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamond
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.ThNHecke

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem inv_natCast_mem (A : ValuationSubring Ω) {l q : ℕ} (hq : q.Prime) (hl : l.Prime) (hql : q ≠ l)
    (hlA : (l : Ω) ∈ A.nonunits) : ((q : Ω))⁻¹ ∈ A := by
  have hcop : Nat.Coprime q l := (Nat.coprime_primes hq hl).mpr hql
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have e : (u : Ω) * (q : Ω) + (v : Ω) * (l : Ω) = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : Ω)) huv
  have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A u)
  have hv : A.valuation (v : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A v)
  have hqle : A.valuation (q : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A q)
  have hl1 : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).mp hlA
  have hq1 : A.valuation (q : Ω) = 1 := by
    refine le_antisymm hqle (not_lt.mp fun hlt => ?_)
    have h1 : A.valuation ((u : Ω) * (q : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hu le_rfl).trans_lt (by rwa [one_mul])
    have h2 : A.valuation ((v : Ω) * (l : Ω)) < 1 := by
      rw [map_mul]; exact (mul_le_mul' hv le_rfl).trans_lt (by rwa [one_mul])
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, map_one] at h3
    exact lt_irrefl _ h3
  rw [← A.valuation_le_one_iff, map_inv₀, hq1, inv_one]

theorem op_mem_B [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (N l w : ℕ) [Fact l.Prime]
    (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (T : Letter) (hT : admitted N l T) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.op N l T b ∈ X.B N l w := by
  obtain ⟨φ, h1, h2⟩ := hj
  have hA := (_root_.GlobalTheory.KZ.kmap_A_stable ε X ε.injective ⟨φ, h2, h1⟩ l).1
  have hNl : Nat.Coprime N l :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).mpr hlN)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.op N l T) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span
      (StabHecke.op_BSet X hA N w (by omega) hNl T hT x hx))
  exact hle hb

theorem isThB_cong [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [hl : Fact l.Prime]
    (l2 : l ≠ 2) (hN : ¬ l ∣ N) (hN1 : 1 ≤ N) (hlA : (l : Ω) ∈ A.nonunits) (n : ℕ) (b : X.Fn l)
    (φ φ' : HahnSeries ℚ Ω) (h1 : IsThB X A N l n b φ) (h2 : IsThB X A N l n b φ') :
    ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨f, hfI, hfc, hfδ, hfD⟩ := h1
  obtain ⟨f', hf'I, hf'c, hf'δ, hf'D⟩ := h2
  obtain ⟨u, hu⟩ := GlobalTheory.Tower.cls_eq_pow X l n f f' (hfc.symm.trans hf'c)
  have hf0 : (f : X.K) ≠ 0 := f.ne_zero
  have hu0 : (u : X.K) ≠ 0 := u.ne_zero
  have hL : (u : X.K) ^ (l ^ n) = (f : X.K)⁻¹ * f' := by rw [hu]; field_simp
  have hT := GlobalTheory.TInv.sl_T_eq X N l n hl.out l2 hN hN1 (u : X.K) hu0 (by
      intro γ hγ; rw [hL, map_mul, map_inv₀, hfI γ hγ, hf'I γ hγ]) (by
      intro δ hδ hδ'
      obtain ⟨g, hgI, hg⟩ := hfδ δ hδ hδ'
      obtain ⟨g', hg'I, hg'⟩ := hf'δ δ hδ hδ'
      have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := by
        intro h0; exact hf0 ((X.sl (ofSL δ)).injective (h0.trans (map_zero _).symm))
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hg; exact mul_ne_zero hf0 hsf hg
      refine ⟨g' / g, ?_, ?_⟩
      · intro γ hγ; rw [map_div₀, hgI γ hγ, hg'I γ hγ]
      · rw [div_pow, ← hg', ← hg, hu, map_mul, map_pow]; field_simp; ring)
  exact GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong X A l hlA n (f : X.K) (u : X.K) hf0 hu0 hT φ φ' hfD (by rw [← hu]; exact hf'D)

end GlobalTheory.ThNHecke


open GlobalTheory.ThNHecke in
theorem GlobalTheory.CyclotomicQExpansion.thN_hecke : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have halg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : l.Prime := Fact.out
  have stab : ∀ T : Letter, admitted N l T → ∀ c : X.Fn l, c ∈ X.B N l w → X.op N l T c ∈ X.B N l w :=
    fun T hT c hc => op_mem_B ε X hj N l w (by omega) hlN T hT c hc
  have dB : ∀ e : ℕ, e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c ∈ X.B N l w :=
    fun e he c hc => stab (Letter.D e) he c hc
  have exL : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) ∧ IsLat 1 (thN X A N l m e c) :=
    fun m e he c hc => _root_.GlobalTheory.CyclotomicQExpansion.thN_isThB Ω ε X A N l hj hl2 hlN (by omega) hlA m w e hw he c hc
  have ex : ∀ (m e : ℕ), e.Coprime N → ∀ c : X.Fn l, c ∈ X.B N l w →
      IsThB X A N l m (X.act l (sgD N l e : Matrix (Fin 2) (Fin 2) ℤ) c) (thN X A N l m e c) :=
    fun m e he c hc => (exL m e he c hc).1
  have uniq : ∀ (m : ℕ) (c : X.Fn l), c ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
      IsThB X A N l m c φ → IsThB X A N l m c φ' → ∀ r, CgA A l m (φ.coeff r) (φ'.coeff r) :=
    fun m c _ φ φ' h h' => isThB_cong X A N l hl2 hlN (by omega) hlA m c φ φ' h h'
  refine ⟨?_, ?_, ?_⟩
  · intro q hqP hqd r
    have hqN : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd hqP).mpr (fun h => hqd (dvd_mul_of_dvd_left h l))
    have hql : q ≠ l := by
      rintro rfl; exact hqd (dvd_mul_left q N)
    have hqinv := inv_natCast_mem A hqP hl hql hlA
    have hTb : X.heckeT N l q b ∈ X.B N l w := stab (Letter.T q) ⟨hqP, hqd⟩ b hb
    have e1 := exL n d hd b hb
    have e2 := exL n (d * q) (Nat.Coprime.mul_left hd hqN) b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l q b))
        (hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)) :=
      GlobalTheory.T.thetaOperator_heckeT_q_eq_U_add_V_twist Ω ε X A N l halg hj (by omega) n w d q hw hqP hqd hqinv hlA hl2 hlN hd b hb _ _ e1.2 e2.2 e1.1 e2.1
    exact uniq n _ (dB d hd _ hTb) _ _ (ex n d hd _ hTb) h2 r
  · intro r
    have hUb : X.heckeU l b ∈ X.B N l w := stab Letter.U trivial b hb
    have e1 := exL (n + 1) d hd b hb
    have h2 : IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b))
        (uq l (thN X A N l (n + 1) d b)) :=
      _root_.GlobalTheory.ThHeckeU.isThB_act_heckeU Ω ε X A N l n w d halg hj hl2 (by omega) hw hlA hd hlN b hb _ e1.2 e1.1
    exact uniq n _ (dB d hd _ hUb) _ _ (ex n d hd _ hUb) h2 r
  · intro a ha r
    have hDb : X.diam N l a b ∈ X.B N l w := stab (Letter.D a) ha b hb
    have h1 := (GlobalTheory.KZ.isThB_act_sgD_diam_iff Ω ε X A N l n w a d ha hd b hb _).mp (ex n d hd _ hDb)
    exact uniq n _ (dB (d * a) (Nat.Coprime.mul_left hd ha) b hb) _ _ h1 (ex n (d * a) (Nat.Coprime.mul_left hd ha) b hb) r
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochains
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section
namespace GlobalTheory.Ord2.SelPerp

theorem phi_bijective : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ), Function.Bijective (GlobalTheory.Ord2.SelPerp.Phi c n) := by
  intro l _ c n
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h : ∀ x : Mn c n, tbA c n (x 0 * y 1 - x 1 * y 0) = 0 := fun x : Mn c n => by
      rw [← Phi_apply, hy]; rfl
    have h1 : y 1 = 0 := GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun a => by simpa using h (Pi.single 0 a)
    have h0 : y 0 = 0 := GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun a => by simpa using h (Pi.single 1 (-a))
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro φ
    let φ' : Mn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ
    obtain ⟨b0, h0⟩ := _root_.GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul l c n (φ'.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 0))
    obtain ⟨b1, h1⟩ := _root_.GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul l c n (φ'.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 1))
    refine ⟨![-b1, b0], ?_⟩
    apply LinearMap.ext
    intro x
    change Phi c n ![-b1, b0] x = φ x
    have e : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
      funext i; fin_cases i <;> simp
    have e2 : φ x = φ' (Pi.single 0 (x 0)) + φ' (Pi.single 1 (x 1)) := by
      rw [← map_add (f := _), ← e]; rfl
    have h0' : φ' (Pi.single 0 (x 0)) = tbA c n (x 0 * b0) := h0 (x 0)
    have h1' : φ' (Pi.single 1 (x 1)) = tbA c n (x 1 * b1) := h1 (x 1)
    rw [Phi_apply, e2, h0', h1', ← map_add (f := _)]
    congr 1
    simp

theorem ord_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∀ y : G ℚ Ω → Mn c n, (∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) B), GlobalTheory.Ord2.SelPerp.Phi c n (y s) = f.1 ⟨s, hs⟩) → ∃ m : Qn c n, ∀ s ∈ Dec (F := ℚ) B, y s 1 = matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s 1 1 * m - m := by
  intro hL l _ Ω _ _ _ c n hn W hint hdet hcont S hN μ hμ B v hB hup f hf y hy
  obtain ⟨m, hm⟩ := GlobalTheory.T.dualCocycle_coboundary_on_stableLine_of_orthogonal hL l Ω c n hn W hint hcont S hN μ hμ B v hB hup f hf
  obtain ⟨w, rfl⟩ := (phi_bijective l c n).2 m
  refine ⟨w 1, fun s hs => ?_⟩
  have h10 : matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s 1 0 = 0 := by
    rw [matQ_apply, ← map_zero (red c n)]
    congr 1
    apply Subtype.ext
    show mat (dual1 W) s 1 0 = 0
    rw [CupCob.mat_dual1 W hdet, Matrix.smul_apply, hup s hs, smul_zero]
  rw [← sub_eq_zero]
  refine GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun u => ?_
  have h := hm ⟨s, hs⟩ u
  have e := _root_.GlobalTheory.Ord2.SelPerp.Phi_equivariant l Ω c n W hint hdet S hN μ hμ s w
  have e' : twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B ⟨s, hs⟩) (Phi c n w) =
      Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ w) := e.symm
  rw [← hy s hs, e', Phi_apply, Phi_apply, Phi_apply, ← map_sub, ← sub_eq_zero, ← map_sub] at h
  rw [← h]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, Pi.single_eq_same, ne_eq, one_ne_zero,
    not_false_eq_true, Pi.single_eq_of_ne]
  ring


set_option maxHeartbeats 1000000 in
theorem sel_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ, μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∃ z : SelD c n W hint S hN A hW.cont μ → (G ℚ Ω → Fin 2 → Qbar l), (∀ x, GwCount.SelN c n S A (dual1 W) (z x)) ∧ ∀ x x', x ≠ x' → ¬ Cob1 c n (dual1 W) ⊤ (z x - z x') := by
  intro hL l _ Ω _ _ _ e S A W hW c hint hN n hn μ hμ
  have hdet := hW.det2
  have hint' := CupCob.dual_representation_integral c W hdet hint
  have hbij : Function.Bijective (Phi c n) := phi_bijective l c n
  set E := LinearEquiv.ofBijective (Phi c n) hbij with hE
  have hΦΨ : ∀ φ, Phi c n (E.symm φ) = φ := fun φ => E.apply_symm_apply φ
  have heq := _root_.GlobalTheory.Ord2.SelPerp.Phi_equivariant l Ω c n W hint hdet S hN μ hμ
  have hΨeq : ∀ s φ, E.symm (twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) φ) =
      matQ c n (dual1 W) hint' s *ᵥ E.symm φ := by
    intro s φ
    apply hbij.1
    rw [hΦΨ, heq, hΦΨ]
  set rho := rhoS c n W hint S hN with hrho_def
  have hcA : ContAction rho := contAction_rhoS c n W hint S hN hW.cont
  let rep : SelD c n W hint S hN A hW.cont μ → Z1 (twDual μ rho) :=
    fun x => Function.surjInv (Submodule.mkQ_surjective _) x.1
  have hrep : ∀ x, Submodule.mkQ _ (rep x) = x.1 := fun x => Function.surjInv_eq (Submodule.mkQ_surjective _) x.1
  let Y : SelD c n W hint S hN A hW.cont μ → G ℚ Ω → Mn c n := fun x s => E.symm ((rep x).1 (toGS Ω (S : Set Pl) s))
  have hY : ∀ x s, Phi c n (Y x s) = (rep x).1 (toGS Ω (S : Set Pl) s) := fun x s => hΦΨ _
  have hYc : ∀ x s t, Y x (s * t) = Y x s + matQ c n (dual1 W) hint' s *ᵥ Y x t := by
    intro x s t
    simp only [Y, map_mul, (rep x).2.2, map_add (f := _), hΨeq]
  refine ⟨fun x s => lftV c n (Y x s), fun x => ?_, fun x x' hne hcob => ?_⟩
  · have hsel0 := (mem_Sel _ _ _ _ _).1 x.2
    refine ⟨⟨?_, fun s i => lftV_mem c n _ i, fun s _ t _ => ?_⟩, fun a ha => ?_, fun q hq hlq => ?_, ?_⟩
    · have h1 : Continuous fun s => (rep x).1 (toGS Ω (S : Set Pl) s) := (rep x).2.1.comp (continuous_toGS Ω _)
      have h2 : Continuous fun s => lftV c n (E.symm ((rep x).1 (toGS Ω (S : Set Pl) s))) :=
        (continuous_of_discreteTopology (f := fun φ => lftV c n (E.symm φ))).comp h1
      exact h2.continuousOn
    · intro i
      dsimp only
      have hb : ∀ i, (lftV c n (Y x s) + mat (dual1 W) s *ᵥ lftV c n (Y x t)) i ∈ c.O := fun i =>
        add_mem (lftV_mem c n _ i) (CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i)
      refine cg_of_red (lftV_mem c n _ i) (hb i) ?_
      have e1 : (⟨(lftV c n (Y x s) + mat (dual1 W) s *ᵥ lftV c n (Y x t)) i, hb i⟩ : c.O) =
          ⟨lftV c n (Y x s) i, lftV_mem c n _ i⟩ +
            ⟨(mat (dual1 W) s *ᵥ lftV c n (Y x t)) i, CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i⟩ := rfl
      rw [e1, map_add (f := _), red_lftV, red_mulVec c n _ (hint' s) _ (lftV_mem c n _), red_lftV, hYc]
      simp only [red_lftV, Pi.add_apply]
      rfl
    · intro i
      have h1 : toGS Ω (S : Set Pl) a = 1 := MonoidHom.mem_ker.1 ha
      have h0 : (rep x).1 1 = 0 := by
        have := (rep x).2.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at this
        exact add_left_cancel (this.symm.trans (add_zero _).symm)
      show Cg n (lftV c n (Y x a) i) 0
      refine cg_of_red (lftV_mem c n _ i) (zero_mem _) ?_
      rw [red_lftV]
      simp only [Y, h1, h0, map_zero, Pi.zero_apply]
      exact (map_zero (red c n)).symm
    · obtain ⟨v0, hA0, hl0⟩ := hW.atL
      have hnot : ¬ IsPlaceOver A q := fun h => hlq ((eq_of_isPlaceOver hA0 h) ▸ hl0)
      have hBq : IsPlaceOver (Av A S ⟨q, hq⟩) q := isPlaceOver_Av A S ⟨q, hq⟩
      have hsel := hsel0 ⟨q, hq⟩
      have hLc : Lc c n W hint S hN A ⟨q, hq⟩ = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) ⟨q, hq⟩))
          ((Ine (F := ℚ) (Av A S ⟨q, hq⟩)).subgroupOf (Dec (F := ℚ) (Av A S ⟨q, hq⟩))) := if_neg hnot
      rw [mem_perpCond, hLc, ← hrep x] at hsel
      obtain ⟨m, hm⟩ := GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal hL l Ω n hn S (Mn c n) rho hcA μ hμ (Av A S ⟨q, hq⟩) q hBq hlq
        (restrictCocycles1 _ (locFam S (Av A S) ⟨q, hq⟩) (continuous_locFam S (Av A S) ⟨q, hq⟩) (rep x)) hsel
      refine ⟨Av A S ⟨q, hq⟩, hBq, lftV c n (E.symm m), lftV_mem c n _, fun s hs i => ?_⟩
      have hsD : s ∈ Dec (F := ℚ) (Av A S ⟨q, hq⟩) := hs.1
      have hms : (rep x).1 (toGS Ω (S : Set Pl) s) = twDual μ rho (toGS Ω (S : Set Pl) s) m - m := hm ⟨s, hsD⟩ hs
      have hb : (mat (dual1 W) s *ᵥ lftV c n (E.symm m) - lftV c n (E.symm m)) i ∈ c.O :=
        sub_mem (CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i) (lftV_mem c n _ i)
      refine cg_of_red (lftV_mem c n _ i) hb ?_
      have e1 : (⟨(mat (dual1 W) s *ᵥ lftV c n (E.symm m) - lftV c n (E.symm m)) i, hb⟩ : c.O) =
          ⟨(mat (dual1 W) s *ᵥ lftV c n (E.symm m)) i, CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i⟩ -
            ⟨lftV c n (E.symm m) i, lftV_mem c n _ i⟩ := rfl
      rw [e1, map_sub, red_mulVec c n _ (hint' s) _ (lftV_mem c n _), red_lftV, red_lftV]
      simp only [red_lftV, Y, hms, map_sub, hΨeq, Pi.sub_apply]
      rfl
    · obtain ⟨v0, hA0, hl0⟩ := hW.atL
      have hv0 : v0 ∈ S := hW.above v0 hl0
      have hAv : Av A S ⟨v0, hv0⟩ = A := if_pos hA0
      have hsel := hsel0 ⟨v0, hv0⟩
      have hLc : Lc c n W hint S hN A ⟨v0, hv0⟩ = ordCond c n W hint S hN (Av A S ⟨v0, hv0⟩) := if_pos hA0
      rw [mem_perpCond, hLc, ← hrep x] at hsel
      have hup : ∀ s ∈ Dec (F := ℚ) (Av A S ⟨v0, hv0⟩), mat W s 1 0 = 0 := by
        rw [hAv]; exact hW.upper
      obtain ⟨m, hm⟩ := ord_perp hL l Ω c n hn W hint hdet hW.cont S hN μ hμ (Av A S ⟨v0, hv0⟩) v0
        (isPlaceOver_Av A S ⟨v0, hv0⟩) hup (restrictCocycles1 _ _ (continuous_locFam S (Av A S) ⟨v0, hv0⟩) (rep x)) hsel
        (Y x) (fun s hs => hY x s)
      rw [hAv] at hm
      refine ⟨lft c n m, (lft c n m).2, fun s hs => ?_⟩
      refine cg_of_red (lftV_mem c n _ 1) (sub_mem (mul_mem (hint' s 1 1) (lft c n m).2) (lft c n m).2) ?_
      rw [red_lftV, hm s hs]
      show _ = red c n (⟨mat (dual1 W) s 1 1, hint' s 1 1⟩ * lft c n m - lft c n m)
      rw [map_sub, map_mul, red_lft]
      rfl
  · apply hne
    obtain ⟨v, hv, hcv⟩ := hcob
    apply Subtype.ext
    rw [← hrep x, ← hrep x', ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    refine (mem_coboundaries1 _ _).2 ⟨Phi c n (fun i => red c n ⟨v i, hv i⟩), fun g => ?_⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    have hs : ∀ i, Cg n (lftV c n (Y x s) i - lftV c n (Y x' s) i) ((mat (dual1 W) s *ᵥ v - v) i) :=
      hcv s (Subgroup.mem_top s)
    have key : Y x s - Y x' s = matQ c n (dual1 W) hint' s *ᵥ (fun i => red c n ⟨v i, hv i⟩) -
        (fun i => red c n ⟨v i, hv i⟩) := by
      funext i
      have h := red_of_cg (sub_mem (lftV_mem c n (Y x s) i) (lftV_mem c n (Y x' s) i))
        (sub_mem (CupCob.mulVec_mem c _ _ (hint' s) hv i) (hv i)) (hs i)
      rw [show (⟨lftV c n (Y x s) i - lftV c n (Y x' s) i, sub_mem (lftV_mem c n (Y x s) i) (lftV_mem c n (Y x' s) i)⟩ : c.O) =
          ⟨lftV c n (Y x s) i, lftV_mem c n _ i⟩ - ⟨lftV c n (Y x' s) i, lftV_mem c n _ i⟩ from rfl,
        show (⟨(mat (dual1 W) s *ᵥ v) i - v i, sub_mem (CupCob.mulVec_mem c _ _ (hint' s) hv i) (hv i)⟩ : c.O) =
          ⟨(mat (dual1 W) s *ᵥ v) i, CupCob.mulVec_mem c _ _ (hint' s) hv i⟩ - ⟨v i, hv i⟩ from rfl,
        map_sub, map_sub, red_lftV, red_lftV, red_mulVec c n _ (hint' s) _ hv] at h
      rw [Pi.sub_apply, Pi.sub_apply, h]
      rfl
    have h2 := congrArg (Phi c n) key
    rw [map_sub, map_sub, hY x s, hY x' s, heq s] at h2
    exact h2

end GlobalTheory.Ord2.SelPerp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClassStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.gw_limit | exact GlobalTheory.Ord2.gw_limit | (intros; apply GlobalTheory.Ord2.gw_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.ZetaPoly.exists_poly | exact GlobalTheory.ZetaPoly.exists_poly | (intros; apply GlobalTheory.ZetaPoly.exists_poly; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CycIne

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  intro l _ Ω _ _ _ A hA m ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Polynomial.C u, ?_, by simp⟩
    intro x hx
    have hxu : x = u := by
      obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
      rw [Polynomial.mem_support_iff, Polynomial.coeff_C] at hn
      rw [Polynomial.coeff_C]
      split_ifs at hn ⊢ with h
      · rfl
      · exact absurd rfl hn
    subst hxu
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨hu, fun s hs => hfix s hs (Units.ext (Subsingleton.elim _ _))⟩
  · obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed l Ω A m ζ hζ u hfix
    have hl : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hlv⟩ := hA
      have := (hv (l : 𝓞 ℚ)).2 hlv
      simpa using this
    let K : Subfield Ω := (IntermediateField.fixedField (Ine (F := ℚ) A)).toSubfield
    have hK : ∀ x, x ∈ K ↔ ∀ s ∈ Ine (F := ℚ) A, s x = x := fun x =>
      IntermediateField.mem_fixedField_iff _ x
    obtain ⟨P, hP, hPe⟩ := _root_.GlobalTheory.exists_integral_poly_of_primitiveRoot_totally_ramified l Ω A hl K
      (fun x hx hx0 => GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation l Ω A hA x hx0 ((hK x).1 hx)) m hm ζ hζ
      (_root_.GlobalTheory.valuation_primitiveRoot_sub_one_pow_totient l Ω A m hm ζ hζ) u hu ⟨Q, fun x hx => (hK x).2 (hQ x hx), hQe⟩
    exact ⟨P, fun x hx => ⟨(hP x hx).1, (hK x).1 (hP x hx).2⟩, hPe⟩

end GlobalTheory.CycIne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalHeightFrobeniusPlaceStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_height_frobenius_place : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (y z d : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (P : Qbar l) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (w : Pl) (B : ValuationSubring Ω) (τ : G ℚ Ω), 1 ≤ n → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B w → l ^ n ∣ normV w - 1 → IsFrob B (normV w) τ → τ ∈ Dec (F := ℚ) B → dt W τ = 1 → Ine (F := ℚ) B ≤ W.ker → IsLocallyConstant ψ → (∃ t ∈ Ine (F := ℚ) B, (ψ t).toAdd = 1) → P ∈ c.O → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → (∀ a ∈ Ine (F := ℚ) B, y a = 0 ∧ z a = 0) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ Ine (F := ℚ) B, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → Continuous d → (∀ s i, d s i ∈ c.O) → (∀ s t, Cv n (d (s * t)) (d s + mat W s *ᵥ d t + ((((ψ s).toAdd.val : ℕ) : Qbar l) * P) • (mat W s *ᵥ y t))) → Cob2 c n (Dec (F := ℚ) B) (fun s t => cup W d z s t - (((ψ s).toAdd.val : ℕ) : Qbar l) * P * eps l s * u t) → Cg n (P * ht W y z u τ) 0 := by
  first | exact @GlobalTheory.Ord2.LocW.local_height_at_frobenius | exact GlobalTheory.Ord2.LocW.local_height_at_frobenius | (intros; apply GlobalTheory.Ord2.LocW.local_height_at_frobenius <;> assumption)
end

