module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0662
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivLiftResiduePadicAlgCl
section
open IsLocalRing

namespace GlobalTheory.ZJ

theorem exists_algEquiv_lift_residue (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l))
    (φ : kb l ≃+* kb l)
    (hφ : ∀ x : OO l, (x : PadicAlgCl l) ∈ L → φ (residue (OO l) x) = residue (OO l) x) :
    ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ x y : OO l,
      residue (OO l) y = φ (residue (OO l) x) → ‖g (x : PadicAlgCl l) - y‖ < 1 := by
  classical
  haveI : IsAlgClosure L (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L⟩
  haveI : IsGalois L (PadicAlgCl l) := {}
  have hmem : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) {x : PadicAlgCl l}, x ∈ OO l → g x ∈ OO l :=
    fun g _ hx => algEquiv_mem_OO (g.restrictScalars ℚ_[l]) hx
  letI : MulSemiringAction (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) :=
    { smul := fun g x => ⟨g x, hmem g x.2⟩
      one_smul := fun _ => Subtype.ext rfl
      mul_smul := fun _ _ _ => Subtype.ext rfl
      smul_zero := fun g => Subtype.ext (map_zero g)
      smul_add := fun g _ _ => Subtype.ext (map_add g _ _)
      smul_one := fun g => Subtype.ext (map_one g)
      smul_mul := fun g _ _ => Subtype.ext (map_mul g _ _) }
  have hsmul : ∀ (g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (x : OO l),
      ((g • x : OO l) : PadicAlgCl l) = g x := fun _ _ => rfl
  let A : Subring (OO l) := L.toSubalgebra.toSubring.comap (OO l).subtype
  have hA : ∀ a : A, (((a : OO l) : PadicAlgCl l)) ∈ L := fun a => a.2
  haveI : SMulCommClass (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) A (OO l) := ⟨fun g a b => by
    apply Subtype.ext
    change g (((a : OO l) : PadicAlgCl l) * b) = ((a : OO l) : PadicAlgCl l) * g b
    rw [map_mul]
    congr 1
    exact g.commutes (⟨_, hA a⟩ : L)⟩
  letI : TopologicalSpace (OO l) := ⊥
  haveI : DiscreteTopology (OO l) := ⟨rfl⟩
  haveI : ContinuousSMul (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (OO l) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := L) (x : PadicAlgCl l)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  haveI : Algebra.IsInvariant A (OO l) (PadicAlgCl l ≃ₐ[L] PadicAlgCl l) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := L) (b : PadicAlgCl l)).2
      fun g => congrArg Subtype.val (hb g)
    have hbL : (b : PadicAlgCl l) ∈ L := hk ▸ k.2
    exact ⟨⟨b, hbL⟩, rfl⟩
  set Q := maximalIdeal (OO l) with hQ
  let φ' : ((OO l) ⧸ Q) ≃ₐ[A ⧸ Q.under A] ((OO l) ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := (φ : ((OO l) ⧸ Q) ≃+* ((OO l) ⧸ Q))) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hφ (a : OO l) (hA a))
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := PadicAlgCl l ≃ₐ[L] PadicAlgCl l) (Q.under A) Q φ'
  refine ⟨σ, fun x y hxy => ?_⟩
  have h1 : Ideal.Quotient.mk Q (σ • x) = φ (residue (OO l) x) :=
    DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)
  have h2 : residue (OO l) (σ • x - y) = 0 := by
    rw [map_sub, hxy]
    exact sub_eq_zero.2 h1
  have h3 : ¬ IsUnit (σ • x - y) := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h2
    exact h2
  have h4 := (GlobalTheory.ZH.not_isUnit_OO_iff _).1 h3
  simpa [hsmul] using h4

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderJetAlgHom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer.Hol

def jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W) (v : E) :
    Hol W →ₐ[ℂ] DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h))
  map_one' := by
    ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by
    ext <;> simp
  map_add' f g := by
    ext <;> simp <;> ring
  commutes' c := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem jet_spec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W)
    (v : E) (h : Hol W) : (jet hp v h).fst = h.fn p ∧ (jet hp v h).snd = fderiv ℂ h.fn p v := by
  constructor
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).fst = _
    simp [ev_apply]
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).snd = _
    simp [ev_apply, fn_der v h hp]

end GlobalTheory.AnPer.Hol

theorem GlobalTheory.AnPer.Hol.exists_jet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  intro E _ _ W p hp v
  exact ⟨GlobalTheory.AnPer.Hol.jet hp v, GlobalTheory.AnPer.Hol.jet_spec hp v⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusMatrixQuasiLogarithmBasis
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

section Div

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} {d : ℕ}

theorem in_mono {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) : In N' f :=
  fun α => by
    obtain ⟨b, hb, e⟩ := hf α
    exact ⟨b, h hb, e⟩

theorem in_span_smul (p : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (Ideal.span {p}) (algebraMap B Q p • f) := fun α => by
  obtain ⟨b, -, e⟩ := hf α
  refine ⟨b * p, Ideal.mem_span_singleton'.2 ⟨b, rfl⟩, ?_⟩
  rw [coeff_smul, e, ← map_mul, mul_comm]

theorem div_coeff (p : B) {c : Q} (hc : c * algebraMap B Q p = 1) {q : Q}
    (h : ∃ b ∈ Ideal.span {p}, q = algebraMap B Q b) : ∃ b ∈ (⊤ : Ideal B), c * q = algebraMap B Q b := by
  obtain ⟨b, hb, e⟩ := h
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b', Submodule.mem_top, ?_⟩
  rw [e, map_mul, ← mul_assoc, mul_comm c, mul_assoc, hc, mul_one]

theorem ql_div (p : B) {c : Q} (hc : c * algebraMap B Q p = 1)
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ (Ideal.span {p}) f) : QL μ ⊤ (c • f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, hμ i]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
      mul_zero]
  · have := div_coeff p hc (h1 i)
    simpa [lin, coeff_smul] using this
  · rw [formalCoboundary_smul hμ']
    intro α
    have := div_coeff p hc (h2 α)
    simpa [coeff_smul] using this

theorem comb_mul {ι : Type} [Fintype ι] (p : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun l => b l * p) e = algebraMap B Q p • comb b e := by
  simp only [comb, Finset.smul_sum, map_mul, mul_comm, mul_smul]

end Div

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem exists_frob_matrix : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∃ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, ∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hm k e hB hA
  have key := fun f hf => _root_.GlobalTheory.QLog.ql_frob p C v O hv ε hε F G d c μ' hL hm f hf
  obtain ⟨u, hu⟩ := F.frame.unit_p
  set pinv : F.Q := ((u⁻¹ : F.Qˣ) : F.Q) with hpinv
  have hpB : (p : F.Q) = algebraMap F.B F.Q (p : F.B) := (map_natCast _ _).symm
  have hc : pinv * algebraMap F.B F.Q (p : F.B) = 1 := by
    rw [← hpB, ← hu, hpinv, Units.inv_mul]
  have hc' : algebraMap F.B F.Q (p : F.B) * pinv = 1 := by rw [mul_comm, hc]
  have h1 : ∀ i', ∃ b : Fin d ⊕ Fin k → F.B,
      In (⊤ : Ideal F.B) (pinv • frob p F.s (e (Sum.inl i')) - comb b e) := fun i' =>
    (hB.2 _ (ql_div (p : F.B) hc hL.const
      ((key _ (hB.1 _)).2 (hA i').1))).exists
  have h2 : ∀ j, ∃ b : Fin d ⊕ Fin k → F.B,
      In (⊤ : Ideal F.B) (frob p F.s (e (Sum.inr j)) - comb b e) := fun j =>
    (hB.2 _ (key _ (hB.1 _)).1).exists
  choose b1 hb1 using h1
  choose b2 hb2 using h2
  refine ⟨Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i, ?_⟩
  intro i
  rcases i with i' | j
  · have hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) *
        blk d k (p : F.B) 1) l (Sum.inl i')) = fun l => b1 i' l * p := by
      funext l
      simp [blk, Matrix.mul_diagonal]
    rw [hcol, comb_mul]
    have heq : frob p F.s (e (Sum.inl i')) - algebraMap F.B F.Q (p : F.B) • comb (b1 i') e =
        algebraMap F.B F.Q (p : F.B) • (pinv • frob p F.s (e (Sum.inl i')) - comb (b1 i') e) := by
      rw [smul_sub, smul_smul, hc', one_smul]
    rw [heq]
    have hp := in_span_smul (p : F.B) (hb1 i')
    exact ⟨in_mono le_top hp, fun _ _ => hp⟩
  · have hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) *
        blk d k (p : F.B) 1) l (Sum.inr j)) = fun l => b2 j l := by
      funext l
      simp [blk, Matrix.mul_diagonal]
    rw [hcol]
    exact ⟨hb2 j, fun _ h => absurd h (by simp)⟩

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSet
section
noncomputable section

namespace GlobalTheory.GoodSetOfChars

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem eS_eq_chiIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (s : T.S) :
    Formalism.MainNotions.PrimeDegreeVariant.eS T s = chiIdem fun g => LinearMap.trace K (T.W s) (T.tau s g) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.trace_one]

theorem exists_goodSet (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P0 : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) [Fintype P0.H]
    (h1 : ∀ χ ∈ X, ∑ h : P0.H, χ (h : G) * (((P0.chi h)⁻¹ : Kˣ) : K) = (Fintype.card P0.H : K)) :
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G,
      (∀ χ, χ ∈ X ↔ ∃ s, χ = fun g => LinearMap.trace K (T.W s) (T.tau s g)) ∧
        Formalism.MainNotions.PrimeDegreeVariant.M1 T P0 ∧ Formalism.MainNotions.PrimeDegreeVariant.eG T = idemOf X := by
  classical
  have key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧
      Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g :=
    fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)
  choose n τ hn hs ht using key
  have ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K) := fun s => funext (ht s)
  let T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G :=
    { S := X
      W := fun s => Fin (n s) → K
      ntW := fun s => by
        have : Nonempty (Fin (n s)) := ⟨⟨0, hn s⟩⟩
        infer_instance
      tau := τ
      irr := hs
      inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }
  refine ⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact (ht' s).symm ▸ s.2
  · have h2 := (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by
      simp_rw [ht s]
      rw [h1 _ s.2, Nat.card_eq_fintype_card])
    rw [← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h2
    exact h2
  · unfold Formalism.MainNotions.PrimeDegreeVariant.eG idemOf
    rw [← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eS_eq_chiIdem]
    exact congrArg chiIdem (ht' s)

end GlobalTheory.GoodSetOfChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicPrimitiveOfCechDeRhamPeriods
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_prim_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ x q,
    IsPer u.ex u.Λ x q → ∀ c, Hyp1.mk _ c = x → ∃ h, IsPrim u.ex c h ∧
      ∀ (U : A.left.affineOpens) (l : u.Λ), ∀ z ∈ pre u.ex U.1, h U (z + l) = h U z + q l := by
  intro A _ g L u x q hx c hc
  obtain ⟨hOpen, hDiff, -, hPer, -, -, -, -, hRes, hHom, -, -⟩ := GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨c₀, h₀, hc₀, ⟨p1, p2, p3⟩, hp⟩ := hx
  obtain ⟨b, hb⟩ := Hyp1.mk_eq_mk.1 (hc.trans hc₀.symm)
  have hval_add : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s + t) z = val u.ex U s z + val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_add]
  have hval_sub : ∀ (U : A.left.Opens) (s t : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (s - t) z = val u.ex U s z - val u.ex U t z := by
    intro U s t z hz
    obtain ⟨e, he⟩ := hHom U z hz
    erw [he, he, he, map_sub]
  have hcf : ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V),
      c.1.1 (Opposite.op U) (Opposite.op V) a = c₀.1.1 (Opposite.op U) (Opposite.op V) a +
        (b (Opposite.op V) - Sec.res (str A) (leOfHom a.unop) (b (Opposite.op U))) := by
    intro U V a
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.1 (Opposite.op U) (Opposite.op V) a) hb
    simp only [dTot0_f] at this
    exact (eq_add_of_sub_eq' this.symm :)
  have hcω : ∀ U : A.left.affineOpens, c.1.2 (Opposite.op U) =
      c₀.1.2 (Opposite.op U) + KaehlerDifferential.D ℂ _ (b (Opposite.op U)) := by
    intro U
    have := congrArg (fun y : Tot1 (OAff (str A)) ↦ y.2 (Opposite.op U)) hb
    simp only [dTot0_ω] at this
    change _ = (c.1 - c₀.1).2 _ at this
    rw [this]
    change c.1.2 _ = c₀.1.2 _ + (c.1.2 _ - c₀.1.2 _)
    abel
  refine ⟨fun U z ↦ h₀ U z + val u.ex U.1 (b (Opposite.op U)) z, ⟨fun U ↦ ?_, fun U V a z hz ↦ ?_, fun U z hz ↦ ?_⟩,
    fun U l z hz ↦ ?_⟩
  · exact (p1 U).add (hDiff U.1 _)
  · have hle : V.1 ≤ U.1 := leOfHom a.unop
    have hr : val u.ex V.1 (Sec.res (str A) hle (b (Opposite.op U))) z = val u.ex U.1 (b (Opposite.op U)) z :=
      hRes U.1 V.1 hle _ z hz
    simp only
    rw [p2 U V a z hz, hcf U V a, hval_add _ _ _ z hz, hval_sub _ _ _ z hz, hr]
    ring
  · have hd₀ : DifferentiableAt ℂ (h₀ U) z := ((p1 U) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    have hd₁ : DifferentiableAt ℂ (val u.ex U.1 (b (Opposite.op U))) z :=
      ((hDiff U.1 _) z hz).differentiableAt ((hOpen U.1).mem_nhds hz)
    obtain ⟨-, -, hD⟩ := _root_.GlobalTheory.CechPer.evForm_rules A g L u U.1 z hz
    change fderiv ℂ (h₀ U + val u.ex U.1 (b (Opposite.op U))) z = _
    rw [fderiv_add hd₀ hd₁, p3 U z hz, hcω U, map_add (f := _), hD]
  · simp only
    rw [hp U l z hz]
    erw [hPer]
    ring

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsHomId
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_isIso_morphismRestrict_of_isHom_id : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  intro o Ω _ _ _ Y M q hq
  have := M.sep
  have : IsSeparated (q ≫ M.s) := hq.inducedModelMorphism_comp_structureMap.symm ▸ Y.sep
  have : IsSeparated q := IsSeparated.of_comp q M.s
  obtain ⟨U, hU, hgU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint Y.Z) trivial
  obtain ⟨S, hS⟩ := fg_ringOn hU ⟨_, hgU⟩
  have hop : IsOpen (⋂ x ∈ S, {z | x ∈ M.O z}) :=
    isOpen_biInter_finset fun x _ => M.isOpen_setOf_mem_O x
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hop⟩) (x := genericPoint M.Z)
      (Set.mem_iInter₂.2 fun x _ => by
        show x ∈ M.O _
        rw [O_genericPoint]
        exact Algebra.mem_top)
  have hR : Y.ringOn U ≤ M.ringOn V := by
    rw [← hS]
    exact Algebra.adjoin_le fun x hx => mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 (hle hw) x hx
  refine ⟨V, ⟨_, hzV⟩, isIso_morphismRestrict_of_local_dominant_sections q V fun z hz => ?_⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint Y.Z, hgU⟩ (V := V) ⟨z, hz⟩ fun x hx => hR hx
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hz⟩)
  have hid : ∀ {X : Scheme.{0}} (a : Spec (CommRingCat.of Ω) ⟶ X),
      Spec.map (CommRingCat.ofHom (AlgHom.id o Ω).toRingHom) ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hz, hV.range_fromSpec ▸ fun w hw => hw,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hq

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHormanderIterationStep
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem hormander_step : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), 0 < t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F1 : ι → Y → ℂ, A.IsSSec (A.kap + la) F1 ∧ n0 A la (F0 - F1) ≤ ENNReal.ofReal (K / t) * n1 C la F0 ∧ n1 C la F1 ≤ ENNReal.ofReal (K / t) * n1 C la F0 := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨K', hK'0, hK'⟩ := _root_.GlobalTheory.OTY.GlueEnergy.energy_glue_le n Y ι La A C
  refine ⟨max (C.m : ℝ) K', le_max_of_le_right hK'0, ?_⟩
  intro la t ht hcurv F0 hF0
  have hball : ∀ a : Fin C.m, ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - F v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤
      ENNReal.ofReal t⁻¹ * ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hsub : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    refine _root_.GlobalTheory.HormanderBall.hormander_ball n (C.c a) (C.r a) t (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w))
      (F0 (C.idx a) ∘ (A.chart (C.idx a)).symm) ht ((A.smooth_ph la (C.idx a)).mono hsub)
      ((hF0.1 (C.idx a)).mono hsub) ?_
    intro v hv ξ
    have h := hcurv a v hv ξ
    unfold WeightedAtlas.leviAt at h
    rwa [(A.chart (C.idx a)).right_inv (hsub hv)] at h
  choose u hu hE using hball
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hE a)
  rw [← Finset.mul_sum] at hsum
  have hK : ENNReal.ofReal (max (C.m : ℝ) K' / t) =
      ENNReal.ofReal (max (C.m : ℝ) K') * ENNReal.ofReal t⁻¹ := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (le_max_of_le_right hK'0)]
  refine ⟨glue C la u, _root_.GlobalTheory.OTY.glue_isSSec_of_holo n Y ι La A C la u hu, ?_, ?_⟩
  · have hm : (C.m : ℝ≥0∞) ≤ ENNReal.ofReal (max (C.m : ℝ) K') := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
    calc n0 A la (F0 - glue C la u) ≤ _ := _root_.GlobalTheory.GlueDist.sq_norm_smoothSection_sub_glued_le n Y ι La A C la F0 u hF0 hu
      _ ≤ (C.m : ℝ≥0∞) * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr
      _ = _ := by rw [hK, mul_assoc]
  · calc n1 C la (glue C la u) ≤ _ := hK' la F0 u hF0 hu
      _ ≤ ENNReal.ofReal K' * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by gcongr; exact hsum
      _ ≤ ENNReal.ofReal (max (C.m : ℝ) K') * (ENNReal.ofReal t⁻¹ * n1 C la F0) := by
        gcongr; exact le_max_right _ _
      _ = _ := by rw [hK, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field : GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Hodge → ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧ Module.finrank k (Fil A) = g := by
  first | exact @GlobalTheory.finrank_HdR_Fil_of_field | exact GlobalTheory.finrank_HdR_Fil_of_field | (intros; apply GlobalTheory.finrank_HdR_Fil_of_field <;> assumption)
end

