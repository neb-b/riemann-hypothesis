module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0284
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SupTrace
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0003
public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair

variable {k K : Type} [Field k] [Field K]

def AdjKlt (c : k →+* K) (n : ℕ) (T : Subring K) (S : Place c) (η : Forms c n) (φ : K →₀ ℚ) :
    Prop :=
  η ≠ 0 ∧ φ 0 = 0 ∧
  ∀ (Q : Subring K) (hQ : IsLocModel c Q) (t u : Q) (E : Place c), T ≤ Q →
    Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
    S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : K) = 1 → E.ord (u : K) = 1 →
    (∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring → P.disc η φ = 0) →
    -1 < E.disc η φ

namespace AdjKlt

variable {c : k →+* K} {n : ℕ} {T T' : Subring K} {S : Place c} {η : Forms c n} {φ : K →₀ ℚ}

theorem form_ne_zero (h : AdjKlt c n T S η φ) : η ≠ 0 := h.1

theorem apply_zero (h : AdjKlt c n T S η φ) : φ 0 = 0 := h.2.1

theorem mono (h : AdjKlt c n T S η φ) (hT : T ≤ T') : AdjKlt c n T' S η φ :=
  ⟨h.1, h.2.1, fun Q hQ t u E hQ' => h.2.2 Q hQ t u E (hT.trans hQ')⟩

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 := by
  refine ⟨fun h h0 => h ?_, fun h hu => h (P.ord_eq_zero hu)⟩
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h0]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)

end AdjKlt

variable {c : k →+* K} {n : ℕ} {T : Subring K} {η : Forms c n} {φ : K →₀ ℚ}

theorem adjKlt_of_lt_disc (S : Place c) (hη : η ≠ 0) (hφ : φ 0 = 0)
    (h : ∀ E : Place c, E.Contains T → E.ring ≠ S.ring → -1 < E.disc η φ) :
    AdjKlt c n T S η φ :=
  ⟨hη, hφ, fun _ hQ _ _ E hT hm hd hS hE ht hu _ =>
    h E (hE.1.mono hT) fun e => AdjKlt.neighbour_ne hQ hm hd hS ht hu (Place.ext e)⟩

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

def locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) : IrrGL (k := w.adicCompletion E) → WD h :=
  (hT E Ω A w h).choose

theorem isRecT_locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) :
    UpperTheory.Zero.LLC.IsRecT h (locRecT hT h) :=
  (hT E Ω A w h).choose_spec

variable [_root_.NumberField.IsTotallyComplex E]

def locParT (hT : UpperTheory.Zero.LLC.RecTExists) (π : CG E a) (h : IsPlaceOver A w) : WD h :=
  locRecT hT h ⟨a, ParLaws.toCl (π.loc w)⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open Formalism.BasicNotions

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGT (hT : UpperTheory.Zero.LLC.RecTExists) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) :
    WD (pl.2 w) :=
  haveI := host_isCMField H; locParT hT π.1 (pl.2 w)

end GlobalTheory.CuspRep.ParLawsT

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

def NonUnit (R : Subring K) (f : K) : Prop := f ∈ R ∧ (f = 0 ∨ f⁻¹ ∉ R)

def RatRes (c : k →+* K) (R : Subring K) : Prop := ∀ r ∈ R, ∃ a, NonUnit R (r - c a)

def Dominates (ρ : K →+* L) (B : Subring L) (O : Subring K) : Prop :=
  ∀ f ∈ O, ρ f ∈ B ∧ (NonUnit O f → NonUnit B (ρ f))

structure IsEtTower (cK : k →+* K) (R : Subring K) (cL : k →+* L) (T : Subring L) {r : ℕ}
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) : Prop where

  base : IsLocModel cK R

  normal : IsIntegrallyClosed R

  top : IsLocModel cL T

  const : ∀ a, (ι ⟨cK a, base.const_mem a⟩ : L) = cL a

  retr : ∀ a, ψ (ι a) = a

  zero : ∀ i, ψ (τ i) = 0

  etale : (MvPolynomial.eval₂Hom ι τ).FormallyEtale


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.nonUnit_iff {R : Subring K} (f : R) :
    _root_.GlobalTheory.FieldPair.NonUnit R f ↔ ¬ IsUnit f := by
  constructor
  · rintro ⟨-, h0 | hinv⟩ hu
    · have hf : f = 0 := Subtype.ext (by simpa using h0)
      exact not_isUnit_zero (hf ▸ hu)
    · obtain ⟨u, rfl⟩ := hu
      have hmul : ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]
        rfl
      rw [inv_eq_of_mul_eq_one_right hmul] at hinv
      exact hinv (u⁻¹ : Rˣ).1.2
  · intro hnu
    refine ⟨f.2, ?_⟩
    by_contra h
    push_neg at h
    apply hnu
    exact IsUnit.of_mul_eq_one (b := (⟨_, h.2⟩ : R)) (Subtype.ext (by simp [h.1]))


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.nonUnit_zero (R : Subring K) : _root_.GlobalTheory.FieldPair.NonUnit R 0 :=
  ⟨R.zero_mem, Or.inl rfl⟩


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.not_nonUnit_one (R : Subring K) : ¬ _root_.GlobalTheory.FieldPair.NonUnit R 1 := by
  rintro ⟨-, h | h⟩
  · exact one_ne_zero h
  · exact h (by rw [inv_one]; exact R.one_mem)


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.Dominates.trans {M : Type} [Field M] {ρ : K →+* L} {σ : L →+* M}
    {O : Subring K} {B : Subring L} {C : Subring M} (h : _root_.GlobalTheory.FieldPair.Dominates ρ B O)
    (h' : _root_.GlobalTheory.FieldPair.Dominates σ C B) :
    _root_.GlobalTheory.FieldPair.Dominates (σ.comp ρ) C O := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  obtain ⟨h3, h4⟩ := h' (ρ f) h1
  exact ⟨h3, fun hn => h4 (h2 hn)⟩


set_option autoImplicit false in
variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.ratRes_self : _root_.GlobalTheory.FieldPair.RatRes (RingHom.id k) ⊤ := by
  intro r _
  exact ⟨r, by rw [RingHom.id_apply, sub_self]; exact _root_.GlobalTheory.FieldPair.nonUnit_zero ⊤⟩

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open GlobalTheory.HCChar (dsChar)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEG

open GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def OmDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, ev k Q * ev k (OmP ε).det = physDet ε k

def ClassFn : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε), physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
      trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k)

def GaInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ Λ m : Fin n → ℤ, gaW ε lam = (fun a => (Λ a : ℝ)) ∧ (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) ∧
      (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) ∧
      ∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)

def ToKType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) →
    ∃ T₀ : S7.KType ε γ, ∀ k : S7.KG ε, ReciprocityTheory.ChartRestriction.TR.Weyl.kChar T₀ k = trK T (S7.toMK k)

def VdmSplit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ),
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) = ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t * ((-1) ^ sDeg ε *
      ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2))

def PhysTor : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ),
    physDet ε (Matrix.diagonal (tor θ)) = (-1) ^ (pOf ε * qOf ε) * (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2)) *
      ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) ∧
    physDet ε (Matrix.diagonal (tor θ)) * conj (physDet ε (Matrix.diagonal (tor θ))) = (dMode ε θ : ℂ)

def NumShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ) (t : Fin n → ℂ), (∀ a, t a ≠ 0) →
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a))

def RangeFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∀ d : ℕ,
    ∃ L : Submodule ℂ (smD ε σ), FiniteDimensional ℂ L ∧
      (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD (isDerivedOn_smE hσ) hk x ∈ L) ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∀ u : H,
        ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ L.map (smD ε σ).subtype

def BuildY : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (c : ℂ), (∀ v : D, casimir E v = c • v) →
    ∀ L : Submodule ℂ D, FiniteDimensional ℂ L → (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    ∃ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y ∧ tensFock L ⊓ physicalSubspace ε ≤ Y ∧
      Y ≤ physicalSubspace ε ∧ (∀ y ∈ Y, dD ε E y ∈ Y) ∧ (∀ y ∈ Y, gradT y ∈ Y) ∧
      ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y

def StrKer : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Y : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Y], (∀ y ∈ Y, dD ε E y ∈ Y) → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y),
    ∃ (Z : Submodule ℂ (TensorProduct ℂ D (Fock n))) (_ : FiniteDimensional ℂ Z)
      (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z) (Γ : TSub Z →ₗ[ℂ] TSub Z),
      Z ≤ Y ∧ (∀ y ∈ Z, dD ε E y = 0) ∧ ∀ (k : Mat n) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
          LinearMap.trace ℂ (TSub Z) (Γ ∘ₗ (tOp hD hZK k : TSub Z →ₗ[ℂ] TSub Z))

def StrIdx : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ d : ℕ,
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (L : Submodule ℂ D) [FiniteDimensional ℂ L],
    (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    (∀ Q : Poly n, Q.totalDegree ≤ d → ∀ u : H,
      ∫ k : KG ε, ev (toMK k) Q • σ (toMK k) u ∂(muK ε) ∈ L.map D.subtype) →
    ∀ (Y : Submodule ℂ (TensorProduct ℂ D (Fock n))) [FiniteDimensional ℂ Y], tensFock L ⊓ physicalSubspace ε ≤ Y →
      Y ≤ physicalSubspace ε → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y) (B : H →L[ℂ] H),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) →
      ∃ hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L.map D.subtype,
        LinearMap.trace ℂ (L.map D.subtype) ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) =
          ∫ k : KG ε, ev (toMK k) P * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (k := toMK k) k.2).restrict
            (fun y hy => hG _ (hK _ k.2 y hy))) ∂(muK ε)

def HWVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Z : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Z] (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z)
      (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T → ∀ Φ : W →ₗ[ℂ] TSub Z, Φ ≠ 0 →
      (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = tOp hD hZK k (Φ v)) →
      ∃ z ∈ Z, z ≠ 0 ∧ IsKHWVec ε (diagE ε (eT E) cpT cmT) γ z

def CoordFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))), FiniteDimensional ℂ Z →
    IsKStableSub ε (diagE ε (eT E) cpT cmT) Z →
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z)

def CasCoord : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E → ∀ z : TensorProduct ℂ M (Fock n),
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z → dD ε E z = 0 →
    ∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z

def AlgDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Gap3 ε lam →
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
    IsGlRep E → IsInfUnitary ε E → ∀ z : TensorProduct ℂ M (Fock n), z ≠ 0 → z ∈ physicalSubspace ε →
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z →
    (∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z) →
    ∀ S : Submodule ℂ M, FiniteDimensional ℂ S → IsKStableSub ε E S → (∀ s, tco s z ∈ S) →
    ∃ V : Submodule ℂ M, IsKIrrHW ε E (lowK ε lam) V ∧ V ≠ ⊥ ∧ ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v

def CptCase : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), pOf ε = 0 ∨ qOf ε = 0 →
    (∀ k, physDet ε k = 1) ∧ sDeg ε = 0 ∧
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
      FiniteDimensional ℂ X ∧ IsKIrr ε (gaW ε lam) D

def TorusId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (Λ m : Fin n → ℤ), (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) →
    (∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)) →
    ∀ θ : Fin n → ℝ, Function.Injective (tor θ) → ∀ x : ℂ,
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x = ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) (tor θ) →
      (-1) ^ sDeg ε * x = dsChar ε lam θ * physDet ε (Matrix.diagonal (tor θ))

end GlobalTheory.PsCo.PcEG
end
end

