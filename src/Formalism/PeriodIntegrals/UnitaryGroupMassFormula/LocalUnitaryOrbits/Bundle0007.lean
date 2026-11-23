module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRAlgebraMap

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.RelIndexSmulSub
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

section Idx

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {W : Type} [AddCommGroup W] [Module (Fv F v) W]

theorem sdc_unifEx_holds : UnifEx v := ⟨unifV v, by rw [IsUnif, unifV_val]; rfl⟩

theorem smulSub_smulSub (s t : Fv F v) (P : AddSubgroup W) :
    smulSub s (smulSub t P) = smulSub (s * t) P := by
  ext z
  simp only [mem_smulSub]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, by rw [smul_smul]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨t • p, ⟨p, hp, rfl⟩, by rw [smul_smul]⟩

theorem smulSub_one (P : AddSubgroup W) : smulSub (1 : Fv F v) P = P := by
  ext z
  simp [mem_smulSub]

theorem relIndex_smulSub {t : Fv F v} (ht : t ≠ 0) (H G : AddSubgroup W) :
    (smulSub t H).relIndex (smulSub t G) = H.relIndex G :=
  AddSubgroup.relIndex_map_map_of_injective H G (smul_right_injective W ht)

theorem smulSub_le {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub s P ≤ P := by
  intro z hz
  rw [mem_smulSub] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact hP s hs p hp

theorem smulSub_unit {u : Fv F v} (hu : u ∈ v.adicCompletionIntegers F)
    (hu' : u⁻¹ ∈ v.adicCompletionIntegers F) (hu0 : u ≠ 0) (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) : smulSub u P = P := by
  apply le_antisymm (smulSub_le v hu P hP)
  intro z hz
  rw [mem_smulSub]
  exact ⟨u⁻¹ • z, hP _ hu' z hz, by rw [smul_smul, mul_inv_cancel₀ hu0, one_smul]⟩

theorem relIndex_pow {ϖ : Fv F v} (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ v.adicCompletionIntegers F)
    (P : AddSubgroup W) (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (k : ℕ) :
    (smulSub (ϖ ^ k) P).relIndex P = ((smulSub ϖ P).relIndex P) ^ k := by
  induction k with
  | zero => simp [smulSub_one]
  | succ k ih =>
    have e : smulSub (ϖ ^ (k + 1)) P = smulSub (ϖ ^ k) (smulSub ϖ P) := by
      rw [smulSub_smulSub, pow_succ]
    have h2 : smulSub (ϖ ^ k) P ≤ P := smulSub_le v (pow_mem hϖ k) P hP
    have h1 : smulSub (ϖ ^ k) (smulSub ϖ P) ≤ smulSub (ϖ ^ k) P := by
      intro z hz
      rw [mem_smulSub] at hz ⊢
      obtain ⟨p, hp, rfl⟩ := hz
      exact ⟨p, smulSub_le v hϖ P hP hp, rfl⟩
    rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2, relIndex_smulSub v (pow_ne_zero k hϖ0), ih]
    ring

theorem exists_unit_pow {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {d : Fv F v} (hd0 : d ≠ 0)
    (hd : d ∈ v.adicCompletionIntegers F) :
    ∃ k : ℕ, ∃ u : Fv F v, u ∈ v.adicCompletionIntegers F ∧ u⁻¹ ∈ v.adicCompletionIntegers F ∧
      u ≠ 0 ∧ d = ϖ ^ k * u ∧ absV v d = qv v ^ (-(k : ℤ)) := by
  have hϖ0 := unif_ne_zero v hϖ
  have hv : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero hv) with hmdef
  have hvm : Valued.v d = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simp [m]
  have hm : m ≤ 0 := by
    have h1 : Valued.v d ≤ 1 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd
      exact hd
    rw [hvm] at h1
    have h2 : (Multiplicative.ofAdd m : Multiplicative ℤ) ≤ 1 := by exact_mod_cast h1
    rw [← ofAdd_zero] at h2
    exact Multiplicative.ofAdd_le.1 h2
  have hk : ((m.natAbs : ℕ) : ℤ) = -m := Int.ofNat_natAbs_of_nonpos hm
  have hvk : Valued.v (ϖ ^ m.natAbs) = Valued.v d := by
    rw [map_pow, hϖ, hvm, ← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 2
    rw [nsmul_eq_mul, hk]
    ring
  have hϖk : ϖ ^ m.natAbs ≠ 0 := pow_ne_zero _ hϖ0
  have hu1 : Valued.v ((ϖ ^ m.natAbs)⁻¹ * d) = 1 := by
    rw [map_mul, map_inv₀, hvk, inv_mul_cancel₀ hv]
  refine ⟨m.natAbs, (ϖ ^ m.natAbs)⁻¹ * d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu1, inv_one]
  · exact mul_ne_zero (inv_ne_zero hϖk) hd0
  · rw [← mul_assoc, mul_inv_cancel₀ hϖk, one_mul]
  · unfold absV
    rw [dite_eq_right hv]
    unfold qv
    congr 1
    rw [hk]
    simp [m]

end Idx

section Steps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Set (Fin n → E))

def IdxPiW (a : ℕ) : Prop :=
  (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
      ((smulSub ϖ (LW v Λ a)).relIndex (LW v Λ a) : ℝ) = qv v ^ (2 * n * a)

def IdxPiH (a : ℕ) : Prop :=
  UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ((smulSub ϖ (HO σ v a)).relIndex (HO σ v a) : ℝ) = qv v ^ (a ^ 2)

theorem relIndex_dV {W : Type} [AddCommGroup W] [Module (Fv F v) W] (P : AddSubgroup W)
    (hP : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ P, s • x ∈ P) (N : ℕ) (e : ℝ)
    (hN : ∀ ϖ : Fv F v, IsUnif v ϖ → ((smulSub ϖ P).relIndex P : ℝ) = qv v ^ N)
    (he : e = -(N : ℝ)) :
    (P.relIndex (smulSub (dV v)⁻¹ P) : ℝ) = absV v (dV v) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := sdc_unifEx_holds v
  have hd0 := dV_ne_zero v
  obtain ⟨k, u, hu, hu', hu0, hd, habs⟩ := exists_unit_pow v hϖ hd0 (dV_int v)
  have e1 : P.relIndex (smulSub (dV v)⁻¹ P) = (smulSub ϖ P).relIndex P ^ k := by
    rw [← relIndex_smulSub v hd0, smulSub_smulSub, mul_inv_cancel₀ hd0, smulSub_one, hd,
      ← smulSub_smulSub, smulSub_unit v hu hu' hu0 P hP,
      relIndex_pow v (unif_ne_zero v hϖ) (unif_int v hϖ) P hP]
  rw [e1, Nat.cast_pow, hN ϖ hϖ, habs, he]
  have hq := qv_pos v
  rw [← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← pow_mul, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem idxW_of (a : ℕ) (h : IdxPiW v Λ a) : IdxW v Λ a := by
  intro hL hU
  exact relIndex_dV v (LW v Λ a) (fun s hs x hx => smul_mem_LW v Λ hs hx) (2 * n * a) _
    (fun ϖ hϖ => h hL hU ϖ hϖ) (by push_cast; ring)

theorem idxHO_of (a : ℕ) (h : IdxPiH σ v a) : IdxHO σ v a := by
  intro hU ϖ hϖ
  refine ⟨relIndex_dV v (HO σ v a) (fun s hs x hx => smul_mem_HO σ v hs hx) (a ^ 2) _
    (fun ϖ hϖ => h hU ϖ hϖ) (by push_cast; ring), h hU ϖ hϖ⟩

end Steps

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitOfPair
section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def FixLoc : Prop :=
  IsCMExt F E σ → ∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x = x → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ y = y →
    IsU v (x + y) → IsU v x ∨ IsU v y

def TrNd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ π : Fv F v, IsUnif v π → ∀ c ∈ OEv (E := E) v,
    sc (E := E) v (π⁻¹) * c ∉ OEv (E := E) v → ∃ t ∈ OEv (E := E) v, IsU v (t * c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (t * c))

def PrimPerp : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ π : Fv F v, IsUnif v π ∧ ∃ p ∈ PerpG σ J v Λ X, sc (E := E) v (π⁻¹) • p ∉ latLoc (E := E) v Λ

theorem isU_neg {z : Fv F v ⊗[F] E} (h : IsU v (-z)) : IsU v z := by
  obtain ⟨w, hw0, hw⟩ := h
  exact ⟨-w, oev_neg v hw0, by rw [mul_neg, ← neg_mul]; exact hw⟩

theorem isU_of_mul {a z : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (h : IsU v (a * z)) : IsU v z := by
  obtain ⟨w, hw0, hw⟩ := h
  exact ⟨a * w, (oSub v).2 _ ha _ hw0, by rw [← hw]; ring⟩

theorem unit_of_pair (hF : FixLoc σ v) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E)
    (p q : Fin n → Fv F v ⊗[F] E) (hp : p ∈ PerpG σ J v Λ X) (hq : q ∈ PerpG σ J v Λ X)
    (t : Fv F v ⊗[F] E) (ht : t ∈ OEv (E := E) v)
    (hu : IsU v (t * hR (Fv F v) σ J q p + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (t * hR (Fv F v) σ J q p))) :
    ∃ r ∈ PerpG σ J v Λ X, IsU v (hR (Fv F v) σ J r r) := by
  have hcm := hstd.1
  have hJ := hstd.2.1.1
  set s := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ t with hs
  have hs0 : s ∈ OEv (E := E) v := sigR_mem σ v ht
  have hss : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ s = t := sigR_invol σ v hcm t
  set r := p + s • q with hr
  have hrP : r ∈ PerpG σ J v Λ X := by
    refine ⟨Submodule.add_mem _ hp.1 (oSmul v Λ hL s hs0 q hq.1), fun i => ?_⟩
    rw [hr, hR_add_right', hR_smul_right, hp.2 i, hq.2 i, mul_zero, add_zero]
  set α := hR (Fv F v) σ J p p
  set β := hR (Fv F v) σ J q q
  set c := hR (Fv F v) σ J q p
  have hpq : hR (Fv F v) σ J p q = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c := (hR_conj σ J v hcm hJ q p).symm
  have hrr : hR (Fv F v) σ J r r = (t * c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (t * c)) + (α + t * s * β) := by
    rw [hr, hR_add_left', hR_add_right', hR_add_right', hR_smul_left, hR_smul_left, hR_smul_right,
      hR_smul_right, hpq, hss, map_mul]
    rw [hs]; ring
  have hα0 : α ∈ OEv (E := E) v := (hsd p).1 hp.1 p hp.1
  have hβ0 : β ∈ OEv (E := E) v := (hsd q).1 hq.1 q hq.1
  have hr0 : hR (Fv F v) σ J r r ∈ OEv (E := E) v := (hsd r).1 hrP.1 r hrP.1
  have hαf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ α = α := hR_conj σ J v hcm hJ p p
  have hβf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ β = β := hR_conj σ J v hcm hJ q q
  have hrf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (hR (Fv F v) σ J r r) = hR (Fv F v) σ J r r := hR_conj σ J v hcm hJ r r
  have hts0 : t * s ∈ OEv (E := E) v := (oSub v).2 _ ht _ hs0
  have htsβ0 : t * s * β ∈ OEv (E := E) v := (oSub v).2 _ hts0 _ hβ0
  have htsβf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (t * s * β) = t * s * β := by
    rw [map_mul, map_mul, hss, hβf, hs]; ring
  have hm0 : -(α + t * s * β) ∈ OEv (E := E) v := oev_neg v (oev_add v hα0 htsβ0)
  have hmf : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (-(α + t * s * β)) = -(α + t * s * β) := by
    rw [map_neg, map_add (f := _), hαf, htsβf]
  have hsum : hR (Fv F v) σ J r r + -(α + t * s * β) = t * c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (t * c) := by
    rw [hrr]; ring
  rcases hF hcm _ hr0 _ hm0 hrf hmf (by rw [hsum]; exact hu) with h | h
  · exact ⟨r, hrP, h⟩
  · have h' : IsU v (-α + -(t * s * β)) := by rw [← neg_add]; exact h
    rcases hF hcm _ (oev_neg v hα0) _ (oev_neg v htsβ0) (by rw [map_neg, hαf]) (by rw [map_neg, htsβf]) h'
      with h2 | h2
    · exact ⟨p, hp, isU_neg v h2⟩
    · exact ⟨q, hq, isU_of_mul v hts0 (isU_neg v h2)⟩

theorem partner (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hX : ∀ i, X i ∈ latLoc (E := E) v Λ) (hU : UniG σ J v X) (π : Fv F v)
    (p : Fin n → Fv F v ⊗[F] E) (hp : p ∈ PerpG σ J v Λ X) (hpn : sc (E := E) v (π⁻¹) • p ∉ latLoc (E := E) v Λ) :
    ∃ q ∈ PerpG σ J v Λ X, sc (E := E) v (π⁻¹) * hR (Fv F v) σ J q p ∉ OEv (E := E) v := by
  have h1 : ¬ ∀ x ∈ latLoc (E := E) v Λ, hR (Fv F v) σ J x (sc (E := E) v (π⁻¹) • p) ∈ OEv (E := E) v :=
    fun h => hpn ((hsd _).2 h)
  push_neg at h1
  obtain ⟨x, hx, hxn⟩ := h1
  obtain ⟨c, -, hc⟩ := splitG σ J v Λ hL hsd X hX hU x hx
  refine ⟨_, hc, ?_⟩
  rw [← hR_smul_right, hR_sub_left', hR_sum_left']
  have : ∀ i, hR (Fv F v) σ J (c i • X i) (sc (E := E) v (π⁻¹) • p) = 0 := by
    intro i
    rw [hR_smul_left, hR_smul_right, hp.2 i, mul_zero, mul_zero]
  simp only [this, Finset.sum_const_zero, sub_zero]
  exact hxn

theorem unitNorm_of (hF : FixLoc σ v) (hT : TrNd σ J ψ v) (hP : PrimPerp σ J ψ v Λ) : UnitNorm σ J ψ v Λ := by
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨π, hπ, p, hp, hpn⟩ := hP hstd hL hsd hun ι X hX hUX hc
  obtain ⟨q, hq, hqp⟩ := partner σ J v Λ hL hsd X hX hUX π p hp hpn
  obtain ⟨t, ht0, htu⟩ := hT hstd hun π hπ _ ((hsd p).1 hp.1 q hq.1) hqp
  obtain ⟨r, hr, u', hu'0, hu'⟩ := unit_of_pair σ J ψ v Λ hF hstd hL hsd X p q hp hq t ht0 htu
  exact ⟨r, hr, u', hu'0, hu'⟩

end PI.OmLocU.UnN
end
end

