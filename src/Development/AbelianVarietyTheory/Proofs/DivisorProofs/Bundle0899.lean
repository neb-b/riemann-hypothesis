module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConj
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem nrmG_succ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ : H) :
    nrmG θ (r + 1) δ = nrmG θ r δ * (⇑θ)^[r] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem iter_hom_mul {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x y : H) :
    (⇑θ)^[r] (x * y) = (⇑θ)^[r] x * (⇑θ)^[r] y := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_mul, ih]

theorem iter_hom_inv {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x : H) :
    (⇑θ)^[r] x⁻¹ = ((⇑θ)^[r] x)⁻¹ := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_inv, ih]

theorem nrmG_twConj {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H) :
    nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧
      δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  induction r with
  | zero => simp [nrmG]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [nrmG_succ, nrmG_succ, h1, iter_hom_mul, iter_hom_mul,
        iter_hom_inv, Function.iterate_succ_apply]
      group
    · rw [nrmG_succ, map_mul, ← mul_assoc, h2, mul_assoc, ← Function.iterate_succ_apply' (⇑θ), mul_assoc]

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn IsDatum TwistedTransport)

namespace GlobalTheory.TwistedTransportProof

variable {E : Type} [Field E] [NumberField E]

theorem modF_rat (y : (Af E)ˣ) : ∃ q : ℚ, (q : ℝ) = modF y := by
  unfold modF
  refine finprod_induction (fun x : ℝ => ∃ q : ℚ, (q : ℝ) = x) ⟨1, by simp⟩ ?_ ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; ring⟩
  · intro v
    exact ⟨((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), by push_cast; rfl⟩

theorem isAlgebraic_modF_pow (y : (Af E)ˣ) (s : ℕ) : IsAlgebraic ℚ (((modF y ^ s : ℝ)) : ℂ) := by
  obtain ⟨q, hq⟩ := modF_rat y
  rw [← hq]
  have : ((((q : ℝ) ^ s : ℝ)) : ℂ) = algebraMap ℚ ℂ (q ^ s) := by simp
  rw [this]; exact isAlgebraic_algebraMap _

theorem lattice_princ_mul (c : Ideal (OF E)) (y : (Af E)ˣ) (a : Eˣ) :
    lattice c (Units.map (algebraMap E (Af E)).toMonoidHom a * y) = (fun x => (a : E) * x) '' lattice c y := by
  ext z
  constructor
  · intro hz
    refine ⟨(a : E)⁻¹ * z, ?_, by simp⟩
    rw [← mul_mem_lattice_princ c y a]
    simpa using hz
  · rintro ⟨x, hx, rfl⟩
    exact (mul_mem_lattice_princ c y a x).2 hx

theorem exists_isLatSum_of_mk_eq [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ)
    (κ : I → ℕ) {c : Ideal (OF E)} {y y' : (Af E)ˣ} (h : (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y')
    {S : ℂ → ℂ} (hS : IsLatSum φ (2 * s) κ (lattice c y) S) : ∃ S', IsLatSum φ (2 * s) κ (lattice c y') S' := by
  classical
  rw [QuotientGroup.eq] at h
  obtain ⟨p, ⟨a, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 h
  have e1 : y * (Units.map (algebraMap E (Af E)).toMonoidHom a * u) = y' := by rw [hpu, mul_inv_cancel_left]
  have e : y' = Units.map (algebraMap E (Af E)).toMonoidHom a * y * u := by rw [← e1]; ac_rfl
  rw [e, lattice_mul_unit _ hu, lattice_princ_mul]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s (lattice c y) κ a S hS).1⟩

theorem coordIn_eq {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold coordIn; ring

abbrev lv (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

theorem lv_mul (χ : HChar E) (s : ℕ) (y z : (Af E)ˣ) : lv χ s (y * z) = lv χ s y * lv χ s z := by
  simp only [lv, map_mul, Units.val_mul, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, mul_pow]
  push_cast; ring

theorem lv_ne_zero (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : lv χ s y ≠ 0 :=
  GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ y

theorem lv_mul_inv (χ : HChar E) (s : ℕ) (y z : (Af E)ˣ) : lv χ s (y * z⁻¹) = lv χ s y * (lv χ s z)⁻¹ := by
  have h := lv_mul χ s (y * z⁻¹) z
  rw [inv_mul_cancel_right] at h
  rw [h, mul_inv_cancel_right₀ (lv_ne_zero χ s z)]

theorem isAlgebraic_lv [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hU : UnramFin E) (h𝔣 : IsBaseCond 𝔣)
    (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (hV : IsValChar φ s κ 𝔣 ∅ χ) [Finite (PicO (condQ 𝔣 Q))] (y : (Af E)ˣ) :
    IsAlgebraic ℚ (lv χ s y) := by
  have hu0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU h𝔣 (fun q hq => by simp at hq) hV
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    unfold condQ
    rw [Finset.prod_empty, mul_one]
    exact Ideal.mul_le_left
  have hu : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ u = 1 := fun u hu => hu0 u (hatOUnits_mono hle hu)
  have h1 := GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hV.2.2.1 hu y
  exact h1.mul (isAlgebraic_modF_pow y s)

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem isAlgebraic_unit_val {G : Type} [Group G] [Finite G] (ψ : G →* ℂˣ) (q : G) : IsAlgebraic ℚ ((ψ q : ℂˣ) : ℂ) := by
  have h : ((ψ q : ℂˣ) : ℂ) ^ (Nat.card G) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact IsAlgebraic.of_pow Nat.card_pos (by rw [h]; exact isAlgebraic_one)

theorem alg_part {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K} {ι : K →+* ℂ} (h2 : Module.finrank ℚ K = 2)
    (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) {Λ₀ : PeriodPair} {Ω₀ : ℂ} (hΛ₀ : IsLatOf ι 1 Λ₀) (hΩ₀ : Ω₀ ^ 12 = latDisc Λ₀)
    (hA : LatAlg) (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (hD : IsDatum ι φ s κ 𝔣 Q χ) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ) (hT : IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T) :
    IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  classical
  obtain ⟨hU, hφ, hι, hs, -, h𝔣, hQ, hV⟩ := hD
  obtain ⟨hfin, S, hS, rfl⟩ := hT
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((ψ q : ℂˣ) : ℂ)⁻¹ * (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s q.out)⁻¹ * S q 0) =
      ((ψ q : ℂˣ) : ℂ)⁻¹ * (lv χ s q.out)⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [coordIn_eq d s κ Ω₀ (S q 0)]; simp only [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF, lv]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ₀ hΩ₀ E I φ s 𝔣 Q ⟨hU, hφ, hι, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h2 := isAlgebraic_lv hφ hU h𝔣 hQ hV q.out
  have h3 := isAlgebraic_unit_val ψ q
  refine mul_mem (mul_mem (inv_mem ?_) (inv_mem ?_)) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof
theorem key_alg (a b l1 l2 lu C N S : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (h1 : l1 ≠ 0) (h2 : l2 ≠ 0) (hu : lu ≠ 0) :
    a⁻¹ * l1⁻¹ * (C * (N⁻¹ * S)) = C * (N⁻¹ * (lu * b)⁻¹ * ((a * b⁻¹)⁻¹ * l2⁻¹ * (l2 * ((l1 * lu⁻¹)⁻¹ * S)))) := by
  field_simp
end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem conj_part {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K} {ι : K →+* ℂ} (h2 : Module.finrank ℚ K = 2)
    (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) {g : ℂ ≃+* ℂ} {t : (Af K)ˣ} {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ}
    (hΩ₀ : Ω₀ ^ 12 = latDisc Λ₀) (hTT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hC : LatConj)
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (hD : IsDatum ι φ s κ 𝔣 Q χ)
    (κ' : I → ℕ) (χ' : HChar E) (hw : IsConjWt φ g κ κ') (hcc : IsConjChar φ s κ' g χ χ')
    (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ) (hT : IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T)
    (hT' : IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T') :
    g (coordIn E d s κ Ω₀ T) =
      coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
        (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T') := by
  classical
  obtain ⟨hU, hφ, hι, hs, -, h𝔣, hQ, hV⟩ := hD
  obtain ⟨hfin, S, hS, rfl⟩ := hT
  obtain ⟨-, S', hS', rfl⟩ := hT'
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  obtain ⟨ct, hct⟩ : ∃ ct, classOf K (condQ 𝔣 Q) t = ct := ⟨_, rfl⟩
  rw [hct]
  have hct' : ct = QuotientGroup.mk (upIdele K E t) := by rw [← hct, GlobalTheory.ToricRatioBridge.upIdele_eq]; rfl
  set N : ℂ := ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) with hN
  have hu0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU h𝔣 (fun q hq => by simp at hq) hV
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    unfold condQ
    rw [Finset.prod_empty, mul_one]
    exact Ideal.mul_le_left
  have hχu : ∀ w ∈ hatOUnits (condQ 𝔣 Q), finPart χ w = 1 := fun w hw => hu0 w (hatOUnits_mono hle hw)
  have hχ'u : ∀ w ∈ hatOUnits (condQ 𝔣 Q), finPart χ' w = 1 := fun w hw => by
    have h1 := hcc.1 w
    have hm := GlobalTheory.CMVal.LUnit.modF_of_mem_hatOUnits hw
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF, hχu w hw, hm] at h1
    simpa using h1
  have hmk : ∀ q : PicO (condQ 𝔣 Q), (QuotientGroup.mk (q * ct⁻¹).out : PicO (condQ 𝔣 Q)) = QuotientGroup.mk (q.out * (upIdele K E t)⁻¹) := fun q => by
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hct']
  choose S'' hS'' using fun q : PicO (condQ 𝔣 Q) => exists_isLatSum_of_mk_eq hφ s κ' (hmk q) (hS' (q * ct⁻¹))
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, coordIn_eq d s κ Ω₀, coordIn_eq d s κ Ω₁]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum]
  refine Fintype.sum_equiv (Equiv.mulRight ct⁻¹) _ _ fun q => ?_
  simp only [Equiv.coe_mulRight]
  have hg1 : g (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s q.out) = lv χ' s q.out := (hcc.1 q.out).symm
  have hg2 := hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E I φ s 𝔣 Q ⟨hU, hφ, hι, hs, h𝔣, hQ⟩ κ κ' hw q.out (S q) (S'' q)
    (hS q) (hS'' q)
  have h' : (lv χ' s (q.out * (upIdele K E t)⁻¹))⁻¹ * S'' q 0 = (lv χ' s (q * ct⁻¹).out)⁻¹ * S' (q * ct⁻¹) 0 :=
    GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hcc.2 hχ'u (q.out * (upIdele K E t)⁻¹) (q * ct⁻¹).out (S'' q)
      (S' (q * ct⁻¹)) (hmk q).symm (hS'' q) (hS' (q * ct⁻¹))
  rw [lv_mul_inv, eq_inv_mul_iff_mul_eq₀ (lv_ne_zero _ _ _)] at h'
  have hsplit : ∀ a b : ℂ, coordIn E d s κ Ω₀ 1 * (a * b * S q 0) = a * b * coordIn E d s κ Ω₀ (S q 0) := fun a b => by
    rw [coordIn_eq d s κ Ω₀ (S q 0)]; ring
  have e1 : ((conjChar g ψ (q * ct⁻¹) : ℂˣ) : ℂ) = g (ψ q) * (g (ψ ct))⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.coe_conjChar, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  rw [hsplit, map_mul, map_mul, map_inv₀, map_inv₀, hg1, hg2, coordIn_eq d s κ Ω₁ (N⁻¹ * S'' q 0), ← h', e1,
    GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.coe_conjChar]
  have n1 := lv_ne_zero χ' s q.out
  have n2 := lv_ne_zero χ' s (q * ct⁻¹).out
  have n3 := lv_ne_zero χ' s (upIdele K E t)
  have n4 : g (ψ q) ≠ 0 := (map_ne_zero g).2 (Units.ne_zero _)
  have n5 : g (ψ ct) ≠ 0 := (map_ne_zero g).2 (Units.ne_zero _)
  exact key_alg _ _ _ _ _ _ _ _ n4 n5 n1 n2 n3

end GlobalTheory.TwistedTransportProof

namespace GlobalTheory.TwistedTransportProof

theorem twistedTransport_of_latClaims (hP : PeriodEx) (hA : LatAlg) (hC : LatConj) : TwistedTransport := by
  intro K _ _ d δ ι h2 hd hδ
  haveI : IsTotallyComplex K := GlobalTheory.Published.isTotallyComplex_of_sq_eq_neg hd hδ
  obtain ⟨Λ₀, hΛ₀⟩ := GlobalTheory.LatVal.Model.exists_isLatOf d δ ι h2 hd hδ
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ₀) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ₀]; norm_num)
  refine ⟨Ω₀, hΩ₀0, fun E _ _ _ _ I _ φ s κ 𝔣 Q χ hD ψ T hT =>
    alg_part h2 hd hδ hΛ₀ hΩ₀ hA E I φ s κ 𝔣 Q χ hD ψ T hT, ?_⟩
  intro Ω _ _ _ j art hj hart g σ t hσ hsym
  obtain ⟨Λ₁, Ω₁, hTT⟩ := hP K ι h2 Λ₀ Ω₀ hΛ₀ hΩ₀0 Ω j art hj hart g σ t hσ hsym
  exact ⟨Ω₁, hTT.2.1, fun E _ _ _ _ I _ φ s κ 𝔣 Q χ hD κ' χ' hw hcc ψ T T' hT hT' =>
    conj_part h2 hd hδ hΩ₀ hTT hC E I φ s κ 𝔣 Q χ hD κ' χ' hw hcc ψ T T' hT hT'⟩

end GlobalTheory.TwistedTransportProof


open GlobalTheory.TwistedTransportProof in
theorem GlobalTheory.TwistedTransportProof.main : PeriodEx → LatAlg → LatConj → GlobalTheory.ToricTransport.TwistedTransport :=
  twistedTransport_of_latClaims
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximation
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem GlobalTheory.ClassSum.sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (x0 : ∀ i, Frame (X i).Ψ r) (S : Finset (Fin m)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, ∀ j ∈ S, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) → (∀ i ∈ S, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧ ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧ ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧ IsOrth (X i) (x0 i)) → ∑ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i)) ≤ ENNReal.ofReal ((M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r M m G Λ Ψ X g x0 S g0 hr hM hU hΛ hg0 hg hT hUE hX
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨i0, hi0⟩
  · subst hS; simp
  obtain ⟨hG0, hΨ0, -, -, hO0⟩ := hX i0 hi0
  subst hG0
  subst hΨ0
  obtain ⟨L, hLset, hLhat, hL⟩ := _root_.GlobalTheory.UCls.selfDual_latOf_translate E r (X i0).Gm Λ g0 hΛ hg0
  obtain ⟨γ, s, hγs, hpair⟩ := _root_.GlobalTheory.UCls.exists_special_reduction E r M m (X i0).Gm Λ L g g0 S (fun i => (X i).Γ) (fun i => (X i).Λ)
    (by omega) hΛ hg0 hLset hLhat hg hT (fun i hi => ⟨(hX i hi).2.2.1, (hX i hi).2.2.2.1⟩)
  have hherm : ∀ a b, cc ((X i0).Gm a b) = (X i0).Gm b a := (X i0).Gm_herm
  have tr : ∀ (Ψ1 : Finset (E →+* ℂ)) (G1 : Matrix (Fin r) (Fin r) E) (x1 : Frame Ψ1 r) (p1 : ℕ)
      (H : Subgroup (GL (Fin r) E)), Ψ1 = (X i0).Ψ → G1 = (X i0).Gm →
      (∀ τ : Ψ1, gram τ.1 G1 (mat x1 τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) →
      covolume (inReal Ψ1 G1 H) (realSU Ψ1 G1) (riemHaar Ψ1 G1 x1) =
        covolume (inReal (X i0).Ψ (X i0).Gm H) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro Ψ1 G1 x1 p1 H h1 h2 h3
    subst h1 h2
    rw [_root_.GlobalTheory.FrameIndep.riemHaar_frame_indep E r p1 (X i0).p0 _ _ x1 (x0 i0) hherm h3 hO0]
  set Δ : Fin m → Subgroup (GL (Fin r) E) := fun i => ((X i).Γ).map (MulAut.conj (γ i)⁻¹).toMonoidHom with hΔ
  have hback : ∀ i, (Δ i).map (MulAut.conj (γ i)).toMonoidHom = (X i).Γ := by
    intro i
    rw [hΔ, Subgroup.map_map]
    have : (MulAut.conj (γ i)).toMonoidHom.comp (MulAut.conj (γ i)⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext δ : 1
      simp [mul_assoc]
    rw [this, Subgroup.map_id]
  have hterm : ∀ i ∈ S, covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
      (riemHaar (X i).Ψ (X i).Gm (x0 i)) =
      covolume (inReal (X i0).Ψ (X i0).Gm (Δ i)) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0)) := by
    intro i hi
    obtain ⟨hGi, hΨi, -, -, hOi⟩ := hX i hi
    rw [tr (X i).Ψ (X i).Gm (x0 i) (X i).p0 (X i).Γ hΨi hGi hOi, ← hback i]
    exact _root_.GlobalTheory.SUCovolConj.covolume_inReal_conj E r (X i0).p0 (X i0).Ψ (X i0).Gm (x0 i0) (γ i) (Δ i) hherm hO0 (hγs i hi).1
  obtain ⟨J, t, ht, hcount⟩ := _root_.GlobalTheory.SUCount.sum_covolume_le_pow_mul_tsum E r M (X i0).p0 (X i0).Gm L (X i0).Ψ (x0 i0) (Fin m) S s Δ hr
    (by omega) hL (X i0).cmType hO0 (fun i hi => (hγs i hi).2.1)
    (fun i hi j hj h => hUE i hi j hj (hpair i hi j hj h)) (fun i hi => (hγs i hi).2.2)
  have hV := _root_.GlobalTheory.SUVolBound.sum_covolume_le hP E r (X i0) L (x0 i0) J t hr hU hL hO0 ht
  rw [Finset.sum_congr rfl hterm]
  refine hcount.trans ?_
  calc (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ∑' j, covolume (inReal (X i0).Ψ (X i0).Gm (ratStab (X i0).Gm (L : Set (Fin r → E)) (t j))) (realSU (X i0).Ψ (X i0).Gm) (riemHaar (X i0).Ψ (X i0).Gm (x0 i0))
      ≤ (M : ℝ≥0∞) ^ (2 * fdeg E * r ^ 2) * ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
        gcongr
    _ = _ := by
        rw [mul_assoc ((M : ℝ) ^ (2 * fdeg E * r ^ 2)), ENNReal.ofReal_mul (p := (M : ℝ) ^ (2 * fdeg E * r ^ 2)) (by positivity),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

open GlobalTheory.AbLaw

variable {Rg : Type} [CommRing Rg]

def ringOf {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom

def cstT {T : Scheme.{0}} (t : T ⟶ Sp Rg) : Rg →+* Γ(T, ⊤) :=
  t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom

theorem ringOf_X {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (k : Fin n) :
    ringOf g (MvPolynomial.X k) = coord g k := rfl

def expand (mA mB : ℕ) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg) :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp MvPolynomial.C)
    (fun j => ∑ i, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i) F

variable {A₀ : Scheme.{0}} {N : LB A₀} {mA : ℕ}

def monSec (a : Fin mA → LB.Sec N) (d : ℕ) (ν : Fin mA →₀ ℕ) : LB.Sec (GlobalTheory.AbLaw.pw N (d : ℤ)) where
  f := fun q => if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0
  compat := fun (q q' : N.ι) => by
    change (A₀.presheaf.map (homOfLE (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q)).op).hom
        (if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0) =
      ((N.g q q' ^ (d : ℤ) : Γ(A₀, N.U q ⊓ N.U q')ˣ) : Γ(A₀, N.U q ⊓ N.U q')) *
        (A₀.presheaf.map (homOfLE (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q')).op).hom
          (if ∑ i, ν i = d then ∏ i, ((a i).f q') ^ ν i else 0)
    split_ifs with h
    · simp only [map_prod, map_pow]
      simp only [(a _).compat, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    · simp only [map_zero, mul_zero]

omit [CommRing Rg] in
theorem idPb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) :
    IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

variable {X : Scheme.{0}} {M : LB X}

def vecOf {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : Fin Q.a → Rg :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).1

theorem vecOf_ker {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : (Q.D₀.map (RingHom.id Rg)).mulVec (vecOf Q s) = 0 :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).2

theorem vecOf_spec {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) (i : Q.I) :
    rs X (le_pull M (𝟙 X) (Q.le i)) ((finSecPullId s).f (fun _ => Q.ch i)) =
      ∑ k, cst f ((𝟙 X) ⁻¹ᵁ Q.W i) (vecOf Q s k) * (Scheme.Hom.app (𝟙 X) (Q.W i)).hom (Q.u k i) := by
  have h := (Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose_spec
    ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)) i
  rw [Equiv.apply_symm_apply] at h
  exact h

variable {mB : ℕ} {f : A₀ ⟶ Sp Rg}

def polys (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (d : ℕ) (F : MvPolynomial (Fin mB) Rg)
    (k : Fin (Q d).a) : MvPolynomial (Fin (mA * mB)) Rg :=
  ∑ ν ∈ (expand mA mB F).support, (expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k)

def formIdeal (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) {B₀ : Scheme.{0}} {H : LB B₀}
    (fB : B₀ ⟶ Sp Rg) (b : Fin mB → LB.Sec H) : Ideal (MvPolynomial (Fin (mA * mB)) Rg) :=
  Ideal.span {P | ∃ (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (k : Fin (Q d).a),
    F.IsHomogeneous d ∧ Kills fB b F ∧ P = polys Q a d F k}

end GlobalTheory.FormsLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VoganNormSqLtOfRemoveNoncompactRoot
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolomorphicRootNormBound

theorem vNormSq_lt_of_root :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam → IsHolChamber ε lam → ∀ a b : Fin n, ε a = true → ε b = false → vNormSq ε (lowK ε lam - root a b) < vNormSq ε (lowK ε lam) := by
  intro n ε lam hanti hch a b ha hb
  have hA1 : CompanionTheory.D.DSIC.A1 ε = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [CompanionTheory.D.DSIC.A1, Finset.mem_filter] at hi
    exact absurd (hch.lt hanti i.2.1 i.2.2) (not_lt.2 hi.2.le)
  let i : CompanionTheory.D.DSIC.NC ε := ⟨(a, b), ha, hb⟩
  have hne : ({i} : Finset (CompanionTheory.D.DSIC.NC ε)) ≠ CompanionTheory.D.DSIC.A1 ε := by
    rw [hA1]; exact Finset.singleton_ne_empty i
  have h := CompanionTheory.D.DSIC.hNormLt n ε lam hanti {i} hne
  have hgam : CompanionTheory.D.DSIC.gam ε lam = lowK ε lam := by
    funext c
    simp [CompanionTheory.D.DSIC.gam, hA1, CompanionTheory.D.DSIC.wtA]
    rfl
  have hw : CompanionTheory.D.DSIC.wtA ({i} : Finset (CompanionTheory.D.DSIC.NC ε)) = root a b := by
    funext c
    simp only [CompanionTheory.D.DSIC.wtA, Finset.filter_singleton, root, Pi.sub_apply, Pi.single_apply, i]
    by_cases h1 : a = c <;> by_cases h2 : b = c <;> simp [h1, h2, eq_comm]
  rw [hgam, hw] at h
  exact h

end GlobalTheory.HolomorphicRootNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolConjEqOneOfMassCNeZero
section
open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

theorem vol_conj_eq_one_of_massC_ne_zero {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G) (ht : t ∈ T)
    (hC : C ≤ T) (h1 : C.relIndex (C.map (MulAut.conj t).toMonoidHom) ≠ 0)
    (h2 : (C.map (MulAut.conj t).toMonoidHom).relIndex C ≠ 0)
    (hf : ∀ s ∈ T, ((Γ' ⊓ C.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G).Finite)
    (hf' : ∀ s ∈ T, ((Γ' ⊓ (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom :
      Subgroup G) : Set G).Finite)
    (hm : massC Γ' T C ≠ 0) :
    vol C (C.map (MulAut.conj t).toMonoidHom) = 1 := by
  have hC' : C.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro x ⟨c, hc, rfl⟩
    have hcT := hC hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)
  have hchange := _root_.GlobalTheory.LKCount.MassChange.massC_mul_vol Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'
  rw [_root_.GlobalTheory.LKCount.massC_map_conj Γ' T C t ht hC] at hchange
  have := mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)
  exact this

end GlobalTheory.LKCount
end

