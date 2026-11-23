module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealPointMovesAdelicThetaByDetCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RealMove

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem root_eq {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D T} {x x' : (AE D)ˣ}
    (hx : IsDetRoot T g x) (hx' : IsDetRoot T g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D T).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem om_compact (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {s : Fam T} (hs : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {k : GA D T} (hk : k ∈ GinfC T)
    (hc : ∀ τ, s τ * compAt C.θ τ (Formalism.L2.Theta.mt T k) = compAt C.θ τ (Formalism.L2.Theta.mt T k) * s τ)
    {y : (AE D)ˣ} (hy : IsDetRoot T k y) {f : WO S T → ℂ} (hf : IsThetaFunO C.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO C.ψ S T) C.θ τ (cplxO 1 (s τ)) f) :
    om (1, k) f = (((χS y : Circle) : ℂ) * vacChar C.θ T s S.rank (fun _ => 0) k) • f := by
  have hdet : ∀ τ, (gramAt D T τ).det ≠ 0 := fun τ => by
    have := (hs τ).2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨y₀, hy₀, hv₀⟩ := GlobalTheory.OneMapRef.RealMove.exists_root C.inf T hdet k hk
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by
    have e : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [e]
    exact ⟨one_mul _, by simp, by rw [one_mul]; exact Matrix.PosDef.one⟩
  have h1 : IsDetRoot S 1 1 := by simp [IsDetRoot]
  rw [_root_.GlobalTheory.WeilVacChar.vacuum_character D C.ψ hW.std S T C.θ C.inf χS χT om η hη hW (fun _ => 1) s hS hs 1 (one_mem _) k hk
    (fun τ => by rw [one_mul, mul_one]) hc 1 y₀ h1 hy₀ f hf hv, root_eq hW.resS C.even hy₀ hy]
  congr 1
  obtain ⟨m, hm⟩ := C.even
  have e1 := hv₀ (η * (η ^ (S.rank + 1))⁻¹) (fun _ => -(m : ℤ)) fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hη.2.2.2 τ) (hη.2.2.2 τ) (S.rank + 1)
    convert this using 1
    rw [hm]
    push_cast
    ring
  have e2 : ((χT * (η ^ T.rank)⁻¹) 1)⁻¹ * (χS * (η ^ S.rank)⁻¹) y₀ = χS y₀ * (η * (η ^ (S.rank + 1))⁻¹) y₀ := by
    simp only [map_one, inv_one, one_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_succ,
      mul_inv]
    rw [mul_left_comm (η y₀), mul_inv_cancel, mul_one]
  rw [e2, Circle.coe_mul, e1, mul_assoc, ← Finset.prod_mul_distrib, vacChar]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, -, hd⟩ := GlobalTheory.OneMapRef.RealMove.detPlus_one (n := S.rank) (s τ) (hs τ).1
  obtain ⟨d1, d2⟩ := hd (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)) (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (hc τ)
  have e3 : (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)).det = 1 := by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, inv_one]
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have e4 : (compAt C.θ τ (Formalism.L2.Theta.mt T k)).det ≠ 0 := by
    intro h0
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k)
    rw [det_mul, h0, mul_zero] at h2
    exact hdet τ h2.symm
  have hc' := hc τ
  rw [d1, e3]
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T k) = b at *
  have p1 : detPos (s τ) b = ((1 / 2 : ℂ) • (1 + s τ) * b + (1 / 2 : ℂ) • (1 - s τ)).det := by
    rw [detPos, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, hc', one_mul, mul_one]
  have p2 : detNeg (s τ) b = ((1 / 2 : ℂ) • (1 - s τ) * b + (1 / 2 : ℂ) • (1 + s τ)).det := by
    rw [detNeg, detPos, Matrix.mul_smul, Matrix.smul_mul, ← sub_eq_add_neg, sub_neg_eq_add, mul_sub, sub_mul, hc',
      one_mul, mul_one]
  rw [← p1, ← p2] at d2
  rw [← p1, d2]
  rw [d2] at e4
  have h0 := left_ne_zero_of_mul e4
  have e5 : S.rank / 2 = m := by omega
  rw [e5, zero_add, zero_sub, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, hm,
    one_pow, mul_one, mul_pow, pow_add, mul_inv]
  have := pow_ne_zero m h0
  field_simp

theorem th_ne_zero (C : GlobalTheory.Ker.Ctx S T) {x : Frame C.X.Ψ T.rank}
    (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem th_zero (C : GlobalTheory.Ker.Ctx S T) {x : Frame C.X.Ψ T.rank}
    (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem om_real (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {a : GA D T} (ha : a ∈ GinfC T) {y : (AE D)ˣ} (hy : IsDetRoot T a y) {B : C.Bas} (hB : C.IsB B)
    {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ) :
    om (1, a) (C.Th (C.xB B) φ) = ((χS y : Circle) : ℂ) • C.Th (C.xB (C.mvB a B)) φ := by
  obtain ⟨χ, -, χmul, hχ⟩ := GlobalTheory.FrameEquiv.exists_real_character D S T C om (GlobalTheory.Ker.isWeak_of_datum hW)
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  by_cases h0 : φ = 0
  · rw [hχ a ha B hB φ hφ, h0, th_zero C
      (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 a).1), smul_zero, smul_zero]
  obtain ⟨hex, -, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D T
  choose rt hrt using hex
  have hne : ∀ g, ((χS (rt g) : Circle) : ℂ) ≠ 0 := fun g => Circle.coe_ne_zero _
  have key := GlobalTheory.FrameEquiv.mulFun_eq_one_of_eq_one_on_maxCompact D T C.θ C.inf (C.sB B)
    (fun τ => ((hJ B hB).2.2.1 τ).1) (fun u => χ u / (χS (rt u) : Circle))
    (fun u hu u' hu' => by
      simp only [χmul u hu u' hu']
      rw [root_eq hW.resS C.even (hmul _ _ _ _ (hrt u) (hrt u')) (hrt (u * u')), map_mul, Circle.coe_mul,
        mul_div_mul_comm])
    (fun k hk hc => by
      have e1 := om_compact C hW hη (fun τ => ((hJ B hB).2.2.1 τ).1) hk (fun τ => (hc τ).symm) (hrt k)
        (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).1.1 ((GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1
      have e2 := hχ k hk B hB φ hφ
      have e3 := GlobalTheory.FrameEquiv.CompactMove.Th_mvB D S T C B hB k hk hc φ hφ
      rw [← smul_smul, ← e3, e2] at e1
      have e4 := smul_left_injective ℂ (th_ne_zero C
        (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 k).1) hφ h0) e1
      show χ k / (χS (rt k) : Circle) = 1
      rw [e4, div_self (hne k)]) a ha
  rw [hχ a ha B hB φ hφ, (div_eq_one_iff_eq (hne a)).1 key, root_eq hW.resS C.even hy (hrt a)]


set_option maxHeartbeats 1000000 in
theorem zak_om_real : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (_hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS χS χT om hW ⟨η, hη⟩ Z hZ a ha y hy φ hφ f hf
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, -, H⟩ := _root_.GlobalTheory.OneMapRef.Flip.exists_flip_model D S T r g hr ψ θ X eT bas idx hS (r - X.p0)
    (Nat.add_sub_cancel' X.p0_le)
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  have hB := (H Z).1.1 hZ
  have em : (fun ρ => (mvZ θ a Z ρ).submatrix id π) = C.mvB a fun ρ => (Z ρ).submatrix id π := by
    funext ρ
    ext i j
    rfl
  have hB' := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 _ hB).2.2.2.2.2 a).1
  have hZ' : IsONeg T X.p0 (mvZ θ a Z) := (H _).1.2 (em ▸ hB')
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  have hd' := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB'
  have e1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).2 f ((((H Z).2 hZ).2.1 φ f).2 hf)
  refine (((H _).2 hZ').2.1 _ _).1 ?_
  have hφ' : GlobalTheory.SW.IsSB (((χS y : Circle) : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 _
  rw [em, e1, om_real C hW hη ha hy hB hφ, ← (GlobalTheory.Ker.Ctx.th_laws D S T C _ hd' φ hφ).2.1]
  exact (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd' _ hφ').1

end GlobalTheory.OneMapRef.RealMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterData
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiTame

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_pow_sub_pow_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (k : ℕ) : A.valuation (x ^ k - y ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : x ^ (k + 1) - y ^ (k + 1) = (x ^ k - y ^ k) * x + (x - y) * y ^ k := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hy k)) h

theorem ine_fix_root {A : ValuationSubring Ω} {m : ℕ} (hm : A.valuation (m : Ω) = 1) (hm0 : m ≠ 0) {ζ : Ω}
    (hζ : ζ ^ m = 1) {ρ : G E Ω} (hρ : ρ ∈ Ine (F := E) A) : ρ ζ = ζ := by
  have hζ1 : A.valuation ζ = 1 := GlobalTheory.val_eq_one_of_pow_eq_one A hm0 hζ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hm0] at hζ; exact zero_ne_one hζ
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hm ?_ ?_
    · rw [mul_pow, ← map_pow, inv_pow, hζ, map_one, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  exact (mul_inv_eq_one₀ hζ0).1 hξ

theorem eq_one_of_wild [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {K : Type} [Field K] [TopologicalSpace K] [T2Space K] (r : G E Ω →* Kˣ)
    (hr : Continuous r) {m : ℕ} (hm : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal) (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ m = 1)
    (τ : G E Ω) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : r τ = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  by_contra hne
  have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
  have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
  have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
    intro h
    apply hm
    obtain ⟨c, hc⟩ := hd
    rw [hc, hk]
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
  have h1 : r (τ ^ k) = 1 := by
    refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
      (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
    rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  rw [map_pow] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ho (by simpa using hk)
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
  rw [hk] at h3
  have := hl.two_le
  have := Nat.pos_of_ne_zero hk0
  nlinarith

theorem exists_pow_pair [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {γ : G E Ω} (hγ : TameGenAt A γ) {K : Type} [Field K] [TopologicalSpace K] [T2Space K]
    (r : G E Ω →* Kˣ) (hr : Continuous r) {m : ℕ} (hm : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal)
    (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) {π : Ω} (hπ0 : π ≠ 0) {c : E} (hπ : π ^ m = algebraMap E Ω c)
    {ρ : G E Ω} (hρ : ρ ∈ Ine (F := E) A) : ∃ n : ℕ, ρ π = (γ π / π) ^ n * π ∧ r ρ = r γ ^ n := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hmA : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A m)) (not_lt.mp fun h => hm ?_)
    rw [← hA]
    simpa using h
  have hroot : ∀ σ : G E Ω, (σ π / π) ^ m = 1 := fun σ => by
    rw [div_pow, ← map_pow, hπ, σ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  set ζ := γ π / π with hζ
  have hζm : ζ ^ m = 1 := hroot γ
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hK : ∀ σ ∈ Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}),
      σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, σ π = ζ ^ n * π ∧ r σ = r γ ^ n := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem τ hτ =>
      rcases hτ with rfl | hτ
      · exact ⟨hγ.1, 1, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ0], (pow_one _).symm⟩
      · refine ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hτ, 0, ?_, by rw [pow_zero, eq_one_of_wild hA r hr hm hI τ hτ]⟩
        have := GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hmA (hroot τ) (hτ π hπ0)
        rw [pow_zero, one_mul]
        exact (div_eq_one_iff_eq hπ0).1 this
    | one => exact ⟨one_mem _, 0, by simp, by simp⟩
    | mul σ τ _ _ h1 h2 =>
      obtain ⟨i1, a, a1, a2⟩ := h1
      obtain ⟨i2, b, b1, b2⟩ := h2
      refine ⟨mul_mem i1 i2, a + b, ?_, by rw [map_mul, a2, b2, pow_add]⟩
      rw [AlgEquiv.mul_apply, b1, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1]
      ring
    | inv σ _ h1 =>
      obtain ⟨i1, a, a1, a2⟩ := h1
      refine ⟨inv_mem i1, a * m', ?_, ?_⟩
      · apply σ.injective
        rw [mul_inv_apply, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1, ← mul_assoc, ← pow_add,
          show a * m' + a = (m' + 1) * a by ring, pow_mul, hζm, one_pow, one_mul]
      · rw [map_inv, a2, inv_eq_iff_mul_eq_one, ← pow_add, show a + a * m' = (m' + 1) * a by ring, pow_mul,
          hI γ hγ.1, one_pow]
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hfin : ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ}).Finite := (GlobalTheory.TameGenPowers.finite_roots K _ hm0).diff
  have ho1 : IsOpen (r ⁻¹' ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ})ᶜ) := hfin.isClosed.isOpen_compl.preimage hr
  have ho2 := (stabilizer_isOpen_of_isIntegral (K := E) π).preimage (continuous_const_mul ρ⁻¹)
  obtain ⟨σ, ⟨h1, h2⟩, h3⟩ := mem_closure_iff.1 (hγ.2 hρ) _ (ho1.inter ho2) ⟨by simp, by simp⟩
  obtain ⟨i1, n, n1, n2⟩ := hK σ h3
  refine ⟨n, ?_, ?_⟩
  · have h4 : (ρ⁻¹ * σ) π = π := h2
    rw [← n1]
    conv_lhs => rw [← h4]
    rw [AlgEquiv.mul_apply, mul_inv_apply]
  · rw [← n2]
    by_contra hne
    exact h1 ⟨hI σ i1, fun h => hne (Eq.symm h)⟩

theorem exists_tameRep (hP : GlobalTheory.Published.GlobalArtinReciprocity) [_root_.NumberField.IsTotallyComplex E] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {g : ℕ} (hg : g.Prime) (hN : normV v = g) (hgv : ((g : ℕ) : 𝓞 E) ∈ v.asIdeal)
    (hgv2 : ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2)
    (hunit : ∀ a : ℕ, a.Coprime g → ∀ x : Eˣ, (x : E) = a → IsUnitAt v (atFin v x))
    {γ : G E Ω} (hγ : TameGenAt A γ) {K : Type} [Field K] [TopologicalSpace K] [T2Space K]
    (r : G E Ω →* Kˣ) (hr : Continuous r) (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ (g - 1) = 1) :
    ∃ (u : 𝓞 E) (hu : (u : E) ≠ 0), NX.TameRep v 1 γ u ∧ IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) ∧
      ∃ σ : G E Ω, art (localIdele E v (atFin v (Units.mk0 (u : E) hu))) = toAb E Ω σ ∧ r σ = r γ := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 := hg.two_le
  have hm : 0 < g - 1 := by omega
  have hg1 : ((g - 1 : ℕ) : 𝓞 E) ∉ v.asIdeal := fun h => by
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := v.asIdeal.sub_mem hgv h
    rwa [Nat.cast_sub hg.one_le, Nat.cast_one, sub_sub_cancel] at this
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (((g : ℕ) : 𝓞 E) : E)) hm
  have hgE : (((g : ℕ) : 𝓞 E) : E) ≠ 0 := by simpa using hg.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hgE hπ
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hb
  set a : ℕ := (b : ZMod g).val with hadef
  have hac : a.Coprime g := ZMod.val_coe_unit_coprime b
  have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
    have : a ≠ 0 := by
      intro h
      rw [h, Nat.coprime_zero_left] at hac
      exact hg.ne_one hac
    simpa using this
  have hx := hunit a hac (Units.mk0 _ ha0) (by simp)
  obtain ⟨σ, hσ, eσ, vσ⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hP E Ω art ha v A hA g hgv hgv2 π (by rw [hN]; exact hπ)
    _ (a : 𝓞 E) hx (by
      show Valued.v (algebraMap E (v.adicCompletion E) ((a : 𝓞 E) : E) - _) < 1
      rw [sub_self, map_zero]
      exact zero_lt_one)
  obtain ⟨n, n1, n2⟩ := exists_pow_pair hA hγ r hr hg1 hI hπ0 hπ hσ
  set ζ := γ π / π with hζ
  have hζm : ζ ^ (g - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, γ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  rw [n1, mul_div_cancel_right₀ _ hπ0] at vσ
  have hζ1 : A.valuation (ζ ^ n) ≤ 1 := by
    rw [map_pow, GlobalTheory.val_eq_one_of_pow_eq_one A hm.ne' hζm, one_pow]
  have haA : A.valuation (algebraMap E Ω ((a : 𝓞 E) : E)) ≤ 1 := by
    have : algebraMap E Ω ((a : 𝓞 E) : E) = (a : Ω) := by simp
    rw [this]
    exact (A.valuation_le_one_iff _).mpr (natCast_mem A a)
  have hpow := val_pow_sub_pow_lt A hζ1 haA vσ
  have hcop : n.Coprime (g - 1) := by
    obtain ⟨e, he⟩ := Nat.gcd_dvd_right n (g - 1)
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left n (g - 1)
    have h1 : (ζ ^ n) ^ e = 1 := by
      rw [← pow_mul, show n * e = (g - 1) * n' by rw [he]; nth_rewrite 1 [hn']; ring, pow_mul, hζm, one_pow]
    have h2 := hpow e
    rw [h1] at h2
    have h3 : ((1 - (a : ℤ) ^ e : ℤ) : 𝓞 E) ∈ v.asIdeal := by
      rw [← hA]
      simpa using h2
    have h4 : (g : ℤ) ∣ 1 - (a : ℤ) ^ e := by
      by_contra hnd
      obtain ⟨s, t, hst⟩ := ((Nat.prime_iff_prime_int.1 hg).irreducible.coprime_iff_not_dvd.2 hnd).map
        (Int.castRingHom (𝓞 E))
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hst]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ (by simpa using hgv)) (v.asIdeal.mul_mem_left _ h3)
    have h5 : b ^ e = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).2 h4
      apply Units.ext
      push_cast at this
      rw [hadef, ZMod.natCast_zmod_val, sub_eq_zero] at this
      rw [Units.val_pow_eq_pow_val, ← this, Units.val_one]
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hb] at h6
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have h7 := Nat.le_of_dvd he0 h6
    have h8 : 0 < Nat.gcd n (g - 1) := Nat.gcd_pos_of_pos_right _ hm
    show Nat.gcd n (g - 1) = 1
    generalize Nat.gcd n (g - 1) = d at *
    nlinarith
  obtain ⟨k, hk⟩ : ∃ k, n * k ≡ 1 [MOD g - 1] :=
    ⟨n ^ (Nat.totient (g - 1) - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
      exact Nat.ModEq.pow_totient hcop⟩
  have hu : (((a : 𝓞 E) ^ k : 𝓞 E) : E) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (by simpa using ha0)
  have hmk : Units.mk0 _ hu = Units.mk0 _ ha0 ^ k := Units.ext (by simp)
  refine ⟨(a : 𝓞 E) ^ k, hu, ⟨A, hA, hγ.1, g, π, hgv, hgv2, by rw [hN]; exact hπ, ?_⟩,
    hunit (a ^ k) (hac.pow_left k) _ (by simp), σ ^ k, ?_, ?_⟩
  · have h1 := hpow k
    rw [← pow_mul, pow_eq_pow_of_modEq hk hζm, pow_one, ← map_pow] at h1
    simpa using h1
  · rw [hmk, map_pow, map_pow, map_pow, map_pow, eσ]
  · rw [map_pow, n2, ← pow_mul, pow_eq_pow_of_modEq hk (hI γ hγ.1), pow_one]

end General

end GlobalTheory.ChiTame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembership
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocLevel

theorem mem_placesOver_of_overPl' {D : D7} {p : ℕ} {w w' : PlE D.host}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hw : NG.OverPl w v) (hw' : NG.OverPl w' v)
    (h : w' ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have h1 : ((p : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw', Ideal.mem_comap, map_natCast]; exact h
  rw [← hw, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem overPl_of_isConjPl {D : D7} {w : PlE D.host} {s : SplitPlace D.host.E} (hc : IsConjPl D.host w s.w) :
    NG.OverPl w s.v := by
  unfold NG.OverPl
  rw [← s.w_under]
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  apply hc
  have hy := GlobalTheory.SplitConjPlace.cO_algebraMap a
  set y := algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) a
  have e1 : (y : D.host.E) = IsCMField.complexConj D.host.E (y : D.host.E) := by
    conv_lhs => rw [← hy]
    rw [IsCMField.coe_ringOfIntegersComplexConj]
  rw [e1]
  conv_rhs => rw [← e1]
  exact D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])


end GlobalTheory.LocLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpanStatement
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)), (∀ x ∈ l, 1 ≤ x.2) → (l.map Prod.snd).sum = n → (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach <;> assumption)
end

