module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteLevelApproxOfGeometricInvariantModPo
section
open GlobalTheory.K5

namespace GlobalTheory.K5.GeoLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_zeta (T : Tower p Ω) (n : ℕ) : IsAlgZp p (T.ζ n) := by
  refine ⟨Polynomial.X ^ (p ^ n) - 1, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · simp [(T.prim n).pow_eq_one]

def ggens (T : Tower p Ω) (N : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x} ∪ T.qq '' Set.Iic N

theorem ggens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : ggens T m ⊆ ggens T n := by
  unfold ggens
  gcongr

theorem fixes_ggens (T : Tower p Ω) (N : ℕ) (g : Gal p Ω)
    (hg : g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N)) :
    ∀ a ∈ ggens T N, g a = a := by
  have hgeo : ∀ x : Ω, IsAlgZp p x → g x = x := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq N) = T.qq N := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ha) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · exact hgeo a ha
  · have hi' : i + (N - i) = N := Nat.add_sub_cancel' hi
    rw [GlobalTheory.K5.FinLevel.qq_eq_pow T i (N - i), hi', map_pow, hq]

theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h y = y) :
    ∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y := by
  haveI := GlobalTheory.K5.FinLevel.charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, ggens T n)
  have hmemL : ∀ a ∈ ⋃ n, ggens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hfix : ∀ a ∈ ⋃ n, ggens T n, g a = a := fun a ha => f.commutes ⟨a, hmemL a ha⟩
      have hg : g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n := by
        refine Subgroup.mem_inf.mpr ⟨fun x hx => hfix x (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr hx)⟩),
          Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
        · exact hfix _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inr (isAlgZp_zeta T n))⟩)
        · exact hfix _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ ggens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ ggens T (S.sup m) := fun t ht =>
    ggens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (ggens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (ggens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_ggens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.GeoLevel

theorem GlobalTheory.K5.geo_invariants_from_finite_level :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ x : Ω, IsInt (p := p) x →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (g x) x) →
  ∃ y : Ω, IsInt (p := p) y ∧ (∃ N, ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) ∧
    Cong (p := p) k ((T.ζ j - 1) * x) y := by
  intro p _ hp2 Ω _ _ hClo T k j hj x hx hfix
  obtain ⟨y₀, E, hy₀, hEH, huniq, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hClo T (Ggeo p Ω ⊓ ⨅ n, Gn T n) inf_le_right {x} j hj
  have hgi : ∀ (g : Gal p Ω) (z : Ω), IsInt (p := p) z → IsInt (p := p) (g z) := fun g z hz =>
    hz.map (g : Ω →ₐ[O0 p] Ω)
  refine ⟨∑ g ∈ E, g (y₀ * x), ?_, ?_, ?_⟩
  · exact IsIntegral.sum _ fun g _ => hgi g _ (hy₀.mul hx)
  · exact GlobalTheory.K5.GeoLevel.exists_level_of_fixed hClo T _
      (GlobalTheory.K5.FinLevel.sum_fixed _ E y₀ x hEH huniq)
  · have hz : ∀ g ∈ E, ∃ z : Ω, IsInt (p := p) z ∧ g x - x = (p : Ω) ^ k * z :=
      fun g hg => hfix g (hEH g hg)
    choose! z hzi hzx using hz
    refine ⟨-∑ g ∈ E, g y₀ * z g, ?_, ?_⟩
    · exact (IsIntegral.sum _ fun g hg => (hgi g _ hy₀).mul (hzi g hg)).neg
    · rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib, mul_neg, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_mul]
      linear_combination (-(g y₀)) * hzx g hg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Comm

open CongruenceSubgroup

theorem cj_sub {Γ : Type} (u v : Γ → ℂ[X]) : cj (u - v) = cj u - cj v := by
  funext γ
  simp [cj, Polynomial.map_sub]

theorem intCast_of_dvd {m n : ℕ} (h : m ∣ n) {x a : ℤ} (hx : ((x : ℤ) : ZMod n) = a) :
    ((x : ℤ) : ZMod m) = a := by
  have := congrArg (ZMod.castHom h (ZMod m)) hx
  simpa using this

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : GlobalTheory.Hk.IsDia N l d σ)
    (hτ : GlobalTheory.Hk.IsDia N l e τ) : GlobalTheory.Hk.IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h1)
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]
    ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]
    ring

theorem gamma_le_lev (N l : ℕ) : Gamma (N * l) ≤ Lev N l := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  refine ⟨?_, ?_⟩
  · change γ ∈ Gamma1 N
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h00)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h11)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h10)
  · change γ ∈ Gamma0 l
    rw [Gamma0_mem]
    simpa using intCast_of_dvd (dvd_mul_left l N) (a := 0) (by simpa using h10)

theorem comm_of_decomp {Γ : Subgroup SL(2, ℤ)} {w : ℕ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (hAc : ∀ z, cj (A z) = A (cj z)) (hBc : ∀ z, cj (B z) = B (cj z))
    (x y b : Γ → ℂ[X]) (hx : A (B x) - B (A x) ∈ B1 Γ w) (hy : A (B y) - B (A y) ∈ B1 Γ w)
    (hb : b ∈ B1 Γ w) :
    A (B (x + cj y + b)) - B (A (x + cj y + b)) ∈ B1 Γ w := by
  have hcj : ∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w := (cj_mem_Z1_cj_mem_B1_per_smul Γ w).2.1
  have e : A (B (x + cj y + b)) - B (A (x + cj y + b)) =
      (A (B x) - B (A x)) + cj (A (B y) - B (A y)) + (A (B b) - B (A b)) := by
    simp only [cj_sub, hAc, hBc, map_add (f := _)]
    abel
  rw [e]
  exact add_mem (add_mem hx (hcj _ hy)) (sub_mem (hA _ (hB _ hb)) (hB _ (hA _ hb)))

theorem per_comm {Γ : Subgroup SL(2, ℤ)} {w : ℕ} {k : ℤ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (FA FB : (ℍ → ℂ) → ℍ → ℂ)
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (mA : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FA ⇑f)
    (mB : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FB ⇑f)
    (eA : ∀ f : ModularForm Γ k, per Γ w (FA ⇑f) - A (per Γ w ⇑f) ∈ B1 Γ w)
    (eB : ∀ f : ModularForm Γ k, per Γ w (FB ⇑f) - B (per Γ w ⇑f) ∈ B1 Γ w)
    (hc : ∀ f : ModularForm Γ k, FA (FB ⇑f) = FB (FA ⇑f)) (f : ModularForm Γ k) :
    A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) ∈ B1 Γ w := by
  obtain ⟨g, hg⟩ := mB f
  obtain ⟨g', hg'⟩ := mA f
  have h1 := eB f
  have h2 := eA g
  have h3 := eA f
  have h4 := eB g'
  rw [hg] at h2
  rw [hg'] at h4
  have e : A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) =
      -A (per Γ w (FB ⇑f) - B (per Γ w ⇑f)) - (per Γ w (FA (FB ⇑f)) - A (per Γ w (FB ⇑f))) +
        (per Γ w (FB (FA ⇑f)) - B (per Γ w (FA ⇑f))) + B (per Γ w (FA ⇑f) - A (per Γ w ⇑f)) := by
    rw [hc f]
    simp only [map_sub]
    abel
  rw [e]
  exact add_mem (add_mem (sub_mem (neg_mem (hA _ h1)) h2) h4) (hB _ h3)

theorem heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  intro N l k hN hl hlN hk hodd q q' σ σ' τ τ' d d' hq hqNl hq' hq'Nl hσ hσ' hτ hτ' z hz
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨bUl, bDd, bTq, bDia, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level N l hN hl hlN
  have eqv := fun f => GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant N l k hN hl hlN hk f

  have opT : ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
      GlobalTheory.Hk.IsDia N l q σ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), TqZ (Lev N l) (k - 2) q σ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (TqZ (Lev N l) (k - 2) q σ z) = TqZ (Lev N l) (k - 2) q σ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = TqF (k : ℤ) q σ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro q σ hq hqn hs
    have dq : GlobalTheory.Hk.IsDia N l q σ := (bDia N l q σ).1 (by rwa [Int.cast_natCast])
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin (q + 1)) (dg 1 q) (tqFam q σ)
      (by simp [dg, Matrix.det_fin_two, hq.pos]) (rT q σ hq hqn hs)
    refine ⟨dq, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).1 q σ hq hqn hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.heckeT_modularForm N l q k σ hN0 hq hqn dq f
    exact ⟨g, hg.trans (bTq _ _ _ _ hq.pos).symm⟩

  have opU :
      (∀ z ∈ B1 (Lev N l) (k - 2), UlZ (Lev N l) (k - 2) l z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (UlZ (Lev N l) (k - 2) l z) = UlZ (Lev N l) (k - 2) l (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = UlF (k : ℤ) l ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin l) (dg 1 l) (ulFam l)
      (by simp [dg, Matrix.det_fin_two, hl.pos]) rU
    refine ⟨H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.1⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.uOp_modularForm N l l k hN0 hl0 hl (dvd_mul_left l N) f
    exact ⟨g, hg.trans (bUl _ _ _ hl0).symm⟩

  have opD : ∀ (d : ZMod N) (τ : SL(2, ℤ)), IsDiam N l d τ →
      GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), DdZ (Lev N l) (k - 2) τ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (DdZ (Lev N l) (k - 2) τ z) = DdZ (Lev N l) (k - 2) τ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = DdF (k : ℤ) τ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (DdF (k : ℤ) τ ⇑f) - DdZ (Lev N l) (k - 2) τ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro d τ hs
    have dτ : GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ := (bDia N l (mat τ 1 1) τ).1 ⟨hs.1, rfl⟩
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) Unit (mat τ) (fun _ => mat τ)
      (by simp [mat]) (rD d τ hs)
    refine ⟨dτ, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.2 d τ hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.dia_modularForm N l k (mat τ 1 1) τ hN0 dτ f
    exact ⟨g, hg.trans (bDd _ _ _).symm⟩

  obtain ⟨f, h, hES⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per N (N * l) (Lev N l) k hN (Nat.mul_pos hN0 hl0)
    (gamma_le_lev N l) inf_le_left hodd hk z hz
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ B1 (Lev N l) (k - 2),
      z = per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b :=
    ⟨_, hES, by abel⟩
  have hh : ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = ⇑h := ⟨ModularFormClass.modularForm h, rfl⟩
  obtain ⟨hm, hhm⟩ := hh
  have pair : ∀ (A B : Module.End ℂ (Lev N l → ℂ[X])) (FA FB : (ℍ → ℂ) → ℍ → ℂ),
      (∀ z ∈ B1 (Lev N l) (k - 2), A z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (A z) = A (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FA ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FA ⇑f) - A (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ z ∈ B1 (Lev N l) (k - 2), B z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (B z) = B (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FB ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FB ⇑f) - B (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ f : ModularForm (Lev N l) (k : ℤ), FA (FB ⇑f) = FB (FA ⇑f)) →
      A (B (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) -
        B (A (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) ∈ B1 (Lev N l) (k - 2) := by
    rintro A B FA FB ⟨hA, hAc, mA, eA⟩ ⟨hB, hBc, mB, eB⟩ hc
    have hy := per_comm A B FA FB hA hB mA mB eA eB hc hm
    rw [hhm] at hy
    exact comm_of_decomp A B hA hB hAc hBc _ _ b (per_comm A B FA FB hA hB mA mB eA eB hc f) hy hb

  have eT : ∀ (q : ℕ) (σ : SL(2, ℤ)), 0 < q → ∀ g, TqF (k : ℤ) q σ g = GlobalTheory.Hk.heckeT k q σ g :=
    fun q σ hq g => bTq _ q σ g hq
  have eU : ∀ g, UlF (k : ℤ) l g = GlobalTheory.Hk.uOp l g := fun g => bUl _ l g hl0
  have eD : ∀ (τ : SL(2, ℤ)) g, DdF (k : ℤ) τ g = GlobalTheory.Hk.dia k τ g := fun τ g => bDd _ τ g
  obtain ⟨dq, oTq⟩ := opT q σ hq hqNl hσ
  obtain ⟨dq', oTq'⟩ := opT q' σ' hq' hq'Nl hσ'
  obtain ⟨dτ, oDτ⟩ := opD d τ hτ
  obtain ⟨dτ', oDτ'⟩ := opD d' τ' hτ'
  refine ⟨pair _ _ _ _ oTq oTq' ?_, pair _ _ _ _ oTq opU ?_, pair _ _ _ _ oTq oDτ ?_,
    pair _ _ _ _ opU oDτ ?_, pair _ _ _ _ oDτ oDτ' ?_⟩
  · intro f
    simp only [eT q σ hq.pos, eT q' σ' hq'.pos]
    exact GlobalTheory.Hk.heckeT_comm N l q q' k σ σ' hN0 hq hq' hqNl hq'Nl dq dq' f
  · intro f
    simp only [eT q σ hq.pos, eU]
    exact (GlobalTheory.Hk.uOp_heckeT_comm N l l q k σ hN0 hl0 hl (dvd_mul_left l N) hq hqNl dq f).symm
  · intro f
    simp only [eT q σ hq.pos, eD]
    exact GlobalTheory.Hk.heckeT_dia_comm N l q k (mat τ 1 1) σ τ hN0 hq hqNl dq dτ f
  · intro f
    simp only [eU, eD]
    exact GlobalTheory.Hk.uOp_dia_comm N l l k (mat τ 1 1) τ hN0 hl0 hl (dvd_mul_left l N) dτ f
  · intro f
    simp only [eD]
    exact (GlobalTheory.Hk.dia_mul N l k _ _ τ' τ (τ' * τ) hN0 dτ' dτ (isDia_mul dτ' dτ) f).trans
      (GlobalTheory.Hk.dia_mul N l k _ _ τ τ' (τ' * τ) hN0 dτ dτ'
        (by rw [mul_comm (mat τ 1 1)]; exact isDia_mul dτ' dτ) f).symm

end GlobalTheory.HeckeFamilyMatrices.Comm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrand
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem strip_integrable_rankin : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  intro k e L N ε h b s hk he hs hL hNL hh hb hsum
  obtain ⟨-, hch⟩ := _root_.GlobalTheory.EisM.qs_summable_continuous h hh.1.1
  obtain ⟨-, hcb⟩ := _root_.GlobalTheory.EisM.qs_summable_continuous b hb
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', δ, hδ, hdec⟩ := _root_.GlobalTheory.EisM.cusp_decay k L N ε h 1 (by omega) hL hNL hh
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.EisM.qs_bdd_above_one b hb
  have fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]
  have hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
    ext τ; simp only [Set.mem_union, Set.mem_setOf_eq]; constructor
    · intro h; rcases lt_or_ge τ.im 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hmre : Measurable (fun τ : ℍ => τ.re) := UpperHalfPlane.continuous_re.measurable
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} :=
    ((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter
      (measurableSet_le measurable_const hmim)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1} :=
      (((_root_.GlobalTheory.EisM.stripLow_integrableOn_im_rpow s hs).const_mul C).add (_root_.GlobalTheory.EisM.integrableOn_sq_qs_low e b s he hs hb hsum)).div_const 2
    refine hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [hnorm]
    have hy := τ.im_pos
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; ring
    have e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; rw [hk]; push_cast; ring
    have amgm := two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))
    have hCb : A ^ 2 * y ^ k ≤ C := hC τ
    have hp : 0 ≤ y ^ (s + 1) := (Real.rpow_pos_of_pos hy _).le
    have : A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCb hp
    have h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s)) := by rw [← e3]; ring
    have h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1)) := by rw [← e1]; ring
    have h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s) := by rw [← e2]; ring
    rw [h1, h2, h3] at amgm
    linarith
  ·
    have hg := (_root_.GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)
    refine hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))
    rw [hnorm]
    have hy := τ.im_pos
    have hy1 : 1 ≤ τ.im := hτ.2
    have hd := hdec τ (by linarith)
    rw [one_smul] at hd
    have hB := hM τ hy1
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have hyk : 0 ≤ y ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hy _).le
    have hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]
      congr 2; push_cast; ring
    have hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y) := by
      have := Real.sqrt_le_sqrt hd
      rw [← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le] at this
      convert this using 2
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
    have hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have hr : 0 ≤ y ^ ((k : ℝ) / 2 + s) := (Real.rpow_pos_of_pos hy _).le
    calc A * B * y ^ ((k : ℝ) + s) = (A * y ^ ((k : ℝ) / 2)) * B * y ^ ((k : ℝ) / 2 + s) := by rw [hsplitpow]; ring
      _ ≤ (Real.sqrt C' * Real.exp (-(δ / 2) * y)) * M * y ^ ((k : ℝ) / 2 + s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr
      _ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring

end GlobalTheory.EisM
end

