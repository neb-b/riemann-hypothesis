module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LatMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem inLat_gl (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (a : ℝ)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (γ : GL (Fin n) D.host.E) (v : VV ℂ lam) (h : InLat lam w a Λ v) :
    InLat lam w a (Λ.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)))
      (rhoVr (tauE D) lam γ v) := by
  obtain ⟨u, s, rfl, hs, ha, hu⟩ := h
  refine ⟨rhoVr (labLL D) lam γ u, s, (TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.rhoVr_mapVV lam γ u).symm, hs, ha, ?_⟩
  rw [← map_smul]
  exact TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.nabAtr_map _ lam γ Λ _ hu

theorem UpperTheory.WildA.latMove :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (a : ℝ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
      (U : Matrix.unitaryGroup (Fin n) D.host.E) (v : VV ℂ lam),
      InLat lam w a (SDLat.smulLat U.1 Λ) (rhoVr (tauE D) lam (Unitary.toUnits U) v) ↔ InLat lam w a Λ v := by
  intro D n lam w a Λ U v
  have e : SDLat.smulLat U.1 Λ = Λ.map ((Matrix.mulVecLin ((Unitary.toUnits U : GL (Fin n) D.host.E) :
      Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl
  rw [e]
  generalize (Unitary.toUnits U : GL (Fin n) D.host.E) = γ
  refine ⟨fun h => ?_, inLat_gl D lam w a Λ γ v⟩
  have h2 := inLat_gl D lam w a _ γ⁻¹ _ h
  have e1 : rhoVr (tauE D) lam γ⁻¹ (rhoVr (tauE D) lam γ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : (Λ.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E))).map
      ((Matrix.mulVecLin ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) = Λ := by
    rw [← Submodule.map_comp]
    have e3 : ((Matrix.mulVecLin ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)).comp
        ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show (γ⁻¹).1 *ᵥ (γ.1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e3, Submodule.map_id]
  rwa [e1, e2] at h2
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ParBdGeneric
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open GlobalTheory.SignedHC

private theorem parBd_block {c x : ℚ} {len : ℕ} (h : x ∈ TPar.block c len) :
    |(x : ℝ) - (c : ℝ)| ≤ (len : ℝ) / 2 := by
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 h
  have : (a' : ℝ) + 1 ≤ len := by exact_mod_cast (Finset.mem_range.1 ha')
  have h0 : (0 : ℝ) ≤ a' := Nat.cast_nonneg a'
  push_cast
  rw [abs_le]; constructor <;> linarith

private theorem parBd_generic (G : GlobalTheory.SignedHC.GridData) (B : ℝ) (hB : 12 ≤ B) (hN : G.NearMid)
    (hv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ B) (ha : ((G.a 0 : ℚ) : ℝ) ≤ B)
    (hb : ∀ l, 1 ≤ l → l ≤ G.m → (0 : ℝ) ≤ G.b l ∧ (G.b l : ℝ) ≤ G.e l ∧ (G.e l : ℝ) ≤ 4 * B)
    (ht : (G.t : ℝ) ≤ B) (hs : (G.s : ℝ) ≤ B) {j : ℕ} (hj : j ≤ G.m) :
    (∀ i, ∀ x ∈ entries (G.parD i j), |(x : ℝ)| ≤ 5 * B) ∧ ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * B := by
  have hal : ∀ l, l ≤ G.m → (0 : ℝ) ≤ ((G.a l : ℚ) : ℝ) ∧ ((G.a l : ℚ) : ℝ) ≤ B := by
    intro l hl
    have h2 := (hv 2 le_rfl G.two_le_k).1
    have hl' : (l : ℝ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℝ) ≤ l := by positivity
    have hg : (0 : ℝ) ≤ G.ga := by positivity
    have h1 : (0 : ℝ) ≤ (l : ℝ) * G.ga := mul_nonneg hl0 hg
    have h3 : (0 : ℝ) ≤ ((G.m : ℝ) + 1 - l) * G.ga := mul_nonneg (by linarith) hg
    unfold GlobalTheory.SignedHC.GridData.a at ha ⊢
    push_cast at ha ⊢
    constructor <;> nlinarith
  have hcen : ∀ l, 1 ≤ l → l ≤ G.m → |(((G.cen l : ℤ) : ℚ) : ℝ)| ≤ B + 1 := by
    intro l h1 h2
    have e := hN l (Finset.mem_Icc.2 ⟨h1, h2⟩)
    have e' : |(((G.cen l : ℤ) : ℚ) : ℝ) - (((G.a (l - 1) : ℚ) : ℝ) + ((G.a l : ℚ) : ℝ)) / 2| ≤ 1 := by
      unfold GlobalTheory.SignedHC.GridData.mid at e
      exact_mod_cast e
    have a1 := hal l h2
    have a2 := hal (l - 1) (by omega)
    rw [abs_le] at e' ⊢
    constructor <;> linarith [e'.1, e'.2, a1.1, a1.2, a2.1, a2.2]
  have hC : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.s → ∀ x ∈ TPar.block (G.cen l : ℚ) len, |(x : ℝ)| ≤ 5 * B := by
    intro l len h1 h2 h3 x hx
    have e := abs_le.1 (parBd_block hx)
    have e' := abs_le.1 (hcen l h1 h2)
    have : (len : ℝ) ≤ G.s := by exact_mod_cast h3
    rw [abs_le]; constructor <;> linarith [e.1, e.2, e'.1, e'.2]
  have hM : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.t + 1 → ∀ x ∈ TPar.block (-(G.e l : ℚ)) len, |(x : ℝ)| ≤ 5 * B := by
    intro l len h1 h2 h3 x hx
    have e := abs_le.1 (parBd_block hx)
    obtain ⟨b1, b2, b3⟩ := hb l h1 h2
    have : (len : ℝ) ≤ G.t + 1 := by exact_mod_cast h3
    push_cast at e
    rw [abs_le]; constructor <;> linarith [e.1, e.2]
  constructor
  · intro i x hx
    obtain ⟨sg, hx⟩ := mem_entries.1 hx
    rcases GlobalTheory.SignedHC.GridData.mem_parD.1 hx with ⟨hc, -⟩ | ⟨l, h1, h2, he⟩ | ⟨l, h1, h2, hc, -⟩ | ⟨l, h1, h2, hc, -⟩
    · obtain ⟨i', h2, hk, e⟩ := GlobalTheory.SignedHC.GridData.mem_cloud.1 hc
      simp only at e
      obtain ⟨v1, v2⟩ := hv i' h2 hk
      rw [e]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have e : x = -(G.b l : ℚ) := congrArg Prod.fst he
      obtain ⟨b1, b2, b3⟩ := hb l h1 h2
      rw [e]; push_cast
      rw [abs_le]; constructor <;> linarith
    · exact hM l G.t h1 (by omega) (by omega) x hc
    · exact hC l G.s (by omega) h2 le_rfl x hc
  · intro x hx
    rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨l, h1, h2, hc⟩ | ⟨l, h1, h2, hc⟩
    · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
      obtain ⟨a1, a2⟩ := hal i hi
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨i, h2, hk, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
      obtain ⟨v1, v2⟩ := hv i h2 hk
      unfold GlobalTheory.SignedHC.GridData.vHalf
      push_cast
      rw [abs_le]; constructor <;> linarith
    · exact hC l (G.s - 1) h1 h2 (by omega) x hc
    · exact hM l (G.t + 1) h1 (by omega) le_rfl x hc

end

theorem UpperTheory.WildA.parBd :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → ∀ X : Node, DefNode D.R.m X → ∀ (τ : D.what₂.Tau),
      ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D 1 X τ), |(x : ℝ)| ≤ 6 * large₂.sc.b := by
  intro D large₂ hS hH X hX τ
  obtain ⟨hN, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, he0⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have he : ∀ l : Fin D.R.m, (((D.hc τ).e l : ℚ) : ℝ) = ((G.e (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).e l = ((G.e (l.1 + 1) : ℤ) : ℚ) := he0 l
    rw [e, Rat.cast_intCast]
  have hprod : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by positivity
  have hvv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ large₂.Sc := by
    intro i h2 hi
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h2
    have h := large₂.cloud_v τ ⟨a, by omega⟩
    rw [hv] at h
    exact h
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    unfold bigN
    have : 1 * (D.R.t + sLen D + 1) ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hgen : ∀ j, j ≤ G.m → (∀ i, ∀ x ∈ GlobalTheory.SignedHC.entries (G.parD i j), |(x : ℝ)| ≤ 5 * large₂.sc.b) ∧
      ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * large₂.sc.b := by
    intro j hj
    refine parBd_generic G large₂.sc.b h12 (GlobalTheory.ChiGrid.num_nearMid D 1 τ) ?_ ?_ ?_ ?_ ?_ hj
    · intro i h2 hi
      obtain ⟨a, b⟩ := hvv i h2 hi
      exact ⟨a, by linarith⟩
    · have h := (hvv 2 le_rfl G.two_le_k).2
      have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        unfold GlobalTheory.SignedHC.GridData.a; rw [hm, hga]; push_cast; ring
      rw [e]; linarith
    · intro l h1 hl
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h1
      obtain ⟨p1, p2⟩ := hpos τ ⟨a, by omega⟩
      have g := (hH.gap τ ⟨a, by omega⟩).1
      have ht0 : (0 : ℚ) ≤ D.R.t := by positivity
      have g' : (D.hc τ).b ⟨a, by omega⟩ ≤ (D.hc τ).e ⟨a, by omega⟩ := by linarith
      have g'' : (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) ≤ (((D.hc τ).e ⟨a, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast g'
      have p1' : (0 : ℝ) ≤ (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast p1.le
      rw [hb] at p1' g''
      rw [he] at p2 g''
      exact ⟨p1', g'', p2⟩
    · have : (D.R.t : ℝ) ≤ bigN D := by exact_mod_cast (by omega : D.R.t ≤ bigN D)
      exact this.trans hN
    · have : (sLen D : ℝ) ≤ bigN D := by exact_mod_cast (by omega : sLen D ≤ bigN D)
      exact this.trans hN
  intro x hx
  cases X with
  | core i => exact hX.elim
  | top j =>
    obtain ⟨sg, hx⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have h := (hgen j hX).2 x (GlobalTheory.SignedHC.mem_plus.1 hx).1
    linarith
  | grid i j =>
    obtain ⟨sg, hx⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have hj : j ≤ G.m := le_of_eq hX.2
    have hx' := GlobalTheory.SignedHC.mem_shift.1 hx
    have h := (hgen j hj).1 i _ (GlobalTheory.SignedHC.fst_mem_entries hx')
    simp only at h
    rw [abs_le] at h ⊢
    split_ifs at h <;> push_cast at h <;> constructor <;> linarith [h.1, h.2]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.PrimeEqOfMemPrimeIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.WildA.prime_eq_of_mem_prime_ideal {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (ha : a.Prime)
    (hb : b.Prime) (hai : (a : R) ∈ I) (hbi : (b : R) ∈ I) : a = b := by
  by_contra hne
  have h : Nat.Coprime a b := (Nat.coprime_primes ha hb).2 hne
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hai) (Ideal.mul_mem_left _ _ hbi)

private theorem UpperTheory.WildA.split_of_split_class {D : D7} {p : ℕ} (h : D.host.cls p = .splitK) : GlobalTheory.NormSum.SplitIn D p := by
  right
  unfold Formalism.BasicNotions.Host.cls primeClass at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact h4 | cases h

theorem UpperTheory.WildA.small_set_primes_split :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → ∀ v ∈ G.pl.S0, ∀ l : ℕ, l.Prime → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := by
  intro D T L sc G large₂ hS v hv l hl hlv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hS
  have key : ∀ p : ℕ, p.Prime → p ∈ D.host.levelPrimes → ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      GlobalTheory.NormSum.SplitIn D l := fun p hp hm h => by
    rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal v.isPrime hl hp hlv h]
    exact UpperTheory.WildA.split_of_split_class (Pm.level_split p hm)
  rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
  · rw [UpperTheory.WildA.prime_eq_of_mem_prime_ideal G.pl.v0.isPrime hl (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1 hlv G.pl.basePlace_over_qZero]
    exact Or.inr (Formalism.L2.Host.split_prime_jacobi_neg_d D)
  · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
    · exact key _ (D.host.g_prime 0) (D.host.g_level 0) h
    · exact key _ (D.host.g_prime 1) (D.host.g_level 1) h
    · exact key _ D.host.pde_prime D.host.pde_level.1 h
    · exact key _ D.host.pde'_prime D.host.pde_level.2 h
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatMove
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem lin_rat {ι κ V W : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Subfield ℂ) (b : Module.Basis ι ℂ V) (c : Module.Basis κ ℂ W) (f : V →ₗ[ℂ] W)
    (hf : ∀ i j, c.repr (f (b j)) i ∈ A) (v : V) (hv : ∀ j, b.repr v j ∈ A) (i : κ) : c.repr (f v) i ∈ A := by
  rw [← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hv j) (hf i j)

private theorem rho_rat {ι E : Type} [Fintype ι] [Field E] {n : ℕ} (A : Subfield ℂ) (emb : ι → E →+* ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (lam : ι → DomWeight n) (g : GL (Fin n) E) (i j : VVIdx lam) :
    (bVV ℂ lam).repr (rhoVr emb lam g (bVV ℂ lam j)) i ∈ A := by
  refine actionRational_holds ℂ ι n lam A (invTrK (embGL emb g)) (fun τ a b => ?_) i j
  show ((((Formalism.UG.bc (emb τ) g)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
  rw [← map_inv]
  exact hA τ _

theorem UpperTheory.WildA.ratMove :
    ∀ (D : D7) {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n') (f f' : VV ℂ lam →ₗ[ℂ] VV ℂ lam')
      (g : GL (Fin n) D.host.E) (g' : GL (Fin n') D.host.E), f' ∘ₗ rhoVr (tauE D) lam g = rhoVr (tauE D) lam' g' ∘ₗ f →
      (∀ i j, (bVV ℂ lam').repr (f (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL) →
      ∀ i j, (bVV ℂ lam').repr (f' (bVV ℂ lam j)) i ∈ Set.range D.what₂.embLL := by
  intro D n n' lam lam' f f' g g' h hf i j
  have hlab : ∀ τ x, tauE D τ x ∈ D.what₂.embLL.fieldRange := fun τ x =>
    ⟨labLL D τ x, DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x⟩
  have e : f' (bVV ℂ lam j) = rhoVr (tauE D) lam' g' (f (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))) := by
    have h1 := LinearMap.congr_fun h (rhoVr (tauE D) lam g⁻¹ (bVV ℂ lam j))
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at h1
    exact h1
  rw [e]
  exact lin_rat D.what₂.embLL.fieldRange _ _ _ (rho_rat _ _ hlab lam' g') _
    (lin_rat D.what₂.embLL.fieldRange _ _ f hf _ fun k => rho_rat _ _ hlab lam g⁻¹ k j) i
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RatReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.ratReal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (r : FinPt G X)
      (U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E), GlobalTheory.RatMoveJets.RatCoord _ (fr X) r U →
      ∃ γ ∈ GQ (G.V X), ∃ k ∈ GinfC (G.V X), (∀ x : FinPt G X, ((r * x : FinPt G X) : GA D (G.V X)) = γ * ((x : GA D (G.V X)) * k)) ∧
        GlobalTheory.DefStep.realAct W.θ fr X k⁻¹ = rhoVr (tauE D) (wt G X) (Unitary.toUnits U) := by
  intro D T L sc G W fr X r U h
  obtain ⟨γ, hγ, hf, hm⟩ := h
  have hk : γ⁻¹ * (r : GA D (G.V X)) ∈ GinfC (G.V X) := by
    show finHom (G.V X) (γ⁻¹ * (r : GA D (G.V X))) = 1
    rw [map_mul, map_inv, hf, inv_mul_cancel]
  refine ⟨γ, hγ, γ⁻¹ * (r : GA D (G.V X)), hk, fun x => ?_, ?_⟩
  · have hc := GlobalTheory.AdelicSplit.commute_GinfC_GfC (G.V X) hk x.2
    rw [← hc, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    rfl
  · have hrat : Bridge.IsRatMat (G.V X) ⟨γ, hγ⟩ (fr X * Unitary.toUnits U * (fr X)⁻¹) := Units.ext hm
    have hin : GlobalTheory.DefStep.realIn W.θ fr X γ = embGL (tauE D) (Unitary.toUnits U) := by
      funext τ
      have h1 := GlobalTheory.CoefModel.realGL_rat W.θ_is (G.V X) ⟨γ, hγ⟩ _ hrat τ
      have h2 : GlobalTheory.DefStep.realIn W.θ fr X γ τ = (GlobalTheory.DefStep.frGL fr X τ)⁻¹ *
          GlobalTheory.CoefModel.realGL W.θ (G.V X) γ τ * GlobalTheory.DefStep.frGL fr X τ := by
        simp [GlobalTheory.DefStep.realIn]
      rw [h2, h1, map_mul, map_mul, map_inv, GlobalTheory.DefStep.frGL]
      show _ = Formalism.UG.bc (tauE D τ) (Unitary.toUnits U)
      group
    rw [_root_.mul_inv_rev, inv_inv, map_mul,
      GlobalTheory.DefStep.realAct_fin W.θ fr X (inv_mem r.2), one_mul, GlobalTheory.DefStep.realAct, MonoidHom.comp_apply,
      MonoidHom.comp_apply, hin]
    rfl
end

