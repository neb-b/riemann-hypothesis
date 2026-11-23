module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0098
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.BadPrimes

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_cofactor {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal := by
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
    rw [← hm, Ideal.map_le_iff_le_comap, ← hP]
  rcases P.isPrime.mul_le.1 hle with h | h
  · have : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q', hQ, hm⟩
  · have : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
    subst this
    exact ⟨Q, hQ.symm, hm.trans (mul_comm _ _)⟩

theorem absNorm_eq_of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v)
    (hq : (Ideal.absNorm v.asIdeal).Prime) {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨P', -, hm⟩ := exists_cofactor hs hP
  have h1 : Ideal.absNorm P.asIdeal * Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E), ← h2,
      Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E]
  have hP1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hP2 : Ideal.absNorm P'.asIdeal ≠ 1 := fun h => P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact (((Nat.Prime.mul_eq_prime_sq_iff hq hP1 hP2).1 h1)).1

theorem notMem_sq_of_split {v : HeightOneSpectrum (𝓞 F)} (hs : SplitAt E v) {a : 𝓞 F} (ha : a ∉ v.asIdeal ^ 2)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    algebraMap (𝓞 F) (𝓞 E) a ∉ P.asIdeal ^ 2 := by
  intro hm2
  obtain ⟨P', hne, hm⟩ := exists_cofactor hs hP
  have hav : a ∈ v.asIdeal := by
    rw [← hP, Ideal.under_def, Ideal.mem_comap]
    exact Ideal.pow_le_self two_ne_zero hm2
  obtain ⟨J, hJ⟩ := Ideal.dvd_span_singleton.2 hav
  have h1 : P.asIdeal * P.asIdeal ∣ P.asIdeal * (P'.asIdeal * Ideal.map (algebraMap (𝓞 F) (𝓞 E)) J) := by
    rw [← mul_assoc, ← hm, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton, Ideal.dvd_span_singleton, ← sq]
    exact hm2
  have h3 := (mul_dvd_mul_iff_left P.ne_bot).1 h1
  rcases P.prime.dvd_or_dvd h3 with h | h
  · exact hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top (Ideal.le_of_dvd h))).symm
  · have h4 : J ≤ v.asIdeal := by
      rw [← hP, Ideal.under_def, ← Ideal.map_le_iff_le_comap]
      exact Ideal.le_of_dvd h
    apply ha
    rw [← Ideal.span_singleton_le_iff_mem, hJ, sq]
    exact Ideal.mul_mono_right h4

end Split


open GlobalTheory.Proof.NarrowJetMoments in
theorem bad_primes : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ (((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u) := by
  classical
  intro X Pr sel S mu u hX hPr hsel hT hg P hP
  have hoff : ∀ Q ∈ rowSG Pr sel mu, ((Pr.T u : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ =>
    notMem_rowSG hPr hsel (hPr.T_prime u) hT (hPr.T_ne_g u) hQ
  have hmem : ∀ Q, Q ∈ Sall sel mu u ↔ Q ∈ Pr.vT u ∨ Q ∈ rowSG Pr sel mu := fun Q => by
    unfold Sall
    exact Finset.mem_union
  rcases (hmem P).1 hP with h | h
  · have hTP := T_mem hPr u ⟨P, h⟩
    refine ⟨fun hc => ?_, ?_, ?_, fun _ => h, fun _ => hTP⟩
    · rcases (hmem _).1 hc with h' | h'
      · apply conj_piT_notMem hPr u ⟨P, h⟩
        exact (mem_conjP P _).1 (decoFin_mem_of_mem_divs h')
      · exact hoff _ h' (natCast_mem_conjP.2 hTP)
    · rw [hPr.vT_norm u P h]
      exact hPr.T_prime u
    · rw [hPr.vT_norm u P h]
      exact (T_unif hX hPr u ⟨P, h⟩).2
  · have hn := hoff P h
    refine ⟨fun hc => ?_, ?_⟩
    · rcases (hmem _).1 hc with h' | h'
      · exact hn (natCast_mem_conjP.1 (T_mem hPr u ⟨_, h'⟩))
      · exact conjP_notMem_rowSG hX hPr hsel hg h h'
    have hlast : ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal ↔ P ∈ Pr.vT u :=
      ⟨fun h' => absurd h' hn, fun h' => T_mem hPr u ⟨P, h'⟩⟩
    rcases Finset.mem_union.1 h with h1 | h1
    · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h1
      rw [hPr.vG_norm i P hi]
      refine ⟨hPr.g_prime i, ?_, hlast⟩
      have hrk : 2 * X.f = Module.finrank ℚ X.E := by
        rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, ← hX.card_Tau, mul_comm]
        rfl
      have hcc : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
      refine GlobalTheory.SplitUnram.natCast_notMem_sq X.E (cO X.E) (X.conjO (Pr.piG i)) (Pr.g i) cO_cO (hPr.g_prime i) ?_ ?_ ?_
        (hPr.vG_norm i) P hi
      · rw [hcc, mul_comm, hPr.piG_norm i]
      · rw [hcc]
        exact (hPr.piG_cop i).symm
      · rw [← hrk, ← hPr.vG_card i]
        rfl
    · obtain ⟨v, ⟨hs, ⟨hq, hq2⟩, -⟩, rfl⟩ := good_of_mem_QE h1
      rw [absNorm_eq_of_split hX.rankE hs hq (hsel v)]
      refine ⟨hq, ?_, hlast⟩
      have := notMem_sq_of_split hs hq2 (hsel v)
      rwa [map_natCast] at this

end GlobalTheory.ThetaMove.BadPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BranchingOk
section
namespace GlobalTheory.LvT.BuiltChain

theorem branching_ok : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6 := Formalism.L2.DIV.BrJ.branching_interlacing_pairs

end GlobalTheory.LvT.BuiltChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CrdSurjective
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.IdxHom

open GlobalTheory.CharValCompare Matrix Kronecker

variable {E : Type} [Field E] {a b : ℕ}

def crd (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b →+ (Fin a × Fin b → E) where
  toFun x := (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec
  map_zero' := by simp
  map_add' x y := by
    rw [LinearMap.add_comp, LinearMap.comp_add, map_add (f := _), Matrix.vec_add]

theorem crd_apply (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    crd g g' x = (LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a))).vec := rfl

theorem crd_injective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Injective (crd g g') := by
  intro x y h
  rw [crd_apply, crd_apply, Matrix.vec_inj] at h
  have h1 := LinearMap.toMatrix'.injective h
  refine LinearMap.ext fun v => ?_
  have := LinearMap.congr_fun h1 (g.symm v)
  simpa using this

theorem crd_surjective (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) : Function.Surjective (crd g g') := by
  intro v
  obtain ⟨A, rfl⟩ := Matrix.vec_bijective.2 v
  refine ⟨(g' : Sp E b →ₗ[E] Sp E b) ∘ₗ Matrix.toLin' A ∘ₗ (g.symm : Sp E a →ₗ[E] Sp E a), ?_⟩
  rw [crd_apply]
  congr 1
  rw [← LinearMap.toMatrix'_toLin' A]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp

def chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) : Matrix (Fin a × Fin b) (Fin a × Fin b) E :=
  (LinearMap.toMatrix' ((g₂.symm : Sp E a →ₗ[E] Sp E a) ∘ₗ (g₁ : Sp E a →ₗ[E] Sp E a)))ᵀ ⊗ₖ
    LinearMap.toMatrix' ((g₁'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ (g₂' : Sp E b →ₗ[E] Sp E b))

theorem chg_mulVec (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    chg g₁ g₂ g₁' g₂' *ᵥ crd g₂ g₂' x = crd g₁ g₁' x := by
  rw [chg, crd_apply, crd_apply, Matrix.kronecker_mulVec_vec, Matrix.transpose_transpose,
    ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  congr 2
  refine LinearMap.ext fun v => ?_
  simp

theorem det_chg (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    (chg g₁ g₂ g₁' g₂').det = ((dt g₂)⁻¹ * dt g₁) ^ b * ((dt g₁')⁻¹ * dt g₂') ^ a := by
  rw [chg, Matrix.det_kronecker, Matrix.det_transpose, LinearMap.det_toMatrix', LinearMap.det_toMatrix',
    LinearMap.det_comp, LinearMap.det_comp, LinearEquiv.det_coe_symm, LinearEquiv.det_coe_symm, Fintype.card_fin,
    Fintype.card_fin, dt_eq, dt_eq, dt_eq, dt_eq]

variable [NumberField E]

theorem ordE_chg (P : HeightOneSpectrum (𝓞 E)) (g₁ g₂ : Sp E a ≃ₗ[E] Sp E a) (g₁' g₂' : Sp E b ≃ₗ[E] Sp E b) :
    ordE P (chg g₁ g₂ g₁' g₂').det =
      (b * ordE P (dt g₁) - a * ordE P (dt g₁')) - (b * ordE P (dt g₂) - a * ordE P (dt g₂')) := by
  have h : ∀ {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n), P.valuation E (dt f) = WithZero.exp (-ordE P (dt f)) := by
    intro n f
    rw [ordE, neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).2 (dt_ne f))]
  rw [det_chg, ordE, map_mul, map_pow, map_pow, map_mul, map_mul, map_inv₀, map_inv₀, h g₁, h g₂, h g₁', h g₂',
    ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_nsmul,
    ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.log_exp, nsmul_eq_mul, nsmul_eq_mul]
  ring

variable [StarRing E]

theorem mem_homAt_iff {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {g : Sp E a ≃ₗ[E] Sp E a} {g' : Sp E b ≃ₗ[E] Sp E b} (hg : IsFr P N g) (hg' : IsFr P N' g') (x : HomE E a b) :
    x ∈ homAt {P} N N' ↔ ∀ i, IntAt P (crd g g' x i) := by
  change (∀ Q ∈ ({P} : Finset _), ∀ y ∈ localization₂ Q.asIdeal N, x y ∈ localization₂ Q.asIdeal N') ↔ _
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro h ⟨j, i⟩
    have h1 := h _ ((hg _).2 (single_mem_stdAt P j))
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice] at h1
    have h2 := h1 i
    simpa [crd_apply, LinearMap.toMatrix'_apply] using h2
  · intro h y hy
    obtain ⟨z, rfl⟩ := g.surjective y
    rw [hg, stdAt, mem_localization_standardLattice] at hy
    rw [← g'.apply_symm_apply (x _), hg', stdAt, mem_localization_standardLattice]
    intro i
    have : g'.symm (x (g z)) =
        LinearMap.toMatrix' ((g'.symm : Sp E b →ₗ[E] Sp E b) ∘ₗ x ∘ₗ (g : Sp E a →ₗ[E] Sp E a)) *ᵥ z := by
      rw [LinearMap.toMatrix'_mulVec]
      rfl
    rw [this, Matrix.mulVec, dotProduct]
    exact intAt_sum _ _ fun j _ => (h (j, i)).mul (hy j)

theorem relIndex_homAt : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (P : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' → homAt {P} N₂ N₂' ≤ homAt {P} N₁ N₁' → (((homAt {P} N₂ N₂').toAddSubgroup.relIndex (homAt {P} N₁ N₁').toAddSubgroup : ℕ) : ℚ) = ((Ideal.absNorm P.asIdeal : ℕ) : ℚ) ^ (volExp P N₁ N₁' - volExp P N₂ N₂') := by
  intro E _ _ _ a b P N₁ N₂ N₁' N₂' h₁ h₂ h₁' h₂' hle
  obtain ⟨g₁, hg₁⟩ := exists_isFr P h₁
  obtain ⟨g₂, hg₂⟩ := exists_isFr P h₂
  obtain ⟨g₁', hg₁'⟩ := exists_isFr P h₁'
  obtain ⟨g₂', hg₂'⟩ := exists_isFr P h₂'
  have h0 : ∀ x, x ∈ (homAt {P} N₁ N₁').toAddSubgroup.map (crd g₁ g₁') ↔ ∀ i, IntAt P (x i) := by
    intro x
    obtain ⟨y, rfl⟩ := crd_surjective g₁ g₁' x
    rw [AddSubgroup.mem_map_iff_mem (crd_injective _ _), Submodule.mem_toAddSubgroup, mem_homAt_iff hg₁ hg₁']
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ (crd_injective g₁ g₁'),
    GlobalTheory.IdxDet.relIndex_mulVec E (Fin a × Fin b) P (chg g₁ g₂ g₁' g₂') _ _ ?_ h0 ?_ (AddSubgroup.map_mono hle),
    ordE_chg, volExp, volExp, ordDet_eq hg₁, ordDet_eq hg₂, ordDet_eq hg₁', ordDet_eq hg₂']
  · rw [det_chg]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
      (pow_ne_zero _ (mul_ne_zero (inv_ne_zero (dt_ne _)) (dt_ne _)))
  · intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, (h0 _).2 ((mem_homAt_iff hg₂ hg₂' y).1 hy), (chg_mulVec _ _ _ _ y).symm⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨y, rfl⟩ := crd_surjective g₂ g₂' v
      exact ⟨y, (mem_homAt_iff hg₂ hg₂' y).2 ((h0 _).1 hv), (chg_mulVec _ _ _ _ y).symm⟩

end GlobalTheory.IdxHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bottom_window_le (eps : ℝ) (K : G.Consts) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hK : 1 ≤ K.La) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ) ≤ s.b' := by
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  refine ⟨max x1 (32 * K.La * CN ^ 2), fun s R he hx hR => ?_⟩
  obtain ⟨-, -, hLa⟩ := hx1 s he (le_trans (le_max_left _ _) hx)
  obtain ⟨hLa1, hLa2⟩ := hLa K hK
  have hx2 : 32 * K.La * CN ^ 2 ≤ s.x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨-, hn⟩, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' : 1 < s.x := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hb : 0 < s.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hkp : (0 : ℝ) < R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk
  have hd0 : 0 < s.delta1 := Real.rpow_pos_of_pos hxp _
  have hd1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := s.eps_pos; linarith)
  have hy : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hxp _
  have hlog0 : 0 ≤ Real.log s.x := Real.log_nonneg hx1'.le
  have hlog : Real.log s.x ^ 2 ≤ 4 * s.x := by
    have h := Real.log_le_rpow_div hxp.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (s.x ^ (1 / 2 : ℝ)) ^ 2 = s.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]; norm_num
    calc Real.log s.x ^ 2 ≤ (s.x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := pow_le_pow_left₀ hlog0 h 2
      _ = 4 * (s.x ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = 4 * s.x := by rw [h2]
  have hKC : 0 ≤ K.La * CN ^ 2 := by positivity
  have hLa3 : G.La K s ≤ s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps := by
    refine hLa2.trans ?_
    rw [Real.rpow_two]
    have : K.La * CN ^ 2 * Real.log s.x ^ 2 ≤ s.x / 32 * (4 * s.x) :=
      mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    nlinarith
  have hLa0 : 0 ≤ G.La K s := hy.le.trans hLa1
  have hmain : 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s ≤ R.k := by
    calc 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s
        ≤ 2 * (2 * s.x ^ (2 + 8 * s.eps)) * 1 * s.x ^ s.eps * (s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps) := by
          gcongr
      _ = s.x ^ (2 + 8 * s.eps) * s.x ^ s.eps * s.x ^ (2 : ℝ) * s.x ^ s.eps := by ring
      _ = s.x ^ (2 + 8 * s.eps + s.eps + 2 + s.eps) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, ← Real.rpow_add hxp]
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk
  rw [div_le_iff₀ hkp]
  nlinarith

theorem middle_between {R : Ranks} (p : HCParam R) {S : ℝ}
    (hv : ∀ i : Fin (R.k - 1), 0 ≤ ((p.v i : ℚ) : ℝ) ∧ ((p.v i : ℚ) : ℝ) ≤ S) (i : Fin R.k) (h1 : 1 ≤ i.1)
    (h2 : i.1 + 1 < R.k) : 0 ≤ ((p.u i : ℚ) : ℝ) ∧ ((p.u i : ℚ) : ℝ) ≤ S := by
  obtain ⟨i, hi⟩ := i
  simp only at h1 h2
  have ha := p.u_gt_v ⟨i, by omega⟩
  have hb := p.v_gt_u ⟨i - 1, by omega⟩
  have he : (⟨i - 1 + 1, by omega⟩ : Fin R.k) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
  simp only [he] at hb
  have ha' : ((p.v ⟨i, by omega⟩ : ℚ) : ℝ) < ((p.u ⟨i, hi⟩ : ℚ) : ℝ) := by exact_mod_cast ha
  have hb' : ((p.u ⟨i, hi⟩ : ℚ) : ℝ) < ((p.v ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hb
  exact ⟨(hv _).1.trans ha'.le, hb'.le.trans (hv _).2⟩

theorem exists_sizeData_explicit : ∀ (eps : ℝ) (C : FC) (cD ch : ℝ), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (aT bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C.P.Cpde D.host → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → |dlogH D.host| ≤ s.x ^ s.eps → D.s.Del = (Delv s cD : ℚ) → D.host.CT2 = C.CT2 → Fintype.card D.what₂.Word = ⌈3 * Real.exp (C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → D.div.etaF = 6 * s.x ^ (-C.P.CF) → (∀ u, Real.log (D.mem u).A.GamP = C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) → (∀ t, (s.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ s.a + s.a / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧ s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ s.b' + 2 * (D.R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (D.R.k : ℝ)) → (∀ τ (t : D.host.TT) (h : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t → (D.hc τ).u ⟨0, h⟩ = (aT t : ℚ) + ((D.R.k : ℚ) - 1) / 2 ∧ (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = -(bT t : ℚ) - ((D.R.k : ℚ) - 1) / 2) → (∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0) → ∃ L : SizeData₂ D, L.sc = s ∧ L.aT = aT ∧ L.bT = bT ∧ Val C cD ch L := by
  intro eps C cD ch h0 h1 hC hcD hch
  obtain ⟨hfix, hCc, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  have hGam : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hCt : C.Ct = 401 := hfix.2.2.2.2.2.2.2.2.2
  obtain ⟨x1, hx1⟩ := bottom_window_le eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.windows_of_explicitParameters eps cD ch C.P.Cpde h0 h1 hcD hch
  refine ⟨max (max x1 x2) ((max C.P.Cpde 1) ^ (100 / eps)), ?_⟩
  intro s D aT bT he hx0 hR hH hHC hdl hDel hCT2 hW heta hG hwin htop hA
  have hx : max x1 x2 ≤ s.x := le_trans (le_max_left _ _) hx0
  have hCo : C.P.Cpde ≤ s.x ^ (s.eps / 100) := by
    have hM : (0 : ℝ) ≤ max C.P.Cpde 1 := le_trans zero_le_one (le_max_right _ _)
    have h3 : (max C.P.Cpde 1) ^ (100 / eps) ≤ s.x := le_trans (le_max_right _ _) hx0
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg hM _) h3 (show 0 ≤ eps / 100 by positivity)
    rw [← Real.rpow_mul hM, show 100 / eps * (eps / 100) = 1 by field_simp, Real.rpow_one] at h4
    rw [he]
    exact (le_max_left _ _).trans h4
  have hb := hx1 s D.R he (le_trans (le_max_left _ _) hx) hR
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ :=
    hx2 s D bT he (le_trans (le_max_right _ _) hx) hR hH
      (fun t => ⟨(hwin t).2.1, by linarith [(hwin t).2.2]⟩) hHC
  have hDelR : ((D.s.Del : ℚ) : ℝ) = (Delv s cD : ℝ) := by rw [hDel]; norm_cast
  have hkp : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hmp : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hnp : (0 : ℝ) < D.R.n := by
    unfold Ranks.n
    exact_mod_cast D.R.ord_pos
  have hxp : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hh0 : (0 : ℝ) < (h0v s ch : ℝ) := by
    have : 0 < ⌈s.x ^ ch⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    unfold h0v
    exact_mod_cast (by omega : 0 < 2 * ⌈s.x ^ ch⌉₊)
  have hDp : (0 : ℝ) < (Delv s cD : ℝ) := by
    rw [← hDelR]; exact_mod_cast D.s.Del_pos
  let L : SizeData₂ D :=
    { sc := s
      aT := aT
      aT_win := fun t => (hwin t).1
      bT := bT
      bT_ge := fun t => (hwin t).2.1
      top_u := fun τ t h hτ => by
        obtain ⟨e1, e2⟩ := htop τ t h hτ
        rw [e1, e2]
        push_cast
        exact ⟨rfl, rfl⟩
      top_b := w1
      supp := ∅
      gain := fun _ _ => 0
      F := fun _ _ => 0
      E := fun _ _ _ => 0
      tau := fun _ => 0
      io := fun _ => 0
      gain_supp := fun _ _ _ => rfl
      F_supp := fun _ _ _ => rfl
      E_supp := fun _ _ _ _ => rfl
      tau_supp := fun _ _ => rfl
      io_supp := fun _ _ => rfl
      gain_g := fun _ _ _ => rfl
      b_le := w2
      untwisted := fun w h j j1 j2 => ⟨hA w h j j1 j2, rfl⟩
      not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
      drop := ∅
      drop_alt := fun _ => Set.notMem_empty _
      F_conj := fun _ _ => rfl
      F_above := fun _ _ _ _ _ => rfl
      j0 := ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
      logFiveDepth_le := Nat.le_ceil _
      weightLength_ge_depth := w11
      logDerivativeAtOne := dlogL D 1
      logDerivative_at_one_eq := rfl
      split_tie := hH.split_tie
      o_tie := hH.o_le.trans hCo
      QS_tie := by
        have h3 := hH.QS_le
        have h4 := mul_le_mul_of_nonneg_right hCo hnp.le
        have h5 : 0 ≤ s.x ^ (s.eps / 100) * D.R.n := by positivity
        show (D.host.QS : ℝ) ≤ 4 * D.R.n * s.x ^ (s.eps / 100)
        nlinarith
      NuLat := fun _ => ⊥
      de2 := (D.host.T2.card : ℝ) / D.R.n
      thickDensity_pos := div_pos (by exact_mod_cast w12) hnp
      thickDensity_le_one := (div_le_one hnp).mpr (by exact_mod_cast w13)
      typeDensity_eq_card_div := rfl
      LaG := G.La C.GK s
      Sc := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ))
      etaSz := (D.R.m : ℝ) * (h0v s ch : ℝ)
      Sc_pos := by positivity
      Sc_eq := by rw [hDelR]
      Cc := C.Cc
      win_thick := w3
      win_top := w4
      win_thin := w5
      cloud_gap := by rw [hCc]; exact w6
      cloud_v := w7
      cloud_u := fun u τ i i1 i2 =>
        middle_between (D.hcW u τ) (by rw [D.hcW_v]; exact w7 τ) i i1 i2
      be_close := w8
      etaSz_pos := by positivity
      TTw := fun _ => Finset.univ
      TTw_full := fun _ _ => rfl
      Ct := C.Ct
      t_win := ⟨w9, by rw [hCt]; exact w10⟩
      CGam := C.CGam
      CGam_pos := by linarith
      Gam_eq := hG
      wPart := fun _ _ _ _ => 1
      wPart_ge := fun _ _ _ _ => le_rfl
      lenMN := fun _ _ => 0 }
  exact ⟨L, rfl, rfl, rfl,
    { ranks := hR
      host := hH
      hc := hHC
      dlog := hdl
      Del_eq := hDel
      eta_eq := rfl
      La_eq := rfl
      bT_le := fun t => (hwin t).2.2
      logFiveDepth_eq := rfl
      Ct_eq := rfl
      Cc_eq := rfl
      CGam_eq := rfl
      secondConstant_eq := hCT2
      words := hW
      etaF_eq := heta }⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

end GlobalTheory.LvT.TwColumn
end
end

