module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationAdditiveQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLattices
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem glue : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep)), (∀ p, IsLat (A.L p) (Λ p)) → {p | Λ p ≠ Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite → ∃! Γ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Γ ∧ ∀ p, A.lat p Γ = Λ p := by
  intro F E _ _ _ _ _ sig A n Λ hlat hfin
  refine existsUnique_of_exists_of_unique ?_ ?_
  · have happ1 := (_root_.GlobalTheory.HL.StrongApprox.strong_approx_additive A (fun _ => 1)
      (Set.finite_empty.subset fun p hp => hp ⟨1, by simp⟩)).2.1
    have h3 : ∀ p (y : (A.loc p).Ep), ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O :=
      GlobalTheory.T.exists_nat_mul_mem_integers_quadraticCompletion A (fun y hy => by
        obtain ⟨x, hx⟩ := happ1 y hy
        exact ⟨x, fun p => by simpa using hx p⟩)
    obtain ⟨N, hN, hb⟩ := GlobalTheory.T.exists_nat_bound_localLattices_standard_ae A n Λ hfin fun p => GlobalTheory.T.local_lattice_between_scaled_standard_lattices A p n (Λ p) (hlat p) (h3 p)
    let Γ : Submodule (𝓞 E) (Fin n → E) :=
      { carrier := {x | ∀ p, A.bc p x ∈ Λ p}
        add_mem' := by
          intro x y hx hy p
          have : A.bc p (x + y) = A.bc p x + A.bc p y := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).add_mem (hx p) (hy p)
        zero_mem' := by
          intro p
          have : A.bc p (0 : Fin n → E) = 0 := by funext i; simp [Places.bc]
          rw [this]; exact (Λ p).zero_mem
        smul_mem' := by
          intro a x hx p
          have ha : (A.loc p).ιE (a : E) ∈ (A.L p).O := ιE_mem A p _ a.isIntegral_coe
          have : A.bc p (a • x) = (⟨_, ha⟩ : (A.L p).O) • A.bc p x := by
            funext i; simp [Places.bc, Subring.smul_def, Algebra.smul_def]; rfl
          rw [this]; exact (Λ p).smul_mem _ (hx p) }
    have hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p := fun x => Iff.rfl
    have hL : Submodule.IsLattice E Γ := by
      refine GlobalTheory.T.isLattice_of_squeezed_between_nat_multiples n Γ N hN (fun x hx p => ?_) (fun x hx i => ?_)
      · have : A.bc p ((N : E) • x) = (N : (A.loc p).Ep) • A.bc p x := by
          funext i; simp [Places.bc]
        rw [this]
        exact (hb p).1 _ fun i => ιE_mem A p _ (hx i)
      · refine _root_.GlobalTheory.HL.isIntegral_of_forall_mem_O A _ fun p => ?_
        have := (hb p).2 _ (hx p) i
        simpa [Places.bc] using this
    refine ⟨Γ, hL, fun p => le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hx p)
    · haveI := (A.loc p).char0
      refine GlobalTheory.T.localLattice_le_completion_glued_lattice A n Λ Γ N hΓ (fun q => (hb q).1) ?_ p
      have hc : ∀ q, (N : (A.loc q).Fp) ≠ 0 := fun q => by
        haveI := (A.loc q).char0; exact_mod_cast hN
      have happN := (_root_.GlobalTheory.HL.StrongApprox.strong_approx_additive A (fun q => Units.mk0 _ (hc q))
        (by simpa using GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all A N hN)).2.1
      intro y hy
      obtain ⟨x, hx⟩ := happN y hy
      exact ⟨x, fun q => by simpa using hx q⟩
  · have full (Γ : Submodule (𝓞 E) (Fin n → E)) (hΓ : Submodule.IsLattice E Γ)
        (e : ∀ p, A.lat p Γ = Λ p) : Submodule.IsFullLattice E Γ := by
      refine { toIsLattice := hΓ, span_eq_top := ?_ }
      by_contra hspan
      obtain ⟨φ, hφ, hker⟩ := (Submodule.span E (Γ : Set (Fin n → E))).exists_le_ker_of_lt_top
        (lt_top_iff_ne_top.mpr hspan)
      obtain ⟨p⟩ := GlueInt.nonempty_place' (F := F)
      have := GlueInt.nontrivial_Ep A p
      -- A functional annihilating the global span extends by mapping its coefficients.
      let ψ : (Fin n → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
        ∑ i, (A.loc p).ιE (φ (Pi.single i 1)) • LinearMap.proj i
      have hψ (x : Fin n → E) : ψ (A.bc p x) = (A.loc p).ιE (φ x) := by
        have hx : φ x = ∑ i, x i * φ (Pi.single i 1) := by
          have hi (i : Fin n) : (fun j : Fin n => if i = j then (1 : E) else 0) =
              Pi.single i 1 := by
            funext j
            simp [Pi.single_apply, eq_comm]
          simpa only [hi, smul_eq_mul] using LinearMap.pi_apply_eq_sum_univ φ x
        simp only [hx, ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          smul_eq_mul, map_sum, map_mul, mul_comm, Places.bc]
      have htop : Submodule.span (A.loc p).Ep (A.bc p '' (Γ : Set (Fin n → E))) = ⊤ := by
        simpa only [← e p, Places.lat, Submodule.span_span_of_tower] using (hlat p).2
      have hle : Submodule.span (A.loc p).Ep (A.bc p '' (Γ : Set (Fin n → E))) ≤
          LinearMap.ker ψ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        change ψ (A.bc p x) = 0
        rw [hψ, LinearMap.mem_ker.mp (hker (Submodule.subset_span hx)), map_zero]
      rw [htop] at hle
      apply hφ
      apply LinearMap.ext
      intro x
      have hz : A.bc p x ∈ LinearMap.ker ψ := hle Submodule.mem_top
      apply (A.loc p).ιE.injective
      simpa only [LinearMap.mem_ker, hψ, LinearMap.zero_apply, map_zero] using hz
    rintro Γ₁ Γ₂ ⟨h1, e1⟩ ⟨h2, e2⟩
    ext x
    rw [(_root_.GlobalTheory.HL.PlacesRec.lattice_local A n Γ₁ (full Γ₁ h1 e1)).1 x,
      (_root_.GlobalTheory.HL.PlacesRec.lattice_local A n Γ₂ (full Γ₂ h2 e2)).1 x]
    simp only [e1, e2]

end GlobalTheory.HL.Glue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPsiEEqExpTrace
section
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.AddCharProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem main_prime_pow (h2 : Module.finrank F E = 2) {sig : E →ₐ[F] E}
    (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) {l : ℕ} (hl : l.Prime) (y : E)
    (hy : IsIntegral ℤ y) (k : ℕ) :
    (Function.mulSupport fun p => (A p).psiE ((A p).ιE (y / (l : E) ^ k))).Finite ∧
      ∏ᶠ p, (A p).psiE ((A p).ιE (y / (l : E) ^ k)) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E (y / (l : E) ^ k) : ℚ) : ℂ))) :=
  _root_.GlobalTheory.ResidueCharacterDense.prod_psi h2 A hl y hy k

theorem finprod_psiE_eq_exp_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p), ∀ x : E, (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧ ∏ᶠ p, (A p).psiE ((A p).ιE x) = Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by
  intro F E _ _ _ _ _ _ hc sig _ A x
  let P : E → Prop := fun x => (Function.mulSupport fun p => (A p).psiE ((A p).ιE x)).Finite ∧
    ∏ᶠ p, (A p).psiE ((A p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ)))
  have hadd : ∀ u v, P u → P v → P (u + v) := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    have e : (fun p => (A p).psiE ((A p).ιE (u + v))) =
        fun p => (A p).psiE ((A p).ιE u) * (A p).psiE ((A p).ιE v) := by
      funext p
      rw [map_add (f := _), AddChar.map_add_eq_mul]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact (hu.union hv).subset (Function.mulSupport_mul _ _)
    · rw [e, finprod_mul_distrib hu hv, hu', hv', ← Complex.exp_add, map_add (f := _), Rat.cast_add, mul_add]
  have key : ∀ N : ℕ, N ≠ 0 → ∀ y : E, IsIntegral ℤ y → P (y / (N : E)) := by
    intro N
    induction N using Nat.recOnPosPrimePosCoprime with
    | prime_pow l k hl _ =>
      intro _ y hy
      have := main_prime_pow hc.deg2 A hl y hy k
      simpa only [Nat.cast_pow] using this
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _ y hy
      have := main_prime_pow hc.deg2 A Nat.prime_two y hy 0
      simpa only [pow_zero, Nat.cast_one] using this
    | coprime a b ha hb hab iha ihb =>
      intro _ y hy
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
      have ha0 : (a : E) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
      have hb0 : (b : E) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
      have huv' : (u : E) * a + v * b = 1 := by exact_mod_cast huv
      have e : y / ((a * b : ℕ) : E) = (v * y) / a + (u * y) / b := by
        push_cast
        field_simp
        linear_combination (-y) * huv'
      rw [e]
      exact hadd _ _ (iha (by omega) _ ((isIntegral_algebraMap (x := v)).mul hy))
        (ihb (by omega) _ ((isIntegral_algebraMap (x := u)).mul hy))
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hi' : IsIntegral ℤ ((n * n : ℤ) • x) := by
    rw [mul_smul]; exact hi.smul n
  have h := key (n * n).natAbs (by simpa using hn) _ hi'
  have e : ((n * n : ℤ) • x) / (((n * n).natAbs : ℕ) : E) = x := by
    have h1 : (((n * n).natAbs : ℕ) : E) = ((n * n : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg n)]
    have h0 : ((n * n : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hn hn
    rw [h1, zsmul_eq_mul, mul_div_cancel_left₀ _ h0]
  rw [e] at h
  exact h

end GlobalTheory.AddCharProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZero
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameUnimod
open GlobalTheory.HL.Defect GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix

theorem frame_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ u : Fin (2 * (r + 1)) → S.V, S.M d Λ = Submodule.span L.O (Set.range u) ∧ Submodule.span E (Set.range u) = S.ME ∧ (∀ i j, hf L S.Hm (u i) (u j) ∈ L.O) ∧ ∃ P : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (u i) (u j)) * P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha0
  obtain ⟨hSD, hW, hM, -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth0, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hv, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hn : (S.wit d Λ).1 ∈ S.N := hW.2.2.1
  have hn' : (S.wit d Λ).2 ∈ S.N' := hW.2.2.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy x hx
  have hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) := Mof_eq S _ _
  have hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ := fun i =>
    (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1
  have hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hn
    exact spanTo_eq S _ _ s hs h
  have hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'
    exact spanTo_eq S _ _ s hs h
  have hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
      (gens S (S.fr d Λ) (S.fr' d Λ) j)).det =
      algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c) := by
    refine (det_gens S hn hn').trans ?_
    rw [hc]; simp only [map_mul, map_pow, map_neg, map_one]
  have hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0 := by
    simp [hc0, hth0]
  have hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F] := by
    rw [← algebraMap_mem_iff L, ← hdet]
    exact det_mem _ fun i j => hint _ (hg i) _ (hg j)
  obtain ⟨w0, hw0⟩ := hvu _ hc'
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)
  rw [hm, zpow_natCast] at hw0
  have ha : S.a = m := by
    have e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m *
        ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F)) := by
      have e2 : ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((w0 : 𝒪[F]) : F) := by
        simp
      rw [e2, mul_left_comm ((S.ϖ : F) ^ m), ← hw0, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _),
        ← mul_pow, inv_pow]
      field_simp
      simp
    unfold Frames.a Frames.vth
    unfold Frames.th at e1
    rw [hc, e1]
    split_ifs
    · rw [← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]; push_cast; ring
    · rw [one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]; ring
  have hm0 : m = 0 := by omega
  rw [hm0, pow_zero, one_mul] at hw0
  let e : Fin (2 * (r + 1)) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (finCongr (two_mul (r + 1))).trans finSumFinEquiv.symm
  have hrange : Set.range (fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i)) =
      Set.range (gens S (S.fr d Λ) (S.fr' d Λ)) :=
    EquivLike.range_comp (gens S (S.fr d Λ) (S.fr' d Λ)) e
  refine ⟨fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i), ?_, ?_, fun i j => hint _ (hg _) _ (hg _), ?_⟩
  · rw [hrange, hMe]
  · rw [hrange]
    unfold Frames.ME
    rw [← hsp, ← hsp']
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b | b, rfl⟩
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)
      · simp only [gens, Sum.elim_inr]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
        · exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩)
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)
    · have h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) :=
        fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨b, -, rfl⟩
        exact h1 b
      · rintro _ ⟨b, -, rfl⟩
        have h2 : S.fr' d Λ b = S.fr d Λ b +
            algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b) := by
          simp only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]
          abel
        rw [h2]
        exact Submodule.add_mem _ (h1 b)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))
  · set Gm : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E :=
      Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) (e i))
        (gens S (S.fr d Λ) (S.fr' d Λ) (e j)) with hGm
    have hGdet : Gm.det = algebraMap F E ((w0 : 𝒪[F]) : F) := by
      have : Gm = (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
          (gens S (S.fr d Λ) (S.fr' d Λ) j)).submatrix e e := rfl
      rw [this, Matrix.det_submatrix_equiv_self, hdet, ← hw0]
    have hA : ∀ i j, Gm i j ∈ L.O := fun i j => hint _ (hg _) _ (hg _)
    let A : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) L.O := Matrix.of fun i j => ⟨Gm i j, hA i j⟩
    have hAG : A.map L.O.subtype = Gm := rfl
    have hadj : ∀ i j, Gm.adjugate i j ∈ L.O := fun i j => by
      have h4 : A.adjugate.map L.O.subtype = Gm.adjugate := by
        rw [← hAG]; exact RingHom.map_adjugate L.O.subtype A
      rw [← h4]
      exact Subtype.property _
    refine ⟨algebraMap F E (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) • Gm.adjugate, fun i j => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact L.O.mul_mem ((algebraMap_mem_iff L _).2 (w0⁻¹ : (𝒪[F])ˣ).1.2) (hadj i j)
    · rw [Matrix.mul_smul, Matrix.mul_adjugate, hGdet, smul_smul, ← map_mul]
      have h8 : (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((w0 : 𝒪[F]) : F) = 1 := by
        rw [← Subring.coe_mul, Units.inv_mul]; simp
      rw [h8, map_one, one_smul]

end GlobalTheory.HL.FrameUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCoordinateLatticeIsTermTrivialWitnesses
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordGood
open GlobalTheory.HL.Model GlobalTheory.HL.Inhab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem adjugate_int (L : LocE F E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : IsIntM L A) :
    IsIntM L A.adjugate := by
  let B : Matrix (Fin n) (Fin n) L.O := fun i j => ⟨A i j, h i j⟩
  have hB : A = L.O.subtype.mapMatrix B := by ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  intro i j
  exact (B.adjugate i j).2

theorem isSD_coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : Good S) :
    IsSD L S.Hm (coordLat S) := by
  obtain ⟨y, hy, hyd⟩ := h.Hm_unit
  refine isSD_stdLat L S.Hm (y • S.Hm.adjugate) h.Hm_int (fun i j => ?_) ?_
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (adjugate_int L _ h.Hm_int i j)
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hyd, one_smul]

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG
  haveI := nontrivial L
  have hsd := isSD_coordLat S hG
  have hmem : ∀ v : S.V, v ∈ coordLat S ↔ ∀ i, v i ∈ L.O := fun v => mem_stdLat L v
  have h1 : ∀ a, S.f a ∈ coordLat S := fun a => (hmem _).2 (hG.f_int a)
  have h2 : ∀ a, S.f' a ∈ coordLat S := fun a => (hmem _).2 (hG.f'_int a)
  have h3 : ∀ a, S.es a ∈ coordLat S := fun a => (hmem _).2 (hG.es_int a)
  have h4 : ∀ a, S.es' a ∈ coordLat S := fun a => (hmem _).2 (hG.es'_int a)
  have hint : ∀ x ∈ coordLat S, ∀ y ∈ coordLat S, hf L S.Hm x y ∈ L.O :=
    fun x hx y hy => (hsd.2 y).2 hy x hx
  have hZ : IsIntM L S.Zh := fun a b => hint _ (h2 b) _ (h1 a)
  have hU : IsUnit (S.D (Fin.last (r + 1))) := (GlobalTheory.FrameBasic.main L r k S).2.2.2.1
  obtain ⟨-, u, hu, hud⟩ := hG.D_unit _ hU.ne_zero
  have hDet : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  rw [hDet] at hud
  have e1 : S.Zh * (u • S.Zh.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm u, hud, one_smul]
  have e2 : (u • S.Zh.adjugate) * S.Zh = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm u, hud, one_smul]
  generalize hPdef : u • S.Zh.adjugate = P at e1 e2
  have hP : IsIntM L P := fun i j => by
    rw [← hPdef, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hu (adjugate_int L _ hZ i j)
  haveI : IsNoetherianRing L.O := by
    obtain ⟨-, -, -, hpid, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
    infer_instance
  have hfg : (coordLat S).FG := hsd.1.1
  have hh := S.herm.1

  have hc : ∀ a, hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
      if a = Fin.last r then 1 else 0 := fun a => by
    have : hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
        L.cj ((S.Zh * P) a (Fin.last r)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hf_sum_right, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hf_smul_right, map_mul, mul_comm, hf_symm L hh]
      rfl
    rw [this, e1, Matrix.one_apply]
    split_ifs <;> simp

  have hc' : ∀ b, hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
      if b = Fin.last r then 1 else 0 := fun b => by
    have : hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
        (P * S.Zh) (Fin.last r) b := by
      rw [hf_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hf_smul_right, L.cj_cj]
      rfl
    rw [this, e2, Matrix.one_apply]
    simp [eq_comm]
  obtain ⟨A, hA, hA'⟩ := GlobalTheory.HL.FrameLift.core S S.f S.es S.T S.gram S.dual S.iso (coordLat S) hfg
    hsd.2 h1 h3 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun b => hP _ _) h2) hc
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.HL.FrameLift.core S S.f' S.es' S.T' S.gram' S.dual' S.iso' (coordLat S)
    hfg hsd.2 h2 h4 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun a => cj_int L (hP _ _)) h1) hc'
  refine ⟨(A, B, S.graphOf (coordLat S)), hA, hB, one_mem _, one_mem _, ?_, ?_, fun b => ?_, rfl⟩
  · rw [one_smul]; exact hA'
  · rw [one_smul]; exact hB'
  · refine ⟨S.f' b - S.f b, sub_mem (h2 b) (h1 b), ?_⟩
    simp [Frames.th, hG.gg]

end GlobalTheory.HL.CoordGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeMapComapOfLeConjMaximalCmDataStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (P Q : Ideal (𝓞 E)), Q.IsMaximal → P ≤ Q → P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) → P ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Q.comap (algebraMap (𝓞 F) (𝓞 E))) := by
  first | exact @GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj | exact GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj | (intros; apply GlobalTheory.UnramifiedConj.le_map_comap_of_le_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZeroStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  first | exact @GlobalTheory.FrameGram.std_frame_gram | exact GlobalTheory.FrameGram.std_frame_gram | (intros; apply GlobalTheory.FrameGram.std_frame_gram <;> assumption)
end

