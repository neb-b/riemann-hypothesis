module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0680
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0033
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OtherLossSum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviGeneratedCommutingBlockGLStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
open Matrix in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_generated_commuting_blockGL :
    ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ) (d : Set.range b → ℕ)
      (h : ∀ c : Set.range b, (block b c).card = d c),
      ∃ f : ∀ c : Set.range b, GL (Fin (d c)) F →* levi (k := F) b,
        (∀ (c : Set.range b) (g : GL (Fin (d c)) F),
          (f c g : GL (Fin r) F) = (blockHom F b c (h c) g : GL (Fin r) F)) ∧
        (⨆ c, (f c).range) = ⊤ ∧
        ∀ c c' : Set.range b, c ≠ c' → ∀ (x : GL (Fin (d c)) F) (y : GL (Fin (d c')) F),
          Commute (f c x) (f c' y) := by
  classical
  intro F _ r b d h
  have mem_enum (c : Set.range b) (i : Fin r) :
      i ∈ Set.range (blockEnum b c (h c)) ↔ b i = c := by
    have hrange : Set.range (blockEnum b c (h c)) = (block b c : Set (Fin r)) :=
      Finset.range_orderEmbOfFin _ (h c)
    rw [hrange]
    simp [block]
  let f (c : Set.range b) : GL (Fin (d c)) F →* levi (k := F) b :=
    ((blockTri (κ := F) b).subtype.comp (blockHom F b c (h c))).codRestrict _ fun g => by
      refine mem_levi.2 fun i j hij => ?_
      show extendMat (blockEnum b c (h c)) (g : Matrix (Fin (d c)) (Fin (d c)) F) i j = 0
      rw [extendMat_out, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
      simp only [mem_enum]
      omega
  let res (c : Set.range b) : levi (k := F) b →* GL (Fin (d c)) F :=
    leviBlock b (blockEnum b c (h c)) (blockEnum b c (h c)).injective fun i j hij => by
      rw [mem_enum, ← hij, blockEnum_mem b c (h c)]
  have f_apply (c : Set.range b) (g : GL (Fin (d c)) F) :
      ((f c g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
        extendMat (blockEnum b c (h c)) (g : Matrix (Fin (d c)) (Fin (d c)) F) := rfl
  have res_apply (c : Set.range b) (m : levi (k := F) b) (a a' : Fin (d c)) :
      (res c m : Matrix (Fin (d c)) (Fin (d c)) F) a a' =
        ((m : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (blockEnum b c (h c) a)
          (blockEnum b c (h c) a') := rfl
  have res_f (c : Set.range b) (g : GL (Fin (d c)) F) : res c (f c g) = g := by
    refine Units.ext (Matrix.ext fun a a' => ?_)
    rw [res_apply, f_apply, extendMat_in]
  have res_f_ne (c c' : Set.range b) (hc : c' ≠ c) (g : GL (Fin (d c)) F) :
      res c' (f c g) = 1 := by
    refine Units.ext (Matrix.ext fun a a' => ?_)
    rw [res_apply, f_apply, extendMat_out]
    · simp [Matrix.one_apply]
    · left
      rw [mem_enum, blockEnum_mem b c' (h c')]
      exact fun e => hc (Subtype.ext e)
  refine ⟨f, fun _ _ => rfl, ?_, ?_⟩
  · have generated : ∀ s : Finset (Set.range b), ∀ m : levi (k := F) b,
        (∀ c : Set.range b, c ∉ s → res c m = 1) → m ∈ ⨆ c : Set.range b, (f c).range := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro m hm
        have hm_one : m = 1 := by
          refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
          by_cases hij : b i = b j
          · let c : Set.range b := ⟨b i, i, rfl⟩
            obtain ⟨a, ha⟩ := (mem_enum c i).2 rfl
            obtain ⟨a', ha'⟩ := (mem_enum c j).2 hij.symm
            have hentry := res_apply c m a a'
            rw [hm c (Finset.notMem_empty _), ha, ha'] at hentry
            rw [← hentry]
            have heq : i = j ↔ a = a' := by
              rw [← (blockEnum b c (h c)).injective.eq_iff, ha, ha']
            simp [Matrix.one_apply, heq]
          · rw [m.2 i j hij]
            simp [Matrix.one_apply_ne (fun e => hij (congrArg b e))]
        rw [hm_one]
        exact Subgroup.one_mem _
      | insert c s _ ih =>
        intro m hm
        let g := f c (res c m)
        have hg : m = m * g⁻¹ * g := by simp
        rw [hg]
        refine Subgroup.mul_mem _ (ih _ fun c' hc' => ?_) (Subgroup.mem_iSup_of_mem c ⟨_, rfl⟩)
        change res c' (m * (f c (res c m))⁻¹) = 1
        by_cases hcc : c' = c
        · subst c'
          rw [map_mul, map_inv, res_f, mul_inv_cancel]
        · rw [map_mul, map_inv, res_f_ne c c' hcc, inv_one, mul_one]
          exact hm c' (by simp [hcc, hc'])
    let := Fintype.ofFinite (Set.range b)
    exact eq_top_iff.2 fun m _ => generated Finset.univ m fun c hc => absurd (Finset.mem_univ c) hc
  · intro c c' hc x y
    refine Subtype.ext (Units.ext ?_)
    change ((f c x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
        ((f c' y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      ((f c' y : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *
        ((f c x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
    rw [f_apply, f_apply]
    let e := blockEnum b c (h c)
    let e' := blockEnum b c' (h c')
    change extendMat e (x : Matrix (Fin (d c)) (Fin (d c)) F) *
        extendMat e' (y : Matrix (Fin (d c')) (Fin (d c')) F) =
      extendMat e' (y : Matrix (Fin (d c')) (Fin (d c')) F) *
        extendMat e (x : Matrix (Fin (d c)) (Fin (d c)) F)
    have disjoint (a : Fin (d c)) (a' : Fin (d c')) : e a ≠ e' a' := by
      intro he
      apply hc
      apply Subtype.ext
      rw [← blockEnum_mem b c (h c) a, ← blockEnum_mem b c' (h c') a']
      exact congrArg b he
    have hxy : (incl F e)ᵀ * incl F e' = 0 := by
      ext a a'
      simp [incl, Matrix.mul_apply, Matrix.one_apply, disjoint a a']
    have hyx : (incl F e')ᵀ * incl F e = 0 := by
      ext a' a
      simp [incl, Matrix.mul_apply, Matrix.one_apply, (disjoint a a').symm]
    let X := incl F e * ((x : Matrix (Fin (d c)) (Fin (d c)) F) - 1) * (incl F e)ᵀ
    let Y := incl F e' * ((y : Matrix (Fin (d c')) (Fin (d c')) F) - 1) * (incl F e')ᵀ
    have hXY : X * Y = 0 := by
      dsimp [X, Y]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e)ᵀ, hxy]
      simp
    have hYX : Y * X = 0 := by
      dsimp [X, Y]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (incl F e')ᵀ, hyx]
      simp
    change (1 + X) * (1 + Y) = (1 + Y) * (1 + X)
    simp only [add_mul, mul_add, hXY, hYX, one_mul, mul_one]
    abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenSubgroup

theorem exists_open_subgroup : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  intro S G _ Z hZ h1 hmul hinv
  let U : G.left.Opens := ⟨Z, hZ⟩
  let G₀ : Over S := Over.mk (U.ι ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk U.ι rfl
  have hjo : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range j.left = Z := U.range_ι
  have : Mono j := Over.mono_of_mono_left j
  have lift : ∀ (X : Over S) (φ : X ⟶ G), Set.range φ.left ⊆ Z → ∃ ψ : X ⟶ G₀, ψ ≫ j = φ := by
    intro X φ hsub
    have hsub' : Set.range φ.left ⊆ Set.range j.left := hr ▸ hsub
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left φ.left hsub') ?_, ?_⟩
    · rw [← j.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left φ.left hsub')
  have inZ : ∀ x : G₀.left, j.left x ∈ Z := fun x => hr ▸ Set.mem_range_self x
  obtain ⟨e, he⟩ := lift (𝟙_ _) η[G] (by
    rintro _ ⟨s, rfl⟩
    exact h1 s)
  obtain ⟨m, hm⟩ := lift (G₀ ⊗ G₀) ((j ⊗ₘ j) ≫ μ[G]) (by
    rintro _ ⟨w, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    apply hmul
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_fst, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _)
  obtain ⟨i, hi⟩ := lift G₀ (j ≫ ι[G]) (by
    rintro _ ⟨x, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinv _ (inZ x))
  obtain ⟨Gs, hG⟩ := exists_grpObj_of_mono_of_fac j e m i he hm hi
  exact ⟨G₀, Gs, j, hG, hjo, hr⟩

end GlobalTheory.OpenSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmOfDualCharacter
section
namespace GlobalTheory.CharLog

variable {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] {θ : B →+* O}

theorem isUnit_intCast [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) {n : ℤ} (hn : n ≠ 0) :
    IsUnit (n : Q) := by
  have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hna p (Fact.out : p.Prime).ne_one
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
  have hu : IsUnit (n.natAbs : Q) := by
    rw [hnm, Nat.cast_mul, Nat.cast_pow]
    refine (h.unit_p.pow k).mul ?_
    simpa using (h.unit_coprime m hcop).map (algebraMap B Q)
  rcases Int.natAbs_eq n with h' | h'
  · rw [h', Int.cast_natCast]; exact hu
  · rw [h', Int.cast_neg, Int.cast_natCast]; exact hu.neg

noncomputable def ratAlgebra [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) : Algebra ℚ Q :=
  (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom Q)
    fun y => by simpa using isUnit_intCast h (nonZeroDivisors.ne_zero y.2)).toAlgebra

end GlobalTheory.CharLog

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem GlobalTheory.CharLog.exists_log_char_period : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ χ
  letI : Algebra ℚ F.Q := GlobalTheory.CharLog.ratAlgebra F.frame
  obtain ⟨u, hu0, hu⟩ := _root_.GlobalTheory.QLog.exists_charSeries p O G d c χ
  have hmul := GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter p O G d c χ u hu
  choose g0 hg0 using fun α => F.frame.surj (coeff α u)
  let g : MvPowerSeries (Fin d) F.B := fun α => if α = 0 then 1 else g0 α
  have hg : map F.θ g = u := by
    ext α
    rw [coeff_map]
    by_cases h : α = 0
    · subst h
      change F.θ (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = _
      rw [if_pos rfl, map_one, coeff_zero_eq_constantCoeff_apply, hu0]
    · change F.θ (if α = 0 then 1 else g0 α) = _
      rw [if_neg h, hg0]
  have hg1 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    change (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = 1
    rw [if_pos rfl]
  have hlin : ∀ i, lin (formalLog (map (algebraMap F.B F.Q) g)) i =
      algebraMap F.B F.Q (coeff (Finsupp.single i 1) g) := fun i => by
    rw [_root_.GlobalTheory.FormalCalc.lin_formalLog F.Q d _ (by rw [constantCoeff_map, hg1, map_one]) i, lin, coeff_map]
  have hcob := _root_.GlobalTheory.CobLog.cob1_formalLog_mem_ker p F.B O F.Q F.θ F.frame d μ' hlift.const g hg1 (by
    rw [hg]; convert hmul using 2; funext i; exact hμ i)
  refine ⟨formalLog (map (algebraMap F.B F.Q) g), fun i => coeff (Finsupp.single i 1) g,
    ⟨constantCoeff_formalLog (by rw [constantCoeff_map, hg1, map_one]),
      fun i => ⟨_, Submodule.mem_top, hlin i⟩,
      fun α => by obtain ⟨b, -, hb⟩ := hcob α; exact ⟨b, Submodule.mem_top, hb⟩⟩,
    hcob, _root_.GlobalTheory.QLog.in_frob_formalLog_sub_smul p F.B O F.Q F.θ F.frame F.σ F.s F.s_alg F.σ_pow d g hg1, hlin, ?_, ?_⟩
  · rw [GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit p O G d c χ u hu0 hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hg, lin, coeff_map]
  · exact _root_.GlobalTheory.CharPeriod.hasPeriod_formalLog_char p C v O hv ε hε F G d c χ g hg1 (by rw [hg]; exact hu)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceZeroIsTay
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

namespace GlobalTheory.AnPer.SliceZero

theorem prod_sumElim_zero {I : Type} {g : ℕ} {R : Type} [CommRing R] (N : ℕ) (t : I → R)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (s : Fin (N + 1) → I ⊕ Fin g) :
    ∏ a, (Sum.elim t (0 : Fin g → R)) (s a) = 0 := by
  by_cases h : ∀ a, ∃ i, s a = Sum.inl i
  · choose f hf using h
    rw [Finset.prod_congr rfl fun a _ ↦ by rw [hf a]]
    simpa using ht f
  · push_neg at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ : ∃ b, s a = Sum.inr b := by
      rcases hs : s a with i | b
      · exact absurd hs (ha i)
      · exact ⟨b, rfl⟩
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hb]; rfl)

end GlobalTheory.AnPer.SliceZero


open GlobalTheory.AnPer.SliceZero in
theorem GlobalTheory.AnPer.exists_sliceZero_isTay : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∃ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ := by
  intro I _ _ g R _ _ N t ht W W₀ hW
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AnPer.exists_sliceTaylor_algHom N (Sum.elim t (0 : Fin g → R))
    (prod_sumElim_zero N t ht) (E := Tot Empty g) W W₀ Prod.snd
    (fun p _ ↦ analyticAt_snd) hW
  refine ⟨ρ.toRingHom, fun h p hp ↦ ?_⟩
  refine (hρ h p hp).trans ?_
  have hh : AnalyticAt ℂ h.fn (0, p.2 + (fun _ : I → ℂ ↦ (0 : Fin g → ℂ)) 0) := by
    rw [add_zero]; exact h.analytic _ (hW p hp)
  have hs := taylor_shear N t ht h.fn (fun _ ↦ (0 : Fin g → ℂ)) p.2 analyticAt_const hh
  simp only [add_zero, Pi.zero_apply, taylor_const_fun, map_zero, sub_zero] at hs
  rw [hs]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePeriodEqFamilyPeriodValue
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_fibre_eq_value : PFix := by
  intro I _ g Λ _ F B _ 𝒜 _ h𝒜 σ e z hz y hy A _ hA φ m L u hE τ hτ P hP c per hper l
  let u' : Unif (⟨(fibFam u).V, (fibFam u).τ.comp τ, fun l ↦ (fibFam u).hol (τ l)⟩ : Fam Empty g Λ)
      (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) :=
    { E := (fibUnif u).E
      w := (fibUnif u).w
      per := fun l p hp ↦ (fibUnif u).per (τ l) p hp
      hol := (fibUnif u).hol }
  have h1 := _root_.GlobalTheory.AnPer.Reindex.isPeriod_comp (fibUnif u) τ u' rfl _ _ (hP (m.pull c))
  have h2 := GlobalTheory.AnPer.isPeriod_pull1_eq_comap u' e (GlobalTheory.abelianScheme_left_isSeparated_of_affine A hA)
    (GlobalTheory.abelianScheme_left_isSeparated_of_affine 𝒜 h𝒜) (fun _ ↦ z) analyticOnNhd_const (fun _ _ ↦ hz)
    LinearMap.id (AddMonoidHom.id Λ) (fun l _ _ ↦ (hτ l).symm) y φ m.isMor
    (fun x ↦ Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Hol.fn_comap _ _ _ _ hp, hy])
    (fun p _ ↦ (hE p.2).symm) c.1 per _ hper h1 l
  have hp : (0 : Empty → ℂ) ∈ (fibFam u).V := trivial
  have h3 := congrArg (fun f ↦ Hol.fn f 0) h2
  simp only [Hol.fn_comap _ _ _ _ hp] at h3
  exact (Hol.fn_algebraMap _ hp).symm.trans h3

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoordinatesSpanFiniteDimensional
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

theorem fockCoordinates_span_finiteDimensional (n : ℕ) (ε : Fin n → Bool) (M : Type)
    [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))) (hZ : FiniteDimensional ℂ Z)
    (hK : IsKStableSub ε (diagE ε (eT E) cpT cmT) Z) :
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z) := by
  have hle : coordSpan Z ≤ ⨆ s : Finset (Fin (n * n)), Z.map (tcoef (M := M) ((fockBasis n).coord s)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨s, y, hy, rfl⟩
    exact (le_iSup (fun s : Finset (Fin (n * n)) => Z.map (tcoef (M := M) ((fockBasis n).coord s))) s)
      (Submodule.mem_map_of_mem hy)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  intro a b hab v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, y, hy, rfl⟩ := hx
    let X := Matrix.single a b (1 : ℂ)
    have e := tco_actDiag (ε := ε) E X y s
    simp only [X, TRGap.actM_single'] at e
    show E a b (tcoef ((fockBasis n).coord s) y) ∈ coordSpan Z
    rw [eq_sub_of_add_eq e.symm, tcoef_eq_sum ((fockBasis n).coord s ∘ₗ sgX ε X) y]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, _, hK a b hab y hy, rfl⟩) ?_
    refine Submodule.sum_mem _ fun s' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s', y, hy, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.GramChartNear

open scoped Matrix ComplexConjugate

theorem gw_sub_jd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  intro E _ _ _ r X w τ a b hrw
  set L : Matrix (Fin r) (Fin r) ℂ := mat (nmat X w) τ - 1 with hLdef
  have hL : ∀ i j, ‖L i j‖ ≤ ‖w‖ := fun i j => PoinPf.nmat_entry X w τ i j
  have hs : ∀ c : Fin r, ‖((sgn X.p0 (c : ℕ) : ℝ) : ℂ)‖ = 1 := fun c => by
    rw [Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  have h1 : mat (nmat X w) τ = 1 + L := by rw [hLdef]; abel
  have key : PoinPf.Gw X w τ - PoinPf.Jd X =
      Lᵀ * PoinPf.Jd X + PoinPf.Jd X * L.map (starRingEnd ℂ) + Lᵀ * PoinPf.Jd X * L.map (starRingEnd ℂ) := by
    rw [PoinPf.Gw, h1, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.map_add _ (map_add (starRingEnd ℂ)), Matrix.map_one _ (map_zero _) (map_one _)]
    noncomm_ring
  rw [← Matrix.sub_apply, key, Matrix.add_apply, Matrix.add_apply, PoinPf.Jd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  have t1 : ‖L b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, mul_one]; exact hL b a
  have t2 : ‖((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L a b)‖ ≤ ‖w‖ := by
    rw [norm_mul, hs, one_mul, Complex.norm_conj]; exact hL a b
  have t3 : ‖∑ c, L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ ≤ ‖w‖ := by
    calc _ ≤ ∑ c : Fin r, ‖L c a * ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (L c b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c : Fin r, ‖w‖ * ‖w‖ := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, hs, mul_one, Complex.norm_conj]
          exact mul_le_mul (hL c a) (hL c b) (norm_nonneg _) (norm_nonneg _)
      _ = ‖w‖ * ((r : ℝ) * ‖w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hrw (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  calc _ ≤ _ := norm_add₃_le
    _ ≤ ‖w‖ + ‖w‖ + ‖w‖ := add_le_add (add_le_add t1 t2) t3
    _ = 3 * ‖w‖ := by ring

end GlobalTheory.GramChartNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertLossPrimeSum
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.OtherLoss

theorem inertLoss_primeSum : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (G.IsResidueClassZero (Fm.D x i) p ∨ G.IsSg (Fm.D x i) p) ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n ∧ ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm _ _
  refine ⟨848, 0, by norm_num, fun x _ hx i j hj P hP => ?_⟩
  have h := sum_eatI (K := Fm.GK) (c := Fm.cX.err) (Fm.sizes x hx i) Fm.fixed.2.1 Fm.fixed.2.2.1 Fm.fixed.2.2.2.2.1 hj P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2.1⟩)
  calc _ = 2 * ∑ p ∈ P, |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| * Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := by linarith

end GlobalTheory.OtherLoss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
section
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.ZalgCpt

theorem zalg_comm_cptRep : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)),
    z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  intro E _ _ _ a k z hz
  have hle : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.cptRep E a k} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u (Unitary.toUnits k)).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (hle hz) _ rfl).symm

end GlobalTheory.ZalgCpt
end

