module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLevelSplitsAtOffLevelSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.Mem.R3.LiftBrg.LevSplitAt

set_option maxHeartbeats 4000000

theorem lev_split_at : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (j : Bridge.Gf (Vc X.toD7 i)) (hj : j ∈ (envL X I hX U Xg tr L cV i t).lev.J),
    ∃ j₁ ∈ (envL X I hX U Xg tr L cV i t).lev.J, ∃ j₂ ∈ (envL X I hX U Xg tr L cV i t).lev.J,
      (envL X I hX U Xg tr L cV i t).isLoc x j₁ ∧ j = j₁ * j₂ ∧
      ∀ l, (envL X I hX U Xg tr L cV i t).isLoc x l → Commute j₂ l := by
  intro X px I hX U Xg tr L hI hV hL cV i t x j hj
  classical
  set L' := L.datVt i t with hL'
  set P : Formalism.L2.DIV.Pl X.toD7.host.E := (x.1.1.1 : Formalism.L2.DIV.Pl X.toD7.host.E) with hPdef
  have hoffP : P ∈ Formalism.L2.DIV.offSet ∅ (sgL X I U t) ∅ := x.1.2
  obtain ⟨hPc, hPn, hPq⟩ := hoffP

  obtain ⟨c, hβ⟩ := hL.is.βV i
  rw [one_pow] at hβ

  have hPg : ∀ PP ∈ (flag1L L').Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Pg = L.Pg from rfl, hL.Pg] at hPP
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L L').Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L L').Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    exact Finset.mem_union.2 (Or.inr hPP)
  have hoff : ∀ PP, PP ∈ (flag1L L').Pg ∨ PP ∈ (flag1L L').Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hm : PP ∈ sgL X I U t := hPP.elim (hPg PP) (hQ PP)
    refine ⟨fun e => hPn ?_, fun hc => hPq PP ?_ ?_⟩
    · subst e; simp [hm]
    · simp [hm]
    · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]

  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hPc
  have hpi : IsPrimeIdem P e (e + cA X.toD7 e) := Or.inl ⟨he, rfl⟩
  have h01 := (_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Vc X.toD7 i)).2.2.1 P e _ hpi
  have hff := h01.1
  have hcf := h01.2.1
  have h1 : ((1 : ℕ) : 𝓞 X.toD7.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  obtain ⟨-, -, hsp⟩ := (GlobalTheory.LevSplit.lev_split (Vc X.toD7 i) (L.βV i) (L.ΛV i) 1 (flag1L L') hβ).2 P e _ hpi h1 hoff
  obtain ⟨g, hg, hgj⟩ := GlobalTheory.SplitHeckeAdj.fin_lift (Vc X.toD7 i) j
  have hj' : GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) g ∈ (levEnv (Vc X.toD7 i) (L.βV i) L').J := by rw [hgj]; exact hj
  obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, hk⟩ := hsp g ((GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' hg).1 hj')
  refine ⟨GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₁, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₁.1).2 h₁,
    GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i) k₂, (GlobalTheory.SplitHeckeAdj.mem_J (Vc X.toD7 i) (L.βV i) L' h₂.1).2 h₂, ⟨e, k₁, he, h₁.1, s₁, rfl⟩,
    by rw [← hgj, hk, map_mul], ?_⟩
  intro l hl
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.SplitHeckeAdj.loc_supp (Vc X.toD7 i) hl he
  exact (GlobalTheory.SplitHeckeAdj.commute_compl (Vc X.toD7 i) _ hff hcf ha s₂).symm.map (GlobalTheory.SplitHeckeAdj.fin (Vc X.toD7 i))

end GlobalTheory.Mem.R3.LiftBrg.LevSplitAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelCharacterTypePrimeEqColumnCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.Mem.R3.LevChi

theorem chi_succ_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (w : {w // w ∈ (X.B.primes px).vGs}) (c : (𝓞 X.B.fields.E ⧸ w.1.asIdeal)ˣ),
      L.chi ((i : ℕ) + 1) w.1 c = Units.map X.toD7.what₂.embLL.toMonoidHom (Formalism.L2.Col.chiAt I.Ch w (i : ℕ) c) := by
  intro X px I U L hI hL i w c
  have hw : w.1 ∈ L.Pg := by rw [hL.Pg]; exact w.2
  have hres := hL.is.chi i w.1 hw
  have hmu : L.C.mu0 i = I.C.mu0 i := by rw [hL.C]; rfl
  rw [hmu] at hres
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.B.fields.E ⧸ w.1.asIdeal)
  have hy0 : ((y : 𝓞 X.B.fields.E) : X.B.fields.E) ≠ 0 := by
    intro h
    have h0 : y = 0 := RingOfIntegers.ext h
    apply c.ne_zero
    rw [← hy, h0, map_zero]
  let x : X.B.fields.Eˣ := Units.mk0 _ hy0
  have h1 := hres y x c rfl hy.symm
  have h2 := (hI.ch_tied.mu0 i).atg w x y c rfl hy.symm
  have h3 : (((L.chi ((i : ℕ) + 1) w.1 c)⁻¹ : ℂˣ) : ℂ) = X.B.embLL (((I.Ch.chi i w c)⁻¹ : X.B.fields.Kˣ) : X.B.fields.K) :=
    (congrArg Units.val h1).trans h2
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀] at h3
  have h5 : ((L.chi ((i : ℕ) + 1) w.1 c : ℂˣ) : ℂ) = X.B.embLL ((I.Ch.chi i w c : X.B.fields.Kˣ) : X.B.fields.K) :=
    inv_injective h3
  have e : Formalism.L2.Col.chiAt I.Ch w (i : ℕ) = I.Ch.chi i w := by
    unfold Formalism.L2.Col.chiAt Formalism.L2.Col.extChi
    rw [dite_eq_left (show (i : ℕ) < X.B.R.m from i.2)]
    rfl
  rw [e]
  exact Units.ext h5

end GlobalTheory.Mem.R3.LevChi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdentificationPlaceEqInducedRealPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TiePlace

theorem iota_sigma_mem_range {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (S : HidaSetting p n' W Qq O Kf ι σ j w) (s : ℕ) (y : Qq) :
    ι ((σ ^ s) y) ∈ Set.range (algebraMap O Kf) ↔ y ∈ Set.range (algebraMap W Qq) := by
  haveI := S.frac_alt
  haveI := S.frac_O

  have h1 : ∀ z : Qq, z ∈ Set.range (algebraMap W Qq) → σ z ∈ Set.range (algebraMap W Qq) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t', ht'⟩ := S.frob t
    exact ⟨_, ht'.symm⟩
  have hk : ∀ (k : ℕ) (z : Qq), z ∈ Set.range (algebraMap W Qq) → (σ ^ k) z ∈ Set.range (algebraMap W Qq) := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      rw [pow_succ]
      exact ih _ (h1 z hz)
  have hs : ∀ z : Qq, (σ ^ s) z ∈ Set.range (algebraMap W Qq) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, hk s z⟩
    have hn : 1 ≤ n' := le_trans (by norm_num) S.two_le
    have e : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = z := by
      have em : (σ ^ (s * (n' - 1))) ((σ ^ s) z) = (σ ^ (s * (n' - 1)) * σ ^ s) z := rfl
      rw [em, ← pow_add]
      have : s * (n' - 1) + s = n' * s := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        simp only [Nat.add_sub_cancel_left]
        ring
      rw [this, pow_mul, S.period, one_pow]
      rfl
    rw [← e]
    exact hk _ _ h

  have hj : Function.Injective j := by
    intro a b h
    apply IsFractionRing.injective W Qq
    apply ι.injective
    rw [S.ι_comp, S.ι_comp, h]
  have hnu : ¬ IsUnit (p : O) := by
    letI := j.toAlgebra
    haveI : Module.Finite W O := S.finite
    haveI : FaithfulSMul W O := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    intro h
    exact S.p_unif.not_isUnit ((isUnit_map_iff (algebraMap W O) _).1 (by simpa using h))
  have hι : ∀ z : Qq, ι z ∈ Set.range (algebraMap O Kf) ↔ z ∈ Set.range (algebraMap W Qq) := by
    intro z
    refine ⟨fun h => ?_, ?_⟩
    · by_contra hz
      obtain ⟨o, ho⟩ := h
      have hz0 : z ≠ 0 := fun h0 => hz ⟨0, by rw [h0, map_zero]⟩
      obtain ⟨t, ht⟩ := (ValuationRing.isInteger_or_isInteger W z).resolve_left hz
      have htu : ¬ IsUnit t := by
        rintro ⟨u, rfl⟩
        apply hz
        refine ⟨(u⁻¹ : Wˣ), ?_⟩
        rw [← inv_inv z, ← ht]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      have htm : t ∈ Ideal.span {(p : W)} := by
        rw [← S.p_unif.maximalIdeal_eq]
        exact htu
      obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.1 htm
      have e1 : algebraMap O Kf (o * j (t' * p)) = 1 := by
        rw [map_mul, ho, ← S.ι_comp, ht, ← map_mul, mul_inv_cancel₀ hz0, map_one]
      have e2 : o * j (t' * p) = 1 := by
        apply IsFractionRing.injective O Kf
        rw [e1, map_one]
      apply hnu
      have : IsUnit (j (t' * p)) := IsUnit.of_mul_eq_one o (by rw [mul_comm]; exact e2)
      rw [map_mul, map_natCast] at this
      exact isUnit_of_mul_isUnit_right this
    · rintro ⟨t, rfl⟩
      exact ⟨j t, (S.ι_comp t).symm⟩
  rw [hι, hs]

theorem val_pos_iff {K : Type} [Field K] (val : AddValuation K (WithTop ℤ)) (z : K) :
    (0 : WithTop ℤ) < val z ↔ z = 0 ∨ ¬ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, false_or, AddValuation.map_inv, not_le]
    obtain ⟨n, hn⟩ : ∃ n : ℤ, val z = n := WithTop.ne_top_iff_exists.1 (fun h => hz ((AddValuation.top_iff val).1 h)) |>.imp fun _ h => h.symm
    rw [hn, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    norm_cast
    omega

theorem mem_asIdeal_iff_inv {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (x : R) :
    x ∈ v.asIdeal ↔ x = 0 ∨ (algebraMap K (v.adicCompletion K) (algebraMap R K x))⁻¹ ∉ v.adicCompletionIntegers K := by
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx, false_or, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, not_le]
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
    have h1 : (algebraMap K (v.adicCompletion K) (algebraMap R K x)) = ((algebraMap R K x : K) : v.adicCompletion K) := rfl
    rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h0 : v.valuation K (algebraMap R K x) ≠ 0 := by
      simpa using hx
    rw [one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem inv_int_iff {p : ℕ} {G : GAtP p} (v : Fin G.P.nV) (s : ℕ) {LL : Type} [Field LL]
    (val : AddValuation LL (WithTop ℤ)) (emb : LL →+* G.Kf)
    (hint : ∀ z, (0 : WithTop ℤ) ≤ val z ↔ emb z ∈ Set.range (algebraMap G.O G.Kf)) (z : LL) (y : G.P.Qq v)
    (hk : emb z = G.P.ι v ((G.P.σ v ^ s) y)) :
    y⁻¹ ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ (0 : WithTop ℤ) ≤ val z⁻¹ := by
  rw [hint, map_inv₀, hk, ← map_inv₀, ← map_inv₀]
  exact (iota_sigma_mem_range (G.P.setting v) s y⁻¹).symm

section Comparison₂

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem tie_mem_iff {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) (x : 𝓞 F) :
    x ∈ (t.pl v).1.asIdeal ↔ x = 0 ∨
      ((t.eQ v _ rfl).symm ((t.spl _ (t.pl v).2 (inclE (F := F) ((t.pl v).1.adicCompletion F) (algebraMap F E (x : F)))).1))⁻¹ ∉
        Set.range (algebraMap (G.P.W v) (G.P.Qq v)) := by
  rw [t.spl_F, mem_asIdeal_iff_inv (K := F), t.completion_integers_iff v _ rfl, map_inv₀, RingEquiv.apply_symm_apply]

end Comparison₂

theorem int_map_eq_zero_iff {F E L : Type} [Field F] [Field E] [Field L] (g : F →+* E) (f : E →+* L)
    (x : 𝓞 F) : f (g (x : F)) = 0 ↔ x = 0 := by
  rw [map_eq_zero_iff f f.injective, map_eq_zero_iff g g.injective]
  exact RingOfIntegers.coe_eq_zero_iff


set_option maxHeartbeats 4000000 in
theorem place_of_tie : ∀ (D : D7) (sc : Scale) (Ce : ℝ)
    (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
    (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
    (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w)))
    (x : 𝓞 D.host.F),
    x ∈ (((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) := by
  intro D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hpos := pos_C D sc Ce Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s
    (algebraMap D.host.F D.host.E (x : D.host.F))
  have hsig : sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F)) =
      algebraMap D.host.F D.host.E (x : D.host.F) := AlgHom.commutes _ _
  have key : (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
      (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F))) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v (algebraMap D.host.F D.host.E (x : D.host.F)))) := by
    have e : tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
        (algebraMap D.host.F D.host.E (x : D.host.F)) = Cmp.tEL (recC D sc Ce Lc I ψ hd)
          ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩) (if Even s.val then algebraMap D.host.F D.host.E (x : D.host.F)
            else sigD (recC D sc Ce Lc I ψ hd) (algebraMap D.host.F D.host.E (x : D.host.F))) := by
      by_cases he : Even s.val
      · simp only [he, if_true, ite_true, ↓reduceIte]; rfl
      · simp only [he, if_false, ite_false, ↓reduceIte, hsig]; rfl
    rw [e]
    exact hpos
  refine (tie_mem_iff ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x).trans ?_
  have hz : x = 0 ↔ tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)) = 0 := by
    exact (int_map_eq_zero_iff (algebraMap D.host.F D.host.E) (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)) x).symm
  refine Iff.trans ?_ (val_pos_iff (D.what₂.places.val w) (tauLL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
      (algebraMap D.host.F D.host.E (x : D.host.F)))).symm
  exact or_congr hz (not_congr (inv_int_iff v s.val (D.what₂.places.val w) ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg)
    ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW_int u w hg) _ _ key))

end GlobalTheory.TiePlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SphLoc

section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

theorem fixed_ne_bot_of_mem_iSup {ι : Type} [Finite ι] {σ : Representation ℂ G V} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}
    (hf : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap) (hf0 : f ≠ 0) (hK : ∀ k ∈ K, ρ k f = f) :
    GlobalTheory.PRep.fixed σ K ≠ ⊥ :=
  _root_.GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ T K hf hf0 hK

end Alg

section Val
open ValuativeRel Filter Topology

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push Not at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push Not at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

end Val

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_Umax_of_mem_KO (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i) (x : GAf L n)
    (hx : TrivOutside {s.v} x)
    (hk : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) ∈ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)) :
    x ∈ Umax L n := by
  have key : ∀ y, ValuativeRel.valuation _ (i y) ≤ 1 → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (le_one_of_map i.toRingHom hi hy)
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hk
  refine GlobalTheory.TSetFin.mem_Umax_of_loc s x hx (fun a b => key _ (hk.1 a b)) (fun a b => key _ (by
    have h2 := hk.2 a b
    rw [← map_inv, ← map_inv] at h2
    exact h2))

theorem isSpherical_of_sphAt (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) (hs : π.SphAt s.v) :
    GlobalTheory.SmGL.IsSpherical σ.ρ := by
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  have hI := _root_.GlobalTheory.SplitAdelic.main L n s
  choose lift hlift using fun A => (hI.2.2 A).exists
  have huniq : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (hI.2.2 A).unique ⟨hx, e⟩ (hlift A)
  have hmul : ∀ A B, lift (A * B) = lift A * lift B := fun A B =>
    (huniq _ _ (GlobalTheory.TSetFin.triv_mul (hlift A).1 (hlift B).1) (by rw [map_mul, (hlift A).2, (hlift B).2])).symm
  have htriv1 : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hone : lift 1 = 1 := (huniq _ _ htriv1 (map_one _)).symm
  let e : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hloc : ∀ g, Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (lift (e g))) = g := fun g => by
    rw [(hlift _).2]
    exact Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let ρX : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → π.W) :=
    { toFun := fun g => NG.rt L n (lift (e g))
      map_one' := by
        simp only [map_one, hone]
        ext φ x
        simp [NG.rt]
      map_mul' := fun g h => by
        simp only [map_mul, hmul]
        ext φ x
        simp [NG.rt, mul_assoc] }
  have hiso : f ∈ NG.isoTyp π.ρ π.S := by
    unfold NG.isoTyp
    exact Submodule.mem_sSup_of_mem (show π.S ∈ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} from
      ⟨π.irrS, LinearEquiv.refl ℂ _, fun _ _ _ e => e⟩) hf
  have h1 := _root_.GlobalTheory.SpanLoc.main L n π.toAlgWt π.S π.irrS s σ hσ i hi hic hiso
  rw [iSup_subtype', Submodule.mem_iSup_iff_exists_finset] at h1
  obtain ⟨t, ht⟩ := h1
  rw [iSup_subtype'] at ht
  let Tm : {j // j ∈ t} → σ.ρ.IntertwiningMap ρX := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => by
      have := j.1.2.2 (lift (e g)) (hlift _).1 a
      rw [hloc] at this
      exact this⟩
  refine fixed_ne_bot_of_mem_iSup σ.irr Tm (GlobalTheory.SplitWeil.KO _ (Fin n)) ht hf0 fun k hk => ?_
  show NG.rt L n (lift (e k)) f = f
  exact hfix _ (mem_Umax_of_mem_KO s i hi _ (hlift _).1 (by rw [hloc]; exact hk)) (hlift _).1

end

end GlobalTheory.SphLoc

end

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end

