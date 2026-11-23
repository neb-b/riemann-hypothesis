module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdB
section
noncomputable section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ChiZero

open GlobalTheory.Mem.Col2.MemChart

theorem redAt_eq_one_of_congAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n D : ℕ} (hD : 1 ≤ D)
    (P : Pl E) (w : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (h : GlobalTheory.TwU.CongAt P D w.1) : redAt 1 P w = 1 := by
  obtain ⟨_, y, rfl⟩ := w
  have e : redAt 1 P ⟨frGL 1 y, ⟨y, rfl⟩⟩ = bc (resS F P) y := by
    show bc (resS F P) (pullFr 1 ⟨frGL 1 y, ⟨y, rfl⟩⟩) = _
    rw [pullFr_frGL]
  rw [e]
  have e1 : frGL 1 y = intGL F E n y := by simp [frGL]
  apply Units.ext
  ext a b
  obtain ⟨s, hs, hm⟩ := h a b
  have hq : ((Formalism.L2.Col.qOf P : ℕ) : E) ≠ 0 := by
    have : Formalism.L2.Col.qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hqm : Ideal.Quotient.mk P.asIdeal ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  have key : oToS F E s * ((y.1 - 1) a b) = oToS F E ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ^ D * ⟨_, hm⟩ := by
    apply Subtype.ext
    have c1 : ∀ r : 𝓞 E, ((oToS F E r : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E r) := fun _ => rfl
    have c2 : (((y.1 - 1) a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((frGL 1 y).1 - 1) a b := by
      rw [e1, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [Subring.coe_mul, Subring.coe_mul, SubmonoidClass.coe_pow, c1, c1, c2, ← map_pow, map_natCast]
    show _ = _ * (_ * (_ * _))
    rw [mul_left_comm, ← mul_assoc (iA F E (_ ^ D)), ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one, one_mul]
  have k2 := congrArg (resS F P) key
  rw [map_mul, map_mul, map_pow, resS_oToS, resS_oToS, hqm, zero_pow (by omega), zero_mul] at k2
  haveI := P.isPrime
  have k3 := (mul_eq_zero.1 k2).resolve_left (fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at k3
  show resS F P (y.1 a b) = (1 : Matrix (Fin n) (Fin n) (kP P)) a b
  rw [k3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem dia_of_base (hPr : (B.primes X).Ok) (u : B.Word) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))} {g k : GA B n}
    (k1 : ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) k = 1)
    (k3 : ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    {p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs Q} (h : PtOf (g * k) p) :
    g ∈ UAd B.sp.cm n ∧ (decoOf ((B.primes X).vT u) (B.primes X).vGs g).dia (diaT (Pr := B.primes X) u) = p.deco := by
  refine GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul _ _ B.sp.cm n _ _ Q g _ p _ h k1 k2 fun P r j hr => ?_
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
    have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
      (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact @Ne.isUnit (Res P.1) _ _ h0
  have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
      Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
    unfold diaT
    rw [dite_eq_left hu]
    rfl
  rw [e]
  exact k3 P r j hr

abbrev levelZeroSubgroupOfWord (u : B.Word) : Subgroup (GA B (B.R.N 0)) :=
  levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp

abbrev typ0 (u : B.Word) : levelZeroSubgroupOfWord I u →* ℂˣ :=
  levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)


set_option maxHeartbeats 1000000 in
theorem stepZeroChartLevel_mem_columnLevel_of_stdBase (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a 0).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N 0))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a 0).Cl → GA B (B.R.N 0)} {st : ∀ c, (I.stp u a 0).Stab c → GL (Fin (B.R.N 0)) B.host.E}
    {k : Ch → GA B (B.R.N 0)} (hR : I.Reads u a 0 chOf Lb U chi y st k) (c : (I.stp u a 0).Cl)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) (k (chOf c)) = 1)
    (x : U (chOf c)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (hq : PtOf (y c * x.1 * k (chOf c)) q) :
    ∃ hx : x.1 ∈ levelZeroSubgroupOfWord I u, chi (chOf c) x = typ0 I u ⟨x.1, hx⟩ := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  obtain ⟨κ, h1, h2, -⟩ := (hR.lev c x.1 q hq).1 x.2
  subst h2
  have hg := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) (hR.pt c)
  have hx := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) hq
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)
  have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := hΛ c.1 ▸ κ.2.1.2
  have hxU : x.1 ∈ levelZeroSubgroupOfWord I u := (mem_levU _ _ _ _ _).2 ⟨hJ, by rw [hr]; exact inv_mem hm⟩
  refine ⟨hxU, Units.ext ((hR.chr c x κ h1 hq).trans (Eq.symm ?_))⟩
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩ = (⟨κ.2.1.1, hm⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((Chart0.lvG I a c.1).chr κ.2.1 * (Chart0.lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl

theorem stepZeroColumnLevelType_eq_of_congruent_typePrimes (u : B.Word) (x x' : levelZeroSubgroupOfWord I u)
    (h : ∀ w ∈ (B.primes X).vGs, ∃ D, 1 ≤ D ∧ GlobalTheory.TwU.CongAt (F := B.host.F) (E := B.host.E) w D (x.1⁻¹ * x'.1)) :
    typ0 I u x = typ0 I u x' := by
  have e : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x') = 1 := by
    apply Subtype.ext
    funext w
    obtain ⟨D, hD, hc⟩ := h w.1 w.2
    exact redAt_eq_one_of_congAt hD w.1 ⟨(x⁻¹ * x').1, congruence_subgroup_le_stabilizer _ _ _ (unipotentLevel_le_mirabolicLevel _ _ _ _ _ (x⁻¹ * x').2)⟩ hc
  have e2 : typ0 I u (x⁻¹ * x') = 1 := by
    show (((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x')))⁻¹ = 1
    rw [e, map_one, inv_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at e2
  exact e2

end GlobalTheory.Fam.ChiZero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam
open GlobalTheory.Fam.ChiZero GlobalTheory.Mem.Col2.MemChart


set_option maxHeartbeats 4000000 in
theorem chi_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ x x' hxx
  have hPr := l.pr
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨c, rfl⟩ := hA.chOf_onto 0 (Nat.zero_le _) β
  have hR := hA.reads 0 (Nat.zero_le _)
  obtain ⟨n, hn, hfin⟩ := hA.fin 0 (Nat.zero_le _) (A.chOf 0 c)
  obtain ⟨x₁, e₁, ⟨q, hq⟩, hcg⟩ := GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt I hI hP l Z u a 0 (Nat.zero_le _) (A.bad 0) (Ch 0) (A.chOf 0)
    (A.K 0 (Nat.zero_le _)) (A.kb 0) hR c ⟨n, hn, fun κ _ => hfin κ⟩ x
  obtain ⟨hx₁, f₁⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u a hR c (fun w hw => by
    rw [hβ]
    exact (kStd_spec hPr u _).2.1 _ fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩) x₁ q hq
  obtain ⟨k, hR'⟩ := (hC u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨c', -⟩ := hR'.onto ()
  have hg1 : gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  let yc : TC.GA B (B.R.N 0) := (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').1
  let xg : TC.GA B (B.R.N 0) := x'.1
  have hxg : xg ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).to0.cls0.lev.U_eq x'.1).1 x'.2).1
  have hyc : yc ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').2
  obtain ⟨p0, hp0, -⟩ := hR'.k_std ()
  have hk : k () ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.uni
  obtain ⟨q', hq'⟩ : ∃ q' : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u 0, TC.PtOf (yc * xg * k ()) q' :=
    GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem B.sp.cm I.twistPrimes_reference_tuple_eq_empty (mul_mem (mul_mem hyc hxg) hk)
  obtain ⟨hx', f'⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u I.mu0 hR' c' (fun w hw =>
    hR'.k_off () _ (fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩)
      (fun ⟨P, hP, _⟩ => by rw [I.twistPrimes_reference_tuple_eq_empty] at hP; exact Finset.notMem_empty _ hP) (Or.inl rfl)) x' q' hq'
  refine e₁.symm.trans (f₁.trans (Eq.trans (Eq.symm ?_) f'.symm))
  refine stepZeroColumnLevelType_eq_of_congruent_typePrimes I u _ _ fun w hw => ?_
  have hw' : w ∈ GlobalTheory.Mem.Col2.AdT.SBof I a := Finset.mem_union_left _ hw
  refine ⟨(I.cst a).D ⟨w, hw'⟩, (hI.idx_ok a).cst_ok.D_pos _, ?_⟩
  have h1 := hcg ⟨w, hw'⟩
  rw [(GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a (B.R.N 0) 0 ⟨w, hw'⟩ x.1).1, hxx] at h1
  exact h1

end GlobalTheory.Fam
end

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedTranslatesCombinationCommutesSchrodinge
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PlaceModelComb

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem mxAt_of_idemAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) {Q : GlobalTheory.FinPl.Pl D → Prop}
    (hQ : Q ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) {m n : ℕ} {w : Mx D m n} (hw : IsHalf (es + cA D es) w) : GlobalTheory.FinPl.MxAt Q w := by
  obtain ⟨v, ε, hε, hsum⟩ := h.1.2.2
  obtain ⟨q, hqe, -⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D v es ε h.1 hε hsum
  have hv : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under q (hqe ▸ h)
  exact GlobalTheory.LevPin.mxAt_of_half q (hv ▸ hQ) w (hqe ▸ hw)

theorem mxAt_of_idemSum {e : AE D} {Pg : Finset (Pl D.host.E)} (hs : IsIdemSum e Pg) {m n : ℕ} {x : Mx D m n}
    (hx : IsHalf e x ∨ IsHalf (cA D e) x) :
    GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hs
  intro i j
  rcases hx with hx | hx
  · rw [← hx i j, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (es PP • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h1, ← mul_assoc, mul_comm (cA D (es PP)), h2,
        zero_mul, add_zero]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this
  · rw [← hx i j, map_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun PP hPP => ?_
    have hw : IsHalf (es PP + cA D (es PP)) (cA D (es PP) • x) := fun a b => by
      obtain ⟨h1, h2, -⟩ := (hes PP hPP).1
      rw [Matrix.smul_apply, smul_eq_mul, add_mul, ← mul_assoc, h2, zero_mul, zero_add, ← mul_assoc, ← map_mul, h1]
    have := mxAt_of_idemAt (Q := fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (hes PP hPP) ⟨PP, hPP, rfl⟩ hw i j
    rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (Pg : Finset (Pl D.host.E)) (P' : GlobalTheory.FinPl.Pl D → Prop), IsIdemSum e Pg → (∀ PP ∈ Pg, ¬ P' ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) → ∀ (d : WO S T →₀ ℂ), GlobalTheory.FinPl.CombAt P' d → ∀ (f₁ : WO S T → ℂ) (T₁ T₂ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₁ T₁ → (∀ Φ, T₂ Φ = comb ψ S T d (T₁ Φ)) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (comb ψ S T d f₁) T₂ := by
  intro D ψ hψ S T Λ e Pg P' hs hd d hdc f₁ T₁ T₂ hT₁ hT₂
  have hd' : ∀ p, (∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → ¬ P' p := by
    rintro p ⟨PP, hPP, rfl⟩
    exact hd PP hPP
  have hcomm : ∀ x : WO S T, GlobalTheory.FinPl.MxAt (fun p => ∃ PP ∈ Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) x → ∀ f,
      heisO ψ S T x (comb ψ S T d f) = comb ψ S T d (heisO ψ S T x f) := by
    intro x hx f
    have h := (GlobalTheory.DisjComb.main D ψ hψ S T _ P' hd').1 (Finsupp.single x 1) d (fun u hu => by
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
      subst hu
      exact hx) hdc f
    simpa only [GlobalTheory.DisjComb.comb_single] using h
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [hT₂, hT₁.trans Φ hΦ x hx, ← hcomm x (mxAt_of_idemSum hs (Or.inl hx)), hT₂]
  · rw [hT₂, hT₁.modul Φ hΦ y hy, ← hcomm y (mxAt_of_idemSum hs (Or.inr hy)), hT₂]
  · rw [hT₂, hT₁.vac]

end GlobalTheory.PlaceModelComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsRealDataSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.RealTrue

theorem ontoUni_reindex {ι K : Type} [Group K] [TopologicalSpace K] {a b : ℕ} (h : a = b)
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) :
    OntoUni fun k τ => (r k τ).reindex (finCongr h) (finCongr h) := by
  subst h; simpa using hr

theorem ontoUni_one {ι K : Type} [Group K] [TopologicalSpace K] {a : ℕ}
    {r : K → ι → Matrix (Fin a) (Fin a) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have hm := hr.mul 1 1 τ
  rw [mul_one] at hm
  have hu := Matrix.mem_unitaryGroup_iff'.1 (hr.uni 1 τ)
  calc r 1 τ = (star (r 1 τ) * r 1 τ) * r 1 τ := by rw [hu, Matrix.one_mul]
    _ = star (r 1 τ) * (r 1 τ * r 1 τ) := Matrix.mul_assoc _ _ _
    _ = 1 := by rw [← hm, hu]

theorem inN_one {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    inN θ V (fun _ => 1) hn g τ = infM θ V hn g τ := by
  simp [inN, GlobalTheory.SeeSaw.inB, infM]

theorem valC_transport {ι : Type} [Fintype ι] {n : ℕ} {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (h : G = G')
    (lam : ι → DomWeight n) (f : Formalism.L2.Forms.Frames G → ℂ) (hf : f ∈ ValC G lam) :
    (fun z : Formalism.L2.Forms.Frames G' => f ⟨z.1, z.2⟩) ∈ ValC G' lam := by
  subst h; exact hf

end GlobalTheory.RealTrue


open GlobalTheory.RealTrue in
theorem GlobalTheory.AdForm.realOf_is : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (realOf u R g s J).Is := by
  intro B X I hOk hPins l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hJ hJO hEmb
  have hstd := _root_.GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hOk hPins l Z R.ψ R.θ hX.std hX.inf
  have hm2 : 2 ≤ B.R.m := B.R.two_le_m
  have hgX : ∀ i, i ≤ B.R.m → ((I.rec7 l Z).sp.X i).gram = 1 := by
    intro i hi
    rcases Nat.lt_or_ge i B.R.m with h | h
    · exact (hstd.1 i h).gS
    · obtain rfl : i = B.R.m := le_antisymm hi h
      have := (hstd.1 (B.R.m - 1) (by omega)).gT
      rwa [show B.R.m - 1 + 1 = B.R.m by omega] at this
  have hrk : ∀ i, i < B.R.m → 0 < B.R.N i ∧ B.R.N i ≤ B.R.N (i + 1) := by
    intro i hi
    have h := (hstd.1 i hi).rk
    rw [rankN (I.rec7 l Z) i hi.le, rankN (I.rec7 l Z) (i + 1) hi] at h
    exact ⟨h.1, h.2.1.le⟩
  have huni : ∀ i (hi : i ≤ B.R.m), OntoUni fun k : GinfC ((I.rec7 l Z).sp.X i) => (realOf u R g s J).r i hi k.1 := by
    intro i hi
    have hB := (hX.xs i hi).2.1
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ ((I.rec7 l Z).sp.X i) (g.x i).B hX.inf (fun τ => by
      rw [hB]; simp [gramAt, hgX i hi])
    exact ontoUni_reindex (rankN (I.rec7 l Z) i hi) this
  have huniT : OntoUni fun k : GinfC (I.rec7 l Z).sp.X' => (realOf u R g s J).rT k.1 := by
    have := GlobalTheory.SeeSaw.ontoUni_inB (I.rec7 l Z) R.θ (I.rec7 l Z).sp.X' (fun _ => 1) hX.inf (fun τ => by
      simp [gramAt, hstd.2.1])
    exact ontoUni_reindex (rankP (I.rec7 l Z)) this
  have hrT : ∀ k, (realOf u R g s J).rT k = infM R.θ _ (rankP (I.rec7 l Z)) k := fun k => funext fun τ => inN_one _ _ _ _ _
  have hone : ∀ τ, infM R.θ _ (rankP (I.rec7 l Z)) 1 τ = 1 := by
    intro τ
    have := ontoUni_one huniT τ
    rw [← hrT]; exact this
  have htr1 : ∀ z : FrN (I.rec7 l Z) (B.R.N B.R.m - 1), IsTr (infM R.θ _ (rankP (I.rec7 l Z)) 1) z z := by
    intro z τ; rw [hone, Matrix.one_mul]
  have hJ1 : ∀ v, J v 1 = fun z => j v ⟨z.1, z.2⟩ := fun v => funext fun z => hJO v 1 (Subgroup.one_mem _) z z (htr1 z)
  have hG : gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z)) = fun _ => 1 := by
    funext τ; simp [gramC, gramP, hstd.2.1]
  refine ⟨huni, ?_, hrk, ?_, ?_, ?_, ?_⟩
  · exact huniT
  · intro i τ
    simp only [realOf]
    split_ifs with h
    · exact one_ne_zero
    · exact div_ne_zero h (hstd.2.2.2.1 τ)
  · intro i hi τ
    obtain ⟨Ch, _, A, hA, -⟩ := _root_.GlobalTheory.AdForm.exists_twDat I hOk hPins l Z u I.mu0
    obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_charExponent_infinity_kernel_shift I hOk hPins l Z u I.mu0 Ch A hA i hi
    exact Int.toNat_of_nonneg (he τ).2.2
  · intro v
    refine ⟨?_, fun k hk z z' hz => ?_⟩
    · show J v 1 ∈ ValC _ (sgT (D := I.rec7 l Z) u)
      rw [hJ1 v]
      have hm : j v ∈ ValC (gramC (gramP (I.rec7 l Z)) (Formalism.L2.Forms.embT (I.rec7 l Z))) (sgT (D := I.rec7 l Z) u) := by
        rw [← hJ.range]; exact LinearMap.mem_range_self j v
      exact valC_transport hG _ _ hm
    · rw [hrT] at hz
      show J v k z' = J v 1 z
      rw [hJO v k hk z z' hz, hJO v 1 (Subgroup.one_mem _) z z (htr1 z)]
  · intro n hn
    subst hn
    have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := by
      have := hrk (B.R.m - 1) (by omega)
      rw [show B.R.m - 1 + 1 = B.R.m by omega] at this
      omega
    obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common I hOk hPins l Z u hN
    refine ⟨hN, h1, h2, h3, ?_⟩
    intro k hk τ
    have hb := GlobalTheory.T.lastGroup_embedding_real_components_block_form I hOk hPins l Z u R.θ hX.inf _ hN hEmb k τ
    have hB := (hX.xs B.R.m le_rfl).2.1
    show GlobalTheory.BranchFormula.IsBlock hN (inN R.θ _ (g.x B.R.m).B (rankN (I.rec7 l Z) B.R.m le_rfl) ((g.oT B.R.m rfl).emb (k, 1)) τ) (inN R.θ _ (fun _ => 1) (rankP (I.rec7 l Z)) k τ) 1
    rw [hB]
    first
      | simpa only [inN_one] using hb
      | simpa [inN, GlobalTheory.SeeSaw.inB, infM] using hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainDescent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.VacTheta

theorem isFinComb_of_combAt {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} {c : WO S T →₀ ℂ}
    (h : GlobalTheory.FinPl.CombAt P c) : IsFinComb c := by
  intro u hu
  ext i j
  have := (Ideal.mem_inf.1 (h u hu i j)).1
  simpa using this

end GlobalTheory.Fam.VacTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twVec' : TwVec' := by
  intro B X I hOk hPins l Z u a Ch A hA ψ θ x vac c₀ hX k _ _ _ _ ι p β Q hStd J hPl j hj α γ cT hReps e he
  have hjm : j ≤ B.R.m := Nat.le_of_succ_le hj
  have hL0 : ∀ z, z ∈ (x j).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs j hjm).2.2
  have hL1 : ∀ z, z ∈ (x (j + 1)).L ↔ z ∈ intVec (I.rec7 l Z) _ := (hX.xs (j + 1) hj).2.2
  have hvac := hX.vc j (by omega)
  have hS0 : ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL0 z
  have hS1 : ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) = intVec (I.rec7 l Z) _ := by ext z; exact hL1 z
  have hV : Vac ψ _ _ (x j).L (x (j + 1)).L (fun v => ∃ i, v = (p i).v) (vac j) := by
    refine ⟨hvac.2.theta, ?_⟩
    have hle : latO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ((x j).L : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) ((x (j + 1)).L : Set (Fin ((I.rec7 l Z).sp.X (j + 1)).rank → (I.rec7 l Z).host.E)) (fun v => ∃ i, v = (p i).v) ≤ stdHom _ _ := by
      rw [hS0, hS1]
      apply AddSubgroup.closure_mono
      rintro w ⟨a, ha, -, rest⟩
      exact ⟨a, ha, fun _ h => absurd trivial h, rest⟩
    exact ⟨fun u hu => hvac.2.lat.1 u (hle hu), fun e' he' u hu hh => hvac.2.lat.2 e' he' u (hle hu) hh⟩
  have hO := hReps.2 (vac j) hV
  obtain ⟨eq, heq⟩ := hStd.1
  have hF := _root_.GlobalTheory.FinPl.PutIn.ratDatum_of_overAll (I.rec7 l Z) k ι p J hPl _ _ ψ hX.std _ _ (β j) (β (j + 1)) (x j).L (x (j + 1)).L
    (_root_.GlobalTheory.AdForm.intVec_isSelfDualC I hOk l Z j hjm _ hL0) (_root_.GlobalTheory.AdForm.intVec_isSelfDualC I hOk l Z (j + 1) hj _ hL1) hL0 hL1 _ e he ⟨eq, heq⟩ _ (vac j) _ hvac.2.theta hvac.2.lat hO
  have hval := _root_.GlobalTheory.PhiOneVal.phiT_base_eq_prod I hOk hPins l Z u a Ch A hA k ι p β Q _ hStd J hPl j hj α γ
  convert hF using 2 with z
  exact hval z

end GlobalTheory.AdForm

end
end

