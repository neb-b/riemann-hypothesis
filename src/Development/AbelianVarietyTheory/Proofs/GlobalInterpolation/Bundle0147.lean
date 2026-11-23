module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefModB
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleAdjointRationalPointPadicMatrix
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0141
public import Formalism.LocalToGlobal.Columns.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulEqOfUnif
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KmapOfOkOfVecP
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0136
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LastStepIntegralFormLocalCoordsMemIntegralSpan
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerQ.Co

theorem bc_invTrK_embGL {B : Base} {n : ℕ} (g : GL (Fin n) B.fields.E) :
  (fun τ => Formalism.UG.bc B.embLL (invTrK (embGL B.fields.emb g) τ)) = invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) g) := by
  funext τ
  apply Units.ext
  ext i j
  simp [invTrK, inside₂, embGL, Formalism.UG.bc, Formalism.L2.Col.embAt]
  rw [← Matrix.map_map, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix, ← Formalism.L2.Col.map_inv_matrix]
  rfl

theorem intSpan_smul (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) (p : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ)
    (hp : p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam) : D.what₂.embLL r • p ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan at *
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hq
    apply AddSubgroup.subset_closure
    exact ⟨r * r', f, mul_mem hr hr', hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem latCo_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl)
    (y : (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V) (hy : y ∈ (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L) :
    GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) ∈
      Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  set v' := ((I.chIn u a).S B.R.m).rho B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u a).b0 (((I.chIn u a).S B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c))
          (y.1 (((I.chIn u a).S B.R.m).cl (I.perIn u a).b0 ((I.perIn u a).tilPt c))) with hv'
  have hmem := GlobalTheory.LvT.BuiltChain.rho_mv_mem B.fields.emb ((I.chIn u a).S B.R.m) (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y hy (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have e1 : GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) y ((I.perIn u a).tilC c)) =
      actP (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (invTrK (embGL (Formalism.L2.Col.embAt B.embLL B.fields.emb) (GlobalTheory.PerQ.Co.bM I u a w c)⁻¹))
        (MvPolynomial.map B.embLL v'.1) := by
    unfold GlobalTheory.PerQ.Co.coM
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    congr 1
    rw [← GlobalTheory.LvT.BuiltChain.polOf_evV B.fields.emb B.embLL]
    congr 1
    rw [hv', GlobalTheory.LvT.BuiltChain.evV_rho]
    rfl
  rw [e1, ← bc_invTrK_embGL, ← GlobalTheory.ValCmp.use₂]
  have hB := (_root_.GlobalTheory.PerQ.Co.usage₉ I hI l u a w c).2.2.2
  have hM : Submodule.IsFullLattice B.fields.E (((I.chIn u a).S B.R.m).Lsh (I.perIn u a).b0 ((I.perIn u a).tilPt c)) :=
    ((l.ch u a).step B.R.m).lsh_full_lat (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have hnat : ∀ τ, ((GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW := by
    intro τ
    show (GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) B.R.m) _).natW = (Examples₂.lamOf (B.hcW u τ) B.R.m).natW
    funext i
    have hN : 0 < B.R.N B.R.m := lt_of_le_of_lt (Nat.zero_le _) i.2
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hN, GlobalTheory.Mem.Col2.shW]
    congr 1
    ring
  exact (_root_.GlobalTheory.WeylLocOnePlace.mem_locW_delAtr_iff B.fields.emb B.embLL B.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq
    (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) hnat _ hM w _ hB v').1 (Submodule.subset_span hmem)

theorem latCo_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (w : B.places.Pl) (c : (I.perIn u a).S'.Cl) :
    ∀ x ∈ Submodule.span (intW B.places w) ((((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).L : Set (((I.chIn u a).S B.R.m).hlat B.fields.emb (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m)).V),
      GlobalTheory.PerQ.Co.coM I u a w c (((I.chIn u a).S B.R.m).embF B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) ((l.fmL u a).fam B.R.m) x ((I.perIn u a).tilC c)) ∈
        Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact latCo_one I hI l Z u a w c y hy
  | zero => rw [map_zero, Pi.zero_apply, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), Pi.add_apply, map_add (f := _)]; exact add_mem hy hz
  | smul r y _ hy =>
    have e : r • y = (r : B.LL) • y := rfl
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, map_smul]
    exact intSpan_smul (I.rec7 l Z) w _ (r : B.LL) r.2 _ hy

theorem latCo_mem_intSpan : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι) (w : B.places.Pl), ∀ x ∈ ((I.tw l l0 Z).fm u a).S (I.rec7 l Z).R.m w, ∀ c, GlobalTheory.PerQ.Co.coM I u a w c (((I.tw l l0 Z).fm u a).emb (I.rec7 l Z).R.m x (((I.tw l l0 Z).fm u a).til c)) ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan (I.rec7 l Z) w (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) :=
  fun I hI l Z _ u a w x hx c => latCo_gen I hI l Z u a w c x hx

end GlobalTheory.PerQ.Co

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundConjugatePrimePlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open _root_.Formalism.L2.Col

local instance starFields (B : Base) : StarRing B.fields.E := B.fields.starE

theorem kerBar : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerBar (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJM hP B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hA : ColIn.A I = ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J)
      (ColIn.chi I) I.J.cD := by
    rw [ColIn.A, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hAl := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hRS := GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
    (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi
  rw [hA] at hRS
  have hRT : GlobalTheory.KerT.RatTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) _ u i hX hPr
      h.sel_ok (h.T_mem u) hRS
  have hT := isTerm h u a hi
  intro w hw hseen b b' d d' F hF
  classical
  unfold OverT at hw
  have hw' : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have h0 := Formalism.L2.Col.att_resChar_mem (I.rec7 l Z).what₂.places (I.rec7 l Z).plEq (I.rec7 l Z).val_eq w
    rw [hw] at h0
    exact h0
  have hs : ¬ seenC (B.primes X) u ((I.rec7 l Z).plEq w) := fun hc => by
    have h0 : decide (seenC (B.primes X) u ((I.rec7 l Z).plEq w)) = false := hseen
    simp [hc] at h0
  have hsb : seenBarC (B.primes X) u ((I.rec7 l Z).plEq w) := (seenC_or_seenBarC hX hPr u _ hw').resolve_left hs
  have hbar : GlobalTheory.KerT.BarTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD) u i (i + 1)
      ((I.rec7 l Z).plEq w) := GlobalTheory.KerT.Bar.barTerm_of_std I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hRT ((I.rec7 l Z).plEq w)
    (fun d fr d' fr' Ξ₀ => GlobalTheory.BarStd.barStd hJM hP I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hAl
      ((I.rec7 l Z).plEq w) hsb d fr d' fr' Ξ₀)
  rw [← hA] at hbar
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := hT b b' d d'
  have hk' := hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  rw [hk']
  have hF' : F ∈ GlobalTheory.KerT.valAt ((I.rec7 l Z).plEq w) (B.wts.lamTrue u i) d.1.1.deco.1.Lsh := hF
  obtain ⟨y', hy', he⟩ := hbar d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hw') F hF'
  refine ⟨y', hy', he.trans ?_⟩
  have e1 : B.fields.f = (I.rec7 l Z).R.f := GlobalTheory.Mem.Base.fields_f B
  rw [e1]
  rfl

end GlobalTheory.LvT.Built.TrueLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundLevelPrimePlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

theorem kerP : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) → ∀ i, i < B.R.m → Dat.KerP (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  intro hJet hKnown B X I h hJ l Z u a hth i hi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro w hw hs b b' d d' F hF
  obtain ⟨Ξ₀, hbox, hint, hfr, hfr', hk⟩ := isTerm h u a hi b b' d d'
  rw [hk d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩]
  have h1 := GlobalTheory.LvT.Inh.resChar_mem_plEq (I.rec7 l Z) w
  have eA := AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J I.chi
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  have hal := GlobalTheory.KerT.alcoveAt_of_ok I.dat hH.ok u (i + 1) (Nat.succ_le_of_lt hi)
  have hrat : GlobalTheory.KerT.RatTerm B.wts I.Ch I.sel (I.tup a) (I.cst a) (ColIn.A I) u i (i + 1) :=
    GlobalTheory.KerRat.ratTerm_of_ratStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (ColIn.A I) u i hX hPr
    h.sel_ok (h.T_mem u) (GlobalTheory.KerT.ratStep_of_chTh_ok B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob
      (B.R.m - 2) u i (ColIn.A I) hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth hi)
  rw [ColIn.A, eA] at hrat
  have hseen : Formalism.L2.Col.seenC (B.primes X) u ((I.rec7 l Z).plEq w) := @of_decide_eq_true _ (Classical.propDecidable _) hs
  have hPT : GlobalTheory.KerT.PTerm B.wts I.Ch I.sel (I.tup a) (I.cst a)
      (ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (AmbIn.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J) (ColIn.chi I) I.J.cD)
      u i (i + 1) ((I.rec7 l Z).plEq w) :=
    GlobalTheory.KerT.PAll.pTerm_of_std I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hrat _
    (GlobalTheory.KerT.PStd.pTerm_std hJet hKnown I.dat (I.rec7 l Z) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hJa hal _ hseen)
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.K) ∈ ((I.rec7 l Z).plEq w).asIdeal := by
    have e := hw
    unfold OverT at e
    rw [e] at h1
    exact h1
  letI : StarRing B.fields.E := B.fields.starE
  have key := hPT d.1.1.deco _ d'.1.1.deco _ Ξ₀ hfr hfr' hbox (hint _ hT) F hF
  rw [ColIn.A, eA]
  have eS : ∀ τ, (dat I l Z u a).ch.C.sDiv i τ = -((B.wts.lamTrue u (i + 1) τ).detShift) := fun τ => by
    have e1 := (KMap.sSharp_eq (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi τ).2
    have e2 := GlobalTheory.GO.ChSrc.trueWt_detShift_succ (X := B.fields) (B.wts.hc u) hi τ
    have e3 := congrFun (GlobalTheory.GO.ChSrc.trueWt_eq B.wts u (i + 1)) τ
    refine e1.trans ?_
    rw [← e3, e2, neg_neg]
  have eE : (((I.rec7 l Z).R.f * (I.rec7 l Z).R.N i : ℕ) : ℤ) + ∑ τ, (dat I l Z u a).ch.C.sDiv i τ =
      ((B.fields.f * B.R.N i : ℕ) : ℤ) - ∑ τ, (B.wts.lamTrue u (i + 1) τ).detShift := by
    rw [Finset.sum_congr rfl (fun τ _ => eS τ), Finset.sum_neg_distrib, B.fields_f, sub_eq_add_neg]
    rfl
  rw [eE]
  exact key

end GlobalTheory.LvT.Built.TrueLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedChainInitialLatticeCompatibleTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem valAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ)
    (b : (I.stp u I.mu0 0).β) (b' : (I.stp u a 0).β) (p : (I.stp u I.mu0 0).D b) (p' : (I.stp u a 0).D b')
    (h : p.1.1.deco = p'.1.1.deco) :
    valAt (I.stp u a 0) B.fields.emb B.embLL (fun c => φ ((I.eCls0 l u a).symm c)) b' p' =
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ b p := by
  have hc : I.eCls0 l u a ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p')) = (I.stp u a 0).cl b' p' :=
    (I.eCls0 l u a).apply_symm_apply _
  have hdeco : ((I.stp u a 0).rep ((I.stp u a 0).cl b' p')).1.1.deco =
      ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))).1.1.deco := by
    conv_lhs => rw [← hc]
    exact stepZero_corresponding_representatives_same_deco hI u a _ _
  show (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p')
      (φ ((I.eCls0 l u a).symm ((I.stp u a 0).cl b' p'))) = _
  generalize (I.eCls0 l u a).symm ((I.stp u a 0).cl b' p') = c at hdeco ⊢
  obtain ⟨b₁, q⟩ := c
  obtain rfl : b = b₁ := stepZero_chartIndex_subsingleton hI _ _ _
  have hm := (I.stp u a 0).mv_smul b' p'
  have hy : ∀ N, (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) 0).ys N = {∅} := fun N => by rw [ys0]; rfl
  obtain ⟨g, g1, g2, g3⟩ := GlobalTheory.LvT.StartTie.exists_lift (y' := ysAt B.R I.sel (I.tup a) (I.cst a) 0) hy
    ((levelTypePrimes_stepZero_eq_colLev hI I.mu0 b).trans (levelTypePrimes_stepZero_eq_colLev hI a b').symm) (chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 b) (chartIndexLevelTwistPrimes_stepZero_eq_top hI a b')
    ((I.stp u a 0).mv b' p') ((I.stp u I.mu0 0).rep ⟨b, q⟩) p ((I.stp u a 0).rep ((I.stp u a 0).cl b' p'))
    hdeco.symm (h.trans (congrArg (fun r : (I.stp u a 0).D b' => r.1.1.deco) hm).symm)
  have h1 := valAt_eq B.fields.emb B.embLL (l.lev u I.mu0).free0 φ ⟨b, q⟩ g
  refine Eq.trans ?_ (h1.symm.trans (congrArg _ g1))
  have h2 : (I.stp u a 0).tr B.fields.emb B.embLL b' ((I.stp u a 0).mv b' p') =
      (I.stp u I.mu0 0).tr B.fields.emb B.embLL b g :=
    congrArg₂ (trFr B.fields.emb B.embLL) (congrArg (Formalism.L2.Col.ufGL B.fields.E (B.R.N 0)) g2.symm) g3.symm
  exact congrFun (congrArg DFunLike.coe h2) _

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem rep_eCls0_symm (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c' : (I.stp u a 0).Cl) :
    ((I.stp u I.mu0 0).rep ((I.eCls0 l u a).symm c')).1.1.deco = ((I.stp u a 0).rep c').1.1.deco := by
  conv_rhs => rw [← (I.eCls0 l u a).apply_symm_apply c']
  exact (stepZero_corresponding_representatives_same_deco hI u a _ _).symm

theorem nm_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Nm (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Nm (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  unfold Nm
  erw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  funext c'
  refine (valAt_eCls0 hI l u a φ _ _ _ _ ?_).symm
  exact (dia_deco _ v a').trans ((congrArg (Formalism.L2.Col.DecoSet.dia1 v a') (rep_eCls0_symm hI l u a c')).trans
    (dia_deco _ v a').symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem up_deco0 (l : I.Laws) (u : B.Word) (a : I.ι) (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b)
    (P : (I.atIn u a).ST) (x : Formalism.L2.Col.Sp B.fields.E (B.R.N 0)) (hx : x ∈ p.1.1.deco.1.N) (hf : p.1.1.deco.1.f P x = 1) :
    (((I.atIn u a).A 0).up b p P x).1.1.deco = p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x := by
  change (p.mv (p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x)).1.1.deco = _
  by_cases hc : (p.1.1.deco.1.up P ((I.atIn u a).T : 𝓞 B.fields.E) x).Ok
  · apply mv_deco
    have h1 := congrArg Formalism.L2.Col.Deco.N (((l.lev u a).tied 0).up_deco b p P x hx hf)
    refine Eq.trans h1 ?_
    unfold Formalism.L2.Col.DecoSet.up
    rw [dif_pos hc]
    rfl
  · have h1 : p.1.1.deco.up P ((I.atIn u a).T : 𝓞 B.fields.E) x = p.1.1.deco := dif_neg hc
    rw [h1]
    exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => q.1.1.deco) (dif_pos ⟨p.1.1.2, p.2⟩ : p.mv p.1.1.deco = _)

def onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) : Finset (Y.fm.lv 0 v c) :=
  Finset.univ.filter (fun x : Y.fm.lv 0 v c => Y.fm.fv 0 v c x = 1)

theorem mem_onesAt {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v : Y.A.vT) (c : Y.C.cls 0) (x : Y.fm.lv 0 v c) :
    x ∈ onesAt Y v c ↔ Y.fm.fv 0 v c x = 1 := by
  simp [onesAt]

theorem uop_apply {D : D7} {u' : D.what₂.Word} (Y : Ch D u') (v) (φ : Fn Y 0) :
    Uop Y 0 v φ = fun c => ∑ x ∈ onesAt Y v c, Y.fm.upT 0 v c x (φ (Y.fm.up 0 v c x)) := by
  funext c
  simp [Uop, LinearMap.sum_apply, onesAt]

theorem uop_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) = Uop (tw (I.tw l l0 Z) u a) 0 v ((I.cols l).e0Tw u a φ) := by
  funext c'
  have hd := rep_eCls0_symm hI l u a c'
  have hN := congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) => d.1.N) hd
  have hF := congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) => d.1.f v) hd
  refine (show (I.cols l).e0Tw u a (Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ) c' =
    Uop (tw (I.tw l l0 Z) u I.mu0) 0 v φ ((I.eCls0 l u a).symm c') from rfl).trans ?_
  refine (congrFun (uop_apply (tw (I.tw l l0 Z) u I.mu0) v φ) _).trans
    (Eq.trans ?_ (congrFun (uop_apply (tw (I.tw l l0 Z) u a) v ((I.cols l).e0Tw u a φ)) c').symm)
  revert hd hN hF
  generalize (I.eCls0 l u a).symm c' = c
  intro hd hN hF
  refine Eq.trans ?e1 (up_match B.fields.emb B.embLL (l.lev u I.mu0).free0 ((l.lev u I.mu0).lev 0) ((l.lev u I.mu0).tied 0)
    ((l.lev u a).lev 0) ((l.lev u a).tied 0) v (onesAt (tw (I.tw l l0 Z) u I.mu0) v) ?hs c' _ ?hs' φ ((I.cols l).e0Tw u a φ) c.1 ((I.stp u I.mu0 0).rep c)
    hN hF ?hup)
  case e1 =>
    exact (valAt_rep B.fields.emb B.embLL (l.lev u I.mu0).free0 (fun c => ∑ x ∈ onesAt (tw (I.tw l l0 Z) u I.mu0) v c,
      valAt (I.stp u I.mu0 0) B.fields.emb B.embLL φ c.1 (((I.atIn u I.mu0).A 0).upPt v c x)) c).symm
  case hs => exact fun c x => mem_onesAt (tw (I.tw l l0 Z) u I.mu0) v c x
  case hs' => exact fun x => mem_onesAt (tw (I.tw l l0 Z) u a) v c' x
  case hup =>
    intro x hx h1
    refine valAt_eCls0 hI l u a φ _ _ _ _ ?_
    refine (up_deco0 l u I.mu0 _ _ v x hx h1).trans ((congrArg (fun d : Formalism.L2.Col.DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := _) (SG := _) =>
      d.up v ((I.atIn u a).T : 𝓞 B.fields.E) x) hd).trans
        (up_deco0 l u a _ _ v x (hN ▸ hx) (by rw [← congrFun hF x]; exact h1)).symm)

end GlobalTheory.LvT.TrueStep0

namespace GlobalTheory.LvT.TrueStep0

open GlobalTheory.LvT.StartTie GlobalTheory.Mem.Col2.ClsZero

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem uop_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (v : (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Uop (tw (I.tw l l0 Z) u a) 0 v φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  erw [uop_apply]
  exact DiaStab.mem_Fi _ B.fields.emb B.embLL _ (l.lev u a).free0 _ fun _ => Submodule.sum_mem _ fun _ _ =>
    DiaStab.tr_mem _ B.fields.emb B.embLL _ _ _ (hφ _).1

theorem ulist_mem (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) {φ : Fn (tw (I.tw l l0 Z) u a) 0} (hφ : φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0) :
    Ulist (tw (I.tw l l0 Z) u a) ls φ ∈ (tw (I.tw l l0 Z) u a).fm.Fi 0 := by
  induction ls with
  | nil => exact hφ
  | cons v ls ih => exact uop_mem l l0 Z u a v ih

theorem ulist_eCls0 (hI : I.Ok) (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (ls : List (tw (I.tw l l0 Z) u a).A.vT) (φ : Fn (tw (I.tw l l0 Z) u I.mu0) 0) :
    (I.cols l).e0Tw u a (Ulist (tw (I.tw l l0 Z) u I.mu0) ls φ) = Ulist (tw (I.tw l l0 Z) u a) ls ((I.cols l).e0Tw u a φ) := by
  induction ls with
  | nil => rfl
  | cons v ls ih => exact (uop_eCls0 hI l l0 Z u a v _).trans (congrArg (Uop (tw (I.tw l l0 Z) u a) 0 v) ih)

theorem step0Tie_trueCols : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), Step0Tie (I.tw l l0 Z) u a := by
  intro B X I hI l l0 Z u a w _
  refine ⟨rfl, fun x hx => ?_⟩
  refine nlam_map (X := tw (I.tw l l0 Z) u I.mu0) (Y := tw (I.tw l l0 Z) u a)
    (e := (I.cols l).e0Tw u a) (eL := (I.tw l l0 Z).e0 u a) w rfl ((I.tw l l0 Z).embed_mul_block_embedding u a)
    (fun x hx => ((I.tw l l0 Z).twist_preserves_base_lattice u a x).1 hx) (fun v => ⟨v, fun φ _ => nm_eCls0 hI l l0 Z u a v φ⟩) rfl
    (fun φ hφ => ulist_mem l l0 Z u I.mu0 _ hφ) (fun φ _ => ulist_eCls0 hI l l0 Z u a _ φ) hx

end GlobalTheory.LvT.TrueStep0
end
end

