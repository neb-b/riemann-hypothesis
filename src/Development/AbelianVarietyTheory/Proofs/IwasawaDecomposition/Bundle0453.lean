module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.JointCharacters.SameChr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnAdel

theorem grpId {G : Type*} [Group G] (a b c d : G) : a * (a⁻¹ * b * c * d⁻¹) * d = b * c := by group

theorem grpId2 {G : Type*} [Group G] (r y1 kb y0 hm m : G) (h : hm = r * (y1 * kb)) :
    r * y1 = y0 * (y0⁻¹ * hm * m⁻¹ * hm⁻¹ * y0) * (y0⁻¹ * hm * m * kb⁻¹) := by subst h; group

theorem etaFacts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (v0 : HeightOneSpectrum (𝓞 F))
    (y0 hm g0 : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))
    (hy0 : y0 ∈ Formalism.L2.Herm.UstdAf hc n) (hh : hm ∈ Formalism.L2.Herm.UstdAf hc n) (hg : g0 ∈ Formalism.L2.Herm.UstdAf hc n) :
    (∀ v', v' ≠ v0 → bc (prV (E := E) v') (y0⁻¹ * hm * (rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)))⁻¹ * hm⁻¹ * y0) = 1) ∧
      y0⁻¹ * hm * (rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)))⁻¹ * hm⁻¹ * y0 ∈ Formalism.L2.Herm.UstdAf hc n := by
  have hm0 : rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)) ∈ Formalism.L2.Herm.UstdAf hc n :=
    rll_put_mem_UAd hc n v0 (afsplit_bc_mem hc.sig 1 v0 _ (mul_mem (inv_mem hh) hg))
  refine ⟨fun v' hv' => ?_, ?_⟩
  · simp only [map_mul, map_inv]
    rw [rll_put_ne n v0 v' hv']
    group
  · exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hy0) hh) (inv_mem hm0)) (inv_mem hh)) hy0

theorem coreMove {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (v0 : HeightOneSpectrum (𝓞 F)) (U : Subgroup (GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))))
    (chi : U →* ℂˣ) (y0 y1 : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (kb : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (t s : ℂ) (hts : t = s⁻¹)
    (hk : kb ∈ Formalism.L2.Herm.UstdAf hc n)
    (hh : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) ∈ Formalism.L2.Herm.UstdAf hc n)
    (hlev : ∀ x, y0.1 * x * kb = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) *
        rll_put n v0 (bc (prV (E := E) v0) ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb))⁻¹ * (y0.1 * kb))) → x ∈ U)
    (hchi : ∀ x : U, y0.1 * x.1 * kb = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) *
        rll_put n v0 (bc (prV (E := E) v0) ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb))⁻¹ * (y0.1 * kb))) →
        ((chi x : ℂˣ) : ℂ) = t) :
    ∃ (η : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (κ : U), (∀ v', v' ≠ v0 → bc (prV (E := E) v') η.1 = 1) ∧
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y1.1 = y0.1 * η.1 * κ.1 ∧ (((chi κ)⁻¹ : ℂˣ) : ℂ) = s := by
  subst hJ
  set hm := bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) with hhm
  set m := rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * (y0.1 * kb))) with hmdef
  have hE := etaFacts hc n v0 y0.1 hm (y0.1 * kb) y0.2 hh (mul_mem y0.2 hk)
  have hx : y0.1 * (y0.1⁻¹ * hm * m * kb⁻¹) * kb = hm * m := grpId _ _ _ _
  have hU := hlev _ hx
  refine ⟨⟨_, hE.2⟩, ⟨_, hU⟩, hE.1, grpId2 _ _ _ _ _ _ hhm, ?_⟩
  rw [Units.val_inv_eq_inv_val, hchi ⟨_, hU⟩ hx, hts, inv_inv]

theorem actSameOff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (v : HeightOneSpectrum (𝓞 F)) {d d' : Deco E n ST SG}
    (h : Deco.SameOff ST SG v d d') (ga : Sp E n ≃ₗ[E] Sp E n) (hh : GLG (E := E) (n := n) (SG := SG)) :
    Deco.SameOff ST SG v (d.act ga hh) (d'.act ga hh) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    ext x
    show x ∈ localization₂ Q.asIdeal (gmap ga d.N) ↔ x ∈ localization₂ Q.asIdeal (gmap ga d'.N)
    rw [mem_localization_gmap, mem_localization_gmap, h.N Q hQ]
  · intro Q hQ
    funext x
    show d.f Q (ga.symm x) = d'.f Q (ga.symm x)
    rw [h.f Q hQ]
  · intro w hw
    funext x
    show (hh w).1.mulVec (d.be w (ga.symm x)) = (hh w).1.mulVec (d'.be w (ga.symm x))
    rw [h.be w hw]

theorem pointGen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 E)))
    (v0 : HeightOneSpectrum (𝓞 F)) (r0 d r' : DecoF E n ST SG Q) (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)
    (hmv : a • r' = d) (hfr : d.fr = r0.fr) (hoff : Deco.SameOff ST SG v0 r0.deco.1 d.deco.1)
    (hQSQ : Q ⊆ SQ) (hdis : Disjoint SG Q) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h0 : IsPtOf hc g0 (extTo SQ r0))
    (h1 : IsPtOf hc h (((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n SQ) • extTo SQ r'))
    (hQ : ∀ P ∈ Q, ¬ IsOver v0 P) (hSG : ∀ w ∈ SG, ¬ IsOver v0 w) :
    IsPtOf hc (h * rll_put n v0 (bc (prV (E := E) v0) (h⁻¹ * g0)))
      ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r0) := by
  have e1 : (((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d = ((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r' := by
    rw [← hmv, smul_smul]
    congr 1
    ext1
    · simp
    · ext1 <;> simp
  refine GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace hc n ST SG Q SQ SQ v0 g0 h (extTo SQ r0) _ _ h0 h1 hQ hSG ?_ ?_ ?_ ?_
  · have h2 := actSameOff v0 hoff (((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)).1.1) (((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)).2.1)
    have e2 : (((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n SQ) • extTo SQ r').deco.1 = ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d).deco.1 := by
      rw [e1]; rfl
    rw [e2]
    exact h2
  · intro P _
    ext x
    show x ∈ localization₂ P.asIdeal (gmap _ r0.deco.1.N) ↔ x ∈ localization₂ P.asIdeal r0.deco.1.N
    rw [mem_localization_gmap]
    exact Iff.rfl
  · intro P _
    funext x
    rfl
  · intro P
    refine ⟨⟨P.1, hQSQ P.2⟩, rfl, ?_⟩
    have hP : P.1 ∉ SG := Finset.disjoint_right.1 hdis P.2
    have e3 : ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r0).fr P =
        ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d).fr P := by
      show _ * r0.1.2 P * _ = _ * d.1.2 P * _
      rw [show d.1.2 P = d.fr P from rfl, hfr]; rfl
    rw [e3, e1]
    show a.1.1 * ptFr r' P.1 * _ = a.1.1 * r'.1.2 P * _
    rw [ptFr_of_mem r' hP P.2]
    simp
    rfl

theorem ufGL_UJ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : UF E n) : ufGL E n γ ∈ UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := by
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ


set_option maxHeartbeats 8000000 in
theorem move_down_adelic : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K eY eV L hR hY hV hL v β c g hg hβ
  obtain ⟨k, R⟩ := hR
  obtain ⟨c0, hc0⟩ := c
  subst hc0

  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((_root_.GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  haveI : NeZero (B.R.N i) := inferInstance
  have hP := _root_.GlobalTheory.Mem.PrimesAtLevel.primes_atT I hOk l u a v
  have hv0 : (eV v).1 = v.1.under (𝓞 B.host.F) := hV v
  have hd : ((I.atIn u a).A i).dnPt v c0 g = ((I.stp u a i).rep c0).mv (((I.stp u a i).rep c0).1.1.deco.dn v (TDat.extF _ v.1 g)) := rfl
  have hdn := GlobalTheory.T.moveDown_point_preserves_index_frames _ ((I.stp u a i).rep c0) v (TDat.extF _ v.1 g) (v.1.under (𝓞 B.host.F)) rfl hP.1 (IsOver.conj B.sp.cm rfl)
  rw [← hd, ← hv0] at hdn
  have hmv := (I.stp u a i).mv_smul c0.1 (((I.atIn u a).A i).dnPt v c0 g)
  have hyc' : ∀ (β' : Ch) (h : chOf ((I.fm l u a).dn i v c0 g) = β'), ((K β').y ⟨_, h⟩).1 = ((K (chOf ((I.fm l u a).dn i v c0 g))).y ⟨_, rfl⟩).1 := by rintro _ rfl; rfl
  have hk : k (chOf ((I.fm l u a).dn i v c0 g)) = k (chOf c0) := by rw [hβ]
  have hpt0 := R.pt c0
  have hpt1 := R.pt ((I.fm l u a).dn i v c0 g)
  rw [hk, ← hyc' _ hβ] at hpt1
  have hh := GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1 _ _ hpt1
  have hq := pointGen B.sp.cm (B.R.N i) _ _ _ I.SQ (eV v).1 _ _ _ (FrmG.incl _ _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g))) (congrArg (fun p => p.1.1) hmv) hdn.2.1 hdn.2.2 (I.Q_subset_SQ a) hP.2.2.2 _ _ hpt0 hh (hv0 ▸ hP.2.2.1) (hv0 ▸ hP.2.1)

  have hκ'mv : (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) * (I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g) = (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) := by
    ext1
    · simp
    · simp
  have hgam1 : (I.stp u a i).gam c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) = 1 := by
    show ufGL _ _ ((1 : UF B.fields.E (B.R.N i))⁻¹) = 1
    simp
  have hchr : (I.stp u a i).chr c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) = ((I.stp u a i).chr c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)))⁻¹ := by
    rw [map_inv]; rfl

  have hc1 := _root_.GlobalTheory.Mem.Col2.cosetIn_congr ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)) ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) (((I.atIn u a).A i).dnPt v c0 g)) (by
      show (fun x => _) '' _ = (fun x => _) '' _
      rw [hdn.1]) (by
      funext P
      show _ * ((I.stp u a i).rep c0).1.1.1.2 P * _ = _ * (((I.atIn u a).A i).dnPt v c0 g).1.1.1.2 P * _
      rw [show (((I.atIn u a).A i).dnPt v c0 g).1.1.1.2 = (((I.atIn u a).A i).dnPt v c0 g).1.1.fr from rfl, hdn.2.1]
      rfl) (fun w => ⟨(actSameOff _ hdn.2.2 _ _).N w.1 (hv0 ▸ hP.2.1 w.1 w.2), (actSameOff _ hdn.2.2 _ _).be w (hv0 ▸ hP.2.1 w.1 w.2)⟩)
  have hc2 : (I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) (((I.atIn u a).A i).dnPt v c0 g) = (I.stp u a i).act c0.1 (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) ((I.stp u a i).rep ((I.stp u a i).cl c0.1 (((I.atIn u a).A i).dnPt v c0 g))) := by
    unfold GStep.act
    rw [← hκ'mv]
    exact (congrArg (fun p => @HSMul.hSMul _ _ _ (@instHSMul _ _ ((I.stp u a i).actD c0.1).toSMul) (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) p) hmv).symm.trans (@mul_smul _ _ _ (@MulAction.toSemigroupAction _ _ _ ((I.stp u a i).actD c0.1)) _ _ _).symm
  have hc3 := _root_.GlobalTheory.Mem.Col2.cosetIn_act_rat I hOk l u a i c0.1 (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) ((I.stp u a i).rep ((I.stp u a i).cl c0.1 (((I.atIn u a).A i).dnPt v c0 g))) rfl
  have hkey := ((R.key ((I.fm l u a).dn i v c0 g) c0).1 hβ).2
  have hcos : cosetIn ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)) = cosetIn ((I.stp u a i).rep c0) := by
    rw [hc1, hc2, hc3]; exact hkey

  have hγU : (I.stp u a i).gam c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)) ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := by
    rw [hgram]; exact ufGL_UJ B.sp.cm _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1
  have hts : B.embLL (((I.stp u a i).chr c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) : B.LLˣ) : B.LL) = (B.embLL (((I.stp u a i).chr c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)) : B.LLˣ) : B.LL))⁻¹ := by
    rw [hchr, Units.val_inv_eq_inv_val, map_inv₀]
  obtain ⟨kp, hkp, -⟩ := R.k_std (chOf c0)
  obtain ⟨η, κ, h1, h2, h3⟩ := coreMove B.sp.cm (B.R.N i) (gramN (I.rec7 l Z) i hi) hgram (eV v).1 ((K (chOf c0)).lev.U) ((K (chOf c0)).lev.chi) ((K (chOf c0)).y ⟨c0, rfl⟩) ((K (chOf c0)).y ⟨_, hβ⟩) ((I.stp u a i).gam c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g))) (k (chOf c0)) _ _ hts hkp.uni hh.uni (fun x hx => (R.lev c0 x ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)).1.1 (by rw [hx]; exact hq)).2 ⟨(((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1), hgam1, rfl, hcos⟩) (fun x hx => R.chr c0 x (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) hgam1 (by rw [hx]; exact hq))
  exact ⟨⟨_, hγU⟩, η, κ, rfl, h1, h2, h3⟩

end GlobalTheory.Mem.Col2.DnAdel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.OpenPrinc

theorem close_of_open {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (K : Set R) (hK : IsCompact K)
    (ht : Filter.Tendsto (fun k : ℕ => ((k.factorial : ℕ) : R)) Filter.atTop (nhds 0))
    (G U : Subgroup (GL (Fin n) R)) (hU : IsOpen {x : G | (x : GL (Fin n) R) ∈ U}) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ z ∈ G, ∀ A B : Matrix (Fin n) (Fin n) R, (∀ i j, A i j ∈ K) → (∀ i j, B i j ∈ K) →
      (z : Matrix (Fin n) (Fin n) R) = 1 + (M : R) • A →
      ((z⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + (M : R) • B → z ∈ U := by
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.1 hU
  obtain ⟨O, hO, hOW⟩ := (Units.isInducing_embedProduct.isOpen_iff).1 hW
  have h1 : ((1 : Matrix (Fin n) (Fin n) R), MulOpposite.op (1 : Matrix (Fin n) (Fin n) R)) ∈ O := by
    have : (1 : G) ∈ {x : G | (x : GL (Fin n) R) ∈ U} := U.one_mem
    rw [← hWU, ← hOW] at this
    simpa using this
  have hKM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ K} := by
    have := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hK))
    have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ K} =
        Set.univ.pi (fun _ : Fin n => Set.univ.pi (fun _ : Fin n => K)) := by
      ext A
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact this
  have hg : Continuous (fun p : R × (Matrix (Fin n) (Fin n) R × Matrix (Fin n) (Fin n) R) =>
      ((1 + p.1 • p.2.1, MulOpposite.op (1 + p.1 • p.2.2)) :
        Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ)) := by
    fun_prop
  have hev := (hKM.prod hKM).eventually_forall_of_forall_eventually (x₀ := (0 : R))
    (P := fun c p => ((1 + c • p.1, MulOpposite.op (1 + c • p.2)) :
        Matrix (Fin n) (Fin n) R × (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ) ∈ O) (by
      intro y _
      apply (hO.preimage hg).mem_nhds
      simpa using h1)
  obtain ⟨k, hk⟩ := (ht.eventually hev).exists
  refine ⟨k.factorial, k.factorial_ne_zero, fun z hz A B hA hB h₁ h₂ => ?_⟩
  have := hk (A, B) ⟨hA, hB⟩
  have h3 : (⟨z, hz⟩ : G) ∈ {x : G | (x : GL (Fin n) R) ∈ U} := by
    rw [← hWU, ← hOW]
    simp only [Set.mem_preimage, Units.embedProduct_apply]
    rw [h₁, h₂]
    exact this
  exact h3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem den_nat {κ : Type} [Fintype κ] (f : κ → E) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  obtain ⟨m, hm, h⟩ := Formalism.UG.P.adelstabL_den f
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm, fun i => ?_⟩
  rcases Int.natAbs_eq m with e | e
  · have := h i
    rw [e, Int.cast_natCast] at this
    exact this
  · have := (h i).neg
    rw [e, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this
    exact this

theorem exists_smul_mem {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ m : ℕ, m ≠ 0 ∧ (m : E) • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatSmulMemIntegral.exists_nat_smul_mem ..)

theorem exists_den {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hf : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ y ∈ Λ, ∀ i, IsIntegral ℤ ((m : E) * y i) := by
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.1 hf
  obtain ⟨m, hm, h⟩ := den_nat (fun p : s × Fin n => (p.1 : Fin n → E) p.2)
  refine ⟨m, hm, fun y hy i => ?_⟩
  rw [← hs] at hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact h (⟨x, hx⟩, i)
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
  | smul e x _ hx =>
    have : (m : E) * (e • x) i = (e : E) * ((m : E) * x i) := by
      change (m : E) * ((e : E) * x i) = _
      ring
    rw [this]
    exact e.isIntegral_coe.mul hx

theorem incl_mem_intV (v : HeightOneSpectrum (𝓞 F)) {e : E} (he : IsIntegral ℤ e) :
    inclE (v.adicCompletion F) e ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨e, ⟨⟨e, he⟩, rfl⟩⟩, rfl⟩)

theorem loc_upper {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hf : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ y ∈ Formalism.L2.Herm.locL v Λ, ∀ i,
      (m : E ⊗[F] v.adicCompletion F) * y i ∈ intV E v := by
  obtain ⟨m, hm, h⟩ := exists_den Λ hf
  refine ⟨m, hm, fun y hy i => ?_⟩
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    have := incl_mem_intV v (h u hu i)
    rwa [map_mul, map_natCast] at this
  | zero => simpa using (intV E v).zero_mem
  | add x y _ _ hx hy => simpa [mul_add] using (intV E v).add_mem hx hy
  | smul e x _ hx =>
    have : (m : E ⊗[F] v.adicCompletion F) * (e • x) i =
        (e : E ⊗[F] v.adicCompletion F) * ((m : E ⊗[F] v.adicCompletion F) * x i) := by
      change (m : E ⊗[F] v.adicCompletion F) * ((e : E ⊗[F] v.adicCompletion F) * x i) = _
      ring
    rw [this]
    exact (intV E v).mul_mem e.2 hx

theorem loc_lower {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ j, (Pi.single j (m : E ⊗[F] v.adicCompletion F) : Fin n → E ⊗[F] v.adicCompletion F)
      ∈ Formalism.L2.Herm.locL v Λ := by
  choose a ha h using fun j : Fin n => exists_smul_mem Λ hs (Pi.single j 1)
  refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.2 fun j _ => ha j, fun j => ?_⟩
  obtain ⟨c, hc⟩ : a j ∣ ∏ j, a j := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have h1 : (fun i => inclE (v.adicCompletion F) (((a j : E) • (Pi.single j 1 : Fin n → E)) i))
      ∈ Formalism.L2.Herm.locL v Λ := Submodule.subset_span ⟨_, h j, rfl⟩
  have h2 := nsmul_mem h1 c
  convert h2 using 1
  funext i
  by_cases hij : i = j
  · subst hij
    simp [hc, mul_comm]
  · simp [hij]

theorem loc_entries {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hf : Module.Finite (𝓞 E) Λ) (hs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ (M : ℕ) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)),
      (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ,
        x *ᵥ y - y = ((d * M : ℕ) : E ⊗[F] v.adicCompletion F) • z) →
      ∃ A : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F), (∀ i j, A i j ∈ intV E v) ∧
        x = 1 + (M : E ⊗[F] v.adicCompletion F) • A := by
  obtain ⟨a, ha, h₁⟩ := loc_upper v Λ hf
  obtain ⟨b, hb, h₂⟩ := loc_lower v Λ hs
  refine ⟨a * b, mul_ne_zero ha hb, fun M x hx => ?_⟩
  choose z hz hxz using fun j => hx _ (h₂ j)
  refine ⟨fun i j => (a : E ⊗[F] v.adicCompletion F) * z j i, fun i j => h₁ _ (hz j) i, ?_⟩
  have hu : IsUnit (b : E ⊗[F] v.adicCompletion F) := by
    have : IsUnit (b : E) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hb)
    simpa using this.map (inclE (F := F) (v.adicCompletion F))
  ext i j
  apply hu.mul_left_cancel
  have := congrFun (hxz j) i
  simp only [Pi.sub_apply, Matrix.mulVec_single, Pi.smul_apply, smul_eq_mul, Nat.cast_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.col_apply] at this
  change _ = (b : E ⊗[F] v.adicCompletion F) * ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j +
    (M : E ⊗[F] v.adicCompletion F) * ((a : E ⊗[F] v.adicCompletion F) * z j i))
  have e : (Pi.single j (b : E ⊗[F] v.adicCompletion F) : Fin n → E ⊗[F] v.adicCompletion F) i =
      b * (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [e] at this
  linear_combination this

theorem glob_eq {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (M : ℕ)
    (A : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    Formalism.UG.P.afsplitC v (1 + (M : E ⊗[F] v.adicCompletion F) • A) 1 =
      1 + (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) • A.map (Formalism.UG.P.afsplitIE v) := by
  ext i j
  rw [Formalism.UG.P.afsplitC_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, Nat.cast_smul_eq_nsmul, map_add (f := _), map_nsmul,
    Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
    ring
  · simp [Matrix.one_apply_ne hij]

attribute [local instance] rlt_top rlt_topRing

theorem tendsto_fact_tens : Filter.Tendsto
    (fun k : ℕ => ((k.factorial : ℕ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Filter.atTop (nhds 0) := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  haveI := rlt_isModTop F E
  have := (GlobalTheory.Mem.Col2.AdT.Opn.tendsto_fact F).smul_const (1 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
  simpa [Nat.cast_smul_eq_nsmul] using this

theorem open_princ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ J v S.Lb →
      (∀ y ∈ Formalism.L2.Herm.locL v S.Lb, ∃ z ∈ Formalism.L2.Herm.locL v S.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y =
          (N : E ⊗[F] v.adicCompletion F) • z) → x ∈ S.Uloc v := by
  obtain ⟨M, hM, hU⟩ := close_of_open _ (rlt_isCompact_intAf (F := F) (E := E)) tendsto_fact_tens
    (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U S.U_open
  obtain ⟨d, hd, hL⟩ := loc_entries v S.Lb S.Lb_fin S.Lb_span
  refine ⟨d * M, Nat.pos_of_ne_zero (mul_ne_zero hd hM), fun x hx hc => ?_⟩
  have hxi : ∀ y ∈ Formalism.L2.Herm.locL v S.Lb,
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y
        ∈ Formalism.L2.Herm.locL v S.Lb := fun y hy =>
    (((levelVL σ J v S.Lb).inv_mem hx).2 y).1 hy
  obtain ⟨A, hA, hxA⟩ := hL M x hc
  obtain ⟨B, hB, hxB⟩ := hL M ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix _ _ _) (by
    intro y hy
    obtain ⟨z, hz, e⟩ := hc y hy
    refine ⟨_, Submodule.neg_mem _ (hxi z hz), ?_⟩
    rw [smul_neg, ← Matrix.mulVec_smul, ← e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec, neg_sub])
  have hX : Formalism.UG.P.afsplitU v x 1 ∈ S.U := by
    refine hU _ (Formalism.UG.P.afsplitU_mem v σ J x 1 hx.1 (Subgroup.one_mem _))
      (A.map (Formalism.UG.P.afsplitIE v)) (B.map (Formalism.UG.P.afsplitIE v))
      (fun i j => Formalism.UG.P.afsplit_IE_int v _ (hA i j))
      (fun i j => Formalism.UG.P.afsplit_IE_int v _ (hB i j)) ?_ ?_
    · rw [Formalism.UG.P.afsplitU_coe, hxA, Units.val_one, glob_eq]
    · rw [Formalism.UG.P.afsplitU_inv_coe, hxB, inv_one, Units.val_one, glob_eq]
  have h := ((S.U_eq _).1 hX).2 v
  have e : bc (prV v) (Formalism.UG.P.afsplitU v x 1) = x := by
    apply Units.ext
    have := Formalism.UG.P.afsplitC_prV v (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      ((1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _)
    rw [← Formalism.UG.P.afsplitU_coe] at this
    exact this
  rwa [e] at h

end GlobalTheory.OpenPrinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameChrOfChrEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameChrFin

theorem sameChr_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch) (X : ThetaX D)
    (T : ThetaTied D X) (H : Formalism.L2.Host.ThetaChrTied D C nch Tp X),
    (∀ c, Formalism.IndefR.Links.ChrEq (T.eChr c) (H.eChr c)) → Formalism.L2.JoinChr.SameChr T H := by
  intro D C nch Tp X T H h
  refine ⟨fun P => ?_, fun c P e he k x hx => (h c).2 P e he k x hx,
    fun θ hθ c τ k x hx => GlobalTheory.CharInfPlace.chrEq_infLoc D (T.eChr c) (H.eChr c) (h c) θ hθ τ k x hx⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  exact ⟨e, he⟩

end GlobalTheory.SameChrFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdPointMatrixAndInverseIntegralAtEveryPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  first | exact @GlobalTheory.ptOf_std_entries_intAtA | exact GlobalTheory.ptOf_std_entries_intAtA | (intros; apply GlobalTheory.ptOf_std_entries_intAtA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z → z ∈ S.U := by
  first | exact @GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep | exact GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep | (intros; apply GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep <;> assumption)
end

