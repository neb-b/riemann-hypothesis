module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JoinEquivEqAtReference
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MidLevMulBeforeLast
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi

theorem last_rep_one {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∃ b : (I.idx a).β (B.R.m - 1), ∀ P, (I.idx a).h (B.R.m - 1) b P = 1 := by
  have hL := hOk.idx_ok a
  have e : B.R.m - 1 = B.R.m - 2 + 1 := by have := hL.hm; omega
  rw [e]
  obtain ⟨b, -⟩ := hL.last_uniq
  exact ⟨b, hL.last_h b⟩

theorem prCat_last_le_GLint {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 ≤ Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1 := by
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have h := (hOk.idx_ok a).int (B.R.m - 1) b P
  rwa [hb P] at h

theorem inv_mul_rearrange {G : Type*} [Group G] (A B C D : G) : (A * B)⁻¹ * (C * D) = (B⁻¹ * D) * (D⁻¹ * (A⁻¹ * C) * D) := by
  group

theorem nearAt_prod_of_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ex ey : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (rg rg' : GL (Fin N) E)
    (hx : GlobalTheory.TwU.CongAt P n (ex⁻¹ * GlobalTheory.TwU.ratA F rg)) (hy : GlobalTheory.TwU.CongAt P n (ey⁻¹ * GlobalTheory.TwU.ratA F rg'))
    (hint : ∀ a b, IntAt P ((rg' : Matrix (Fin N) (Fin N) E) a b) ∧ IntAt P (((rg'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) a b)) :
    GlobalTheory.TwU.CongAt P n ((ex * ey)⁻¹ * GlobalTheory.TwU.ratA F (rg * rg')) := by
  rw [map_mul, inv_mul_rearrange]
  exact GlobalTheory.CplPt.congAt_mul _ hy (GlobalTheory.CplPt.congAt_conj _ hx hint)

theorem nearV_mul_pairs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) (x y : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F)) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P x g z → GlobalTheory.Mem.Col2.QChi.NearPair I l Z a v P y g' z' → GlobalTheory.Mem.Col2.QChi.NearV I l Z a v P (x * y) (g * g') := by
  intro B X I hOk l Z a v P x y g g' z z' hx hy
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 :=
    (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g').1 ⟨z', hy.1⟩
  have hint := prCat_last_le_GLint I hOk a P hg'
  have hx2 := hx.2
  have hy2 := hy.2
  unfold NearV GlobalTheory.TwU.NearAt at hx2 hy2 ⊢
  have key := nearAt_prod_of_conj _ _ _ _ _ _ hx2 hy2 (GlobalTheory.CplPt.seamGL_int (sm I l Z) ⟨g', hint⟩)
  rw [map_mul (GlobalTheory.Mem.Col2.ChartLevel.emb v)]
  erw [map_mul (GlobalTheory.TwU.seamGL (sm I l Z)) g g']
  exact key

theorem chiInv_last_eq_char {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) (P : SBof I a) :
    ∃ φ : ↥(prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1) →* B.fields.Kˣ,
      ∀ r ∈ Loc.Cbe (Jat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1) 1,
      ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
      (∀ x, r (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) = Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) (g x)) →
      chiInv I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 r = φ ⟨g, hg⟩ := by
  have hL := hOk.idx_ok a
  obtain ⟨b, hb⟩ := last_rep_one I hOk a
  have hint := prCat_last_le_GLint I hOk a P
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        GlobalTheory.TopStep.redGL _ P.1 ⟨g, hint hg⟩ ∈ ((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).H := fun g hg =>
      (hL.grpG _ b ⟨P.1, hP⟩ _).2 ⟨g, by rw [hb]; exact hg, fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx⟩
    refine ⟨((I.idx a).levG (B.R.m - 1) b ⟨P.1, hP⟩).lam.comp
      (MonoidHom.codRestrict ((GlobalTheory.TopStep.redGL _ P.1).comp (Subgroup.inclusion hint)) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrG (B.R.m - 1) b ⟨P.1, hP⟩ ⟨_, hH g hg⟩ g r (by rw [hb]; exact hr) hrx
      (fun x hx => GlobalTheory.TopStep.redV_redGL ⟨g, hint hg⟩ hx)
    rw [hb] at hc
    exact hc.symm
  · classical
    have hQ := (Finset.mem_union.mp P.2).resolve_left hP
    have hH : ∀ g (hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1),
        (⟨g, hint hg⟩ : ↥(Formalism.L2.Col.GLint B.fields.E (B.R.N (B.R.m - 1)) P.1)) ∈ ((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).H := fun g hg => by
      rw [hL.grpQ _ b ⟨P.1, hQ⟩, hb]
      exact Subgroup.mem_subgroupOf.2 hg
    refine ⟨((I.idx a).levQ (B.R.m - 1) b ⟨P.1, hQ⟩).lam.comp
      (MonoidHom.codRestrict (Subgroup.inclusion hint) _ fun g => hH g.1 g.2), ?_⟩
    intro r hr g hg hrx
    have hc := hL.chrQ (B.R.m - 1) b ⟨P.1, hQ⟩ ⟨⟨g, hint hg⟩, hH g hg⟩ r (by rw [hb]; exact hr) hrx
    rw [hb] at hc
    exact hc.symm

theorem midLev_mul_beforeLast : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (g g' : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z z' : B.fields.K), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g z → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 g' z' → GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 (g * g') (z * z') := by
  intro B X I hOk a P g g' z z' ⟨r, hr, hrx, hz⟩ ⟨r', hr', hrx', hz'⟩
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  have hg : g ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r, hr, hrx⟩
  have hg' : g' ∈ prCat (Pr := B.primes X) (R := B.R) (I.cst a).sharp (B.R.m - 1) P.1 1 := ⟨r', hr', hrx'⟩
  have hrr : ∀ x, (r * r') (Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) x) =
      Loc.inX B.fields.E (B.R.N (B.R.m - 1)) (cOf B.R (B.R.m - 1)) ((g * g') x) := fun x => by
    rw [LinearEquiv.mul_apply, hrx', hrx]
    rfl
  refine ⟨r * r', mul_mem hr hr', hrr, ?_⟩
  rw [hz, hz', hφ r hr g hg hrx, hφ r' hr' g' hg' hrx', hφ (r * r') (mul_mem hr hr') (g * g') (mul_mem hg hg') hrr,
    ← Units.val_mul, ← map_mul]
  rfl

theorem midLev_one_last : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a), GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 1) P 1 1 1 := by
  intro B X I hOk a P
  obtain ⟨φ, hφ⟩ := chiInv_last_eq_char I hOk a P
  refine ⟨1, one_mem _, fun x => rfl, ?_⟩
  rw [hφ 1 (one_mem _) 1 (one_mem _) (fun x => rfl)]
  exact (congrArg Units.val (map_one φ)).symm

theorem nearV_one_one {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (P : SBof I a) : NearV I l Z a v P 1 1 := by
  unfold NearV GlobalTheory.TwU.NearAt
  erw [map_one (GlobalTheory.TwU.seamGL (sm I l Z)), map_one, map_one, inv_one, one_mul]
  exact GlobalTheory.TwU.congAt_one _ _

open Classical in
theorem valV_factor {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (P : SBof I a) (g : Sp B.fields.E (B.R.N (B.R.m - 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N (B.R.m - 1))) (z : B.fields.K)
    (hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) (hn : NearPair I l Z a v P x g z) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = z := by
  rw [dite_eq_left ⟨hP, g, z, hn⟩]
  exact GlobalTheory.Mem.Col2.QChi.nearPair_val_unique I hOk l Z a v P x _ g _ z (Exists.choose_spec (Exists.choose_spec (⟨hP, g, z, hn⟩ : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z).2)) hn

open Classical in
theorem valV_factor_off {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (x : GL (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N (B.R.m - 1))) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E ⊗[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F] v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))
    (P : SBof I a) (hP : ¬ IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)) :
    (if h : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) ∧ ∃ g z, NearPair I l Z a v P x g z then h.2.choose_spec.choose else 1) = 1 :=
  dif_neg fun h => hP h.1

theorem valV_mul : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), GlobalTheory.Mem.Col2.QChi.valV I l Z a v 1 = 1 ∧ ∀ x y, x ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → y ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v → GlobalTheory.Mem.Col2.QChi.valV I l Z a v (x * y) = GlobalTheory.Mem.Col2.QChi.valV I l Z a v x * GlobalTheory.Mem.Col2.QChi.valV I l Z a v y := by
  intro B X I hOk l Z a v
  constructor
  · unfold valV
    rw [Finset.prod_eq_one, map_one]
    intro P _
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · exact valV_factor I hOk l Z a v 1 P 1 1 hP ⟨midLev_one_last I hOk a P, nearV_one_one I l Z a v P⟩
    · exact valV_factor_off I l Z a v 1 P hP
  · intro x y hx hy
    unfold valV
    rw [← map_mul, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
    by_cases hP : IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)
    · have hx' : ∃ g z, NearPair I l Z a v P x g z := hx P hP
      have hy' : ∃ g z, NearPair I l Z a v P y g z := hy P hP
      obtain ⟨g, z, hgz⟩ := hx'
      obtain ⟨g', z', hgz'⟩ := hy'
      have hxy : NearPair I l Z a v P (x * y) (g * g') (z * z') := ⟨midLev_mul_beforeLast I hOk a P g g' z z' hgz.1 hgz'.1, nearV_mul_pairs I hOk l Z a v P x y g g' z z' hgz hgz'⟩
      rw [valV_factor I hOk l Z a v (x * y) P _ _ hP hxy, valV_factor I hOk l Z a v x P _ _ hP hgz, valV_factor I hOk l Z a v y P _ _ hP hgz']
    · rw [valV_factor_off I l Z a v (x * y) P hP, valV_factor_off I l Z a v x P hP, valV_factor_off I l Z a v y P hP, mul_one]

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PenultimateChartLocalGroupMemNearLevelSet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.QChi.NearLev

def triv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) :
    StepLevel F E σ J T f bad :=
  { S with chi := 1, chi_triv := fun _ _ => rfl }

theorem chiFin_triv {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {T i : ℕ} {hi : i ≤ B.R.m}
    {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) :
    ChiFin I l Z (triv S) :=
  ⟨1, one_pos, fun _ _ => by simp only [triv, pow_one]; rfl⟩


set_option maxHeartbeats 16000000 in
theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (κ : (K (chOf c)).lev.U), ∃ x : (K (chOf c)).lev.U, (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  classical
  have : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) = UAd B.sp.cm (B.R.N i) := by rw [hg]; rfl
  set y : GA B (B.R.N i) := ((K (chOf c)).y ⟨c, rfl⟩).1 with hy
  set kk : GA B (B.R.N i) := k (chOf c) with hkk
  have hsel : ∀ P : SBof I a, ∃ z : (K (chOf c)).lev.U,
      (∀ P' : SBof I a, P' ≠ P → ∀ r s, adAt B.host.F P'.1 (((show GA B (B.R.N i) from z.1) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = (1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P'.1.adicCompletion B.fields.E)) r s) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) z.1 ∧
      (P.1 ∈ I.Q a → ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 ((((y * (show GA B (B.R.N i) from κ.1)) * (show GA B (B.R.N i) from z.1) * kk : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) := by
    intro P
    by_cases hP : P.1 ∈ I.Q a
    · obtain ⟨v, hv, hv'⟩ := LevelElt.place_under I hOk hPins l Z a P hP
      obtain ⟨z, -, hz2, hz3, hz4⟩ := LevelElt.one_prime I hOk hPins l Z a _ i hi bad (triv (K (chOf c)).lev) (chiFin_triv I l Z _) P hP v hv ((I.cst a).D P) (y * (show GA B (B.R.N i) from κ.1)) kk
      refine ⟨⟨z.1, z.2⟩, fun P' hP' r s => ?_, hz3, fun _ => hz4⟩
      have e := (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a (B.R.N i) 0 P' z.1).1
      have h2 := hv' P' hP'
      rw [e] at h2
      exact LevelElt.support_one z.1 v hz2 P'.1 h2 r s
    · refine ⟨1, fun P' _ r s => ?_, GlobalTheory.TwU.congAt_one _ _, fun h => absurd h hP⟩
      show adAt B.host.F P'.1 ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = _
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  choose zf hzf2 hzf3 hzf4 using hsel
  let cP : ∀ P : HeightOneSpectrum (𝓞 B.fields.E), GA B (B.R.N i) →* Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (P.adicCompletion B.fields.E) :=
    fun P => (RingHom.mapMatrix (adAt B.host.F P)).toMonoidHom.comp (Units.coeHom _)
  have cP_apply : ∀ P (g : GA B (B.R.N i)) r s, cP P g r s = adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) := fun _ _ _ _ => rfl
  let ι : (K (chOf c)).lev.U →* GA B (B.R.N i) := (K (chOf c)).lev.U.subtype
  have hone : ∀ P P' : SBof I a, P' ≠ P → cP P'.1 (ι (zf P)) = 1 := fun P P' h => Matrix.ext fun r s => by
    rw [cP_apply]; exact hzf2 P P' h r s
  have hlist : ∀ (L : List (SBof I a)), L.Nodup → ∀ P' : SBof I a, cP P'.1 (ι (L.map zf).prod) = if P' ∈ L then cP P'.1 (ι (zf P')) else 1 := by
    intro L
    induction L with
    | nil => intro _ P'; simp
    | cons P L ih =>
      intro hL P'
      rw [List.nodup_cons] at hL
      rw [List.map_cons, List.prod_cons, map_mul, map_mul, ih hL.2]
      by_cases h : P = P'
      · subst h
        simp [hL.1]
      · rw [hone P P' (Ne.symm h)]
        simp [Ne.symm h]
  obtain ⟨w, hw⟩ : ∃ w : (K (chOf c)).lev.U, w = ((Finset.univ : Finset (SBof I a)).toList.map zf).prod := ⟨_, rfl⟩
  have hwP : ∀ P : SBof I a, cP P.1 (ι w) = cP P.1 (ι (zf P)) := fun P => by
    rw [hw, hlist _ (Finset.nodup_toList _) P, if_pos (Finset.mem_toList.2 (Finset.mem_univ _))]
  have hpt : ∀ g : GA B (B.R.N i), g ∈ UAd B.sp.cm (B.R.N i) → (∀ P ∈ I.Q a, ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P ((g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s)) → ∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf g q :=
    fun g hg hr => LevelElt.point_of_rat B.sp.cm _ _ _ g hg hr
  have hQsub : ∀ P ∈ I.Q a, P ∈ SBof I a := fun P hP => by
    show P ∈ uSG _ _
    exact Finset.mem_union_right _ hP
  obtain ⟨p0, hp0, -⟩ := hR.k_std (chOf c)
  refine ⟨κ * w, ?_, ?_⟩
  ·
    have hyU : y ∈ UAd B.sp.cm (B.R.N i) := eU ▸ ((K (chOf c)).y ⟨c, rfl⟩).2
    have hxU : (show GA B (B.R.N i) from (κ * w).1) ∈ UAd B.sp.cm (B.R.N i) := eU ▸ (((K (chOf c)).lev.U_eq _).1 (κ * w).2).1
    have hkU : kk ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
    refine hpt _ (mul_mem (mul_mem hyU hxU) hkU) fun P hP => ?_
    let P' : SBof I a := ⟨P, hQsub P hP⟩
    obtain ⟨γ, hγ⟩ := hzf4 P' hP
    refine ⟨γ, fun r s => ?_⟩
    have e1 := LevelElt.mul_comp_eq (cP P) y (show GA B (B.R.N i) from κ.1) (show GA B (B.R.N i) from w.1) (show GA B (B.R.N i) from (zf P').1) kk (hwP P')
    have e2 := congrFun (congrFun e1 r) s
    exact (cP_apply P _ r s).symm.trans (e2.trans ((cP_apply P _ r s).trans (hγ r s)))
  · intro P
    have e : κ.1⁻¹ * (κ * w).1 = w.1 := inv_mul_cancel_left κ.1 w.1
    refine (congrArg (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P)) e).mpr ?_
    refine ((_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a (B.R.N i) ((I.cst a).D P) P w.1).2.2).mpr fun r s => ?_
    have e := LevelElt.entry_eq_of_eq (cP P.1) _ _ (hwP P) r s
    have D2 := ((_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a (B.R.N i) ((I.cst a).D P) P (zf P).1).2.2.1 (hzf3 P)) r s
    convert D2 using 3
    exact e


set_option maxHeartbeats 4000000 in
theorem exists_stepElt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (κ : (K (chOf c)).lev.U), ∃ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) ∧ ∀ (P : SBof I a) (f : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((show GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from k (chOf c))⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F f) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F f)⁻¹ * (show GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) from k (chOf c))) → ∀ (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), LiftsInv I κ' P g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) (fun _ : SBof I a => f) (I.cst a).D P κ.1 g := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  obtain ⟨x, ⟨q, hq⟩, hxκ⟩ := exists_level_elt I hOk hPins l Z u a i hi bad Ch chOf K k hR c κ
  have hl := hR.lev c x.1 q hq
  have hx : x.1 ∈ (fun β => (K β).lev.U) (chOf c) := x.2
  obtain ⟨κ', h3⟩ := hl.mp hx
  refine ⟨κ', ⟨h3.1, h3.2.2⟩, fun P f he hei g hL => ?_⟩
  obtain ⟨hm1, hm2, hn⟩ := GlobalTheory.T.levelElement_at_bad_primes_integral_and_near I hOk l Z u a i hi bad Ch chOf K k hR c x.1 κ' h3.1 (h3.2.1 ▸ hq) P
  obtain ⟨p, hp, hpN⟩ := hR.k_std (chOf c)
  exact GlobalTheory.T.adelicMatrixCongruence_move_rational_frame _ _ κ.1 x.1 (k (chOf c)) f _ (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).1)
    (fun r s => (GlobalTheory.T.stdPointMatrix_and_inverse_integral_at_every_prime _ _ p hp hpN _ r s).2) hm1 hm2 (hxκ P) (hn g hL) he hei

end GlobalTheory.Mem.Col2.QChi.NearLev

namespace GlobalTheory.Mem.Col2.QChi

theorem idx_h_last_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ (j : ℕ), j = B.R.m - 2 + 1 → ∀ (b : (I.idx a).β j) (P : SBof I a), (I.idx a).h j b P = 1 := by
  intro j hj
  subst hj
  exact (hOk.idx_ok a).last_h


set_option maxHeartbeats 4000000 in
theorem mem_nearSet_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), x.1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g hQ _ _ hk _ _ Lb0 _ v hv β x
  obtain ⟨k, hR, hk1⟩ := hk
  have hm : B.R.m - 1 < B.R.m := by omega
  have hm2 : B.R.m - 1 = B.R.m - 2 + 1 := by have := hOk.hm; omega
  obtain ⟨c, rfl⟩ := hR.onto β
  intro P hPv
  let κ : (K (chOf c)).lev.U := GlobalTheory.Mem.Col2.ChartLevel.embU (K (chOf c)).lev v x
  obtain ⟨κ', -, hκ'⟩ := NearLev.exists_stepElt I hOk hPins l Z u a (B.R.m - 1) (Nat.sub_le _ _) (badQ (I.rec7 l Z) Q) Ch chOf K k hR c κ
  obtain ⟨g', z, hMid, hL⟩ := _root_.GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv I hOk u a (B.R.m - 1) hm c.1 κ' P
  let kk : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E) := k (chOf c)
  have hv1 : bc (prV (E := (I.rec7 l Z).host.E) v) kk = 1 := hk1 (chOf c) v ((hQ v).1 hv)
  have he : GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (kk⁻¹ * 1) :=
    GlobalTheory.AwayFr.congAt_of_prV_eq v _ hPv ((I.cst a).D P) kk 1 ((map_one _).trans hv1.symm)
  have hei : GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (1⁻¹ * kk) :=
    GlobalTheory.AwayFr.congAt_of_prV_eq v _ hPv ((I.cst a).D P) 1 kk (hv1.trans (map_one _).symm)
  have hIF := hκ' P 1 (by rw [map_one]; exact he) (by rw [map_one]; exact hei) g' hL
  refine ⟨g', z, ?_, ?_⟩
  · have h := hMid
    unfold MidAt at h
    rw [idx_h_last_step I hOk a _ hm2] at h
    exact h
  · unfold GlobalTheory.TwU.InFrame at hIF
    rw [map_one, inv_one, one_mul, mul_one] at hIF
    exact hIF

end GlobalTheory.Mem.Col2.QChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRelationPreservesLevelFormLatticeNormStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Rows
open scoped TensorProduct InnerProductSpace ComplexOrder
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRelation_preserves_levelForm_lattice_norm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ} {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) (e : Df.MtCx I a ≃ₗ[ℂ] s.A.T), (∀ y, IsCrd I hX a e (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y)) → ∀ x : (Df.MtHL I hX a).V, Formalism.HermitianLatticesTheory.normAt (Df.MtHL I hX a).b (Df.MtHL I hX a).X (InfinitePlace.mk X.B.embLL) x = ‖e (Df.toCx I hX a x)‖ := by
  first | exact @GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie | exact GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie | (intros; apply GlobalTheory.Mem.R3.Rw.NormTie.normAt_eq_norm_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverFixedFieldSameCoefficientPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.Top.Bl

theorem below_of_overOne : ∀ (D D' : D7), (∀ x : D.what₂.LL, ∃ y ∈ D'.LL0, D'.what₂.embLL y = D.what₂.embLL x) → ∀ (v : D.what₂.places.Pl) (v₁ v₂ : D'.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D' v₁ v₂ → Below D D' v v₁ → Below D D' v v₂ := by
  intro D D' hsub v v₁ v₂ h12 hb x x' hxx'
  rw [hb x x' hxx']
  obtain ⟨y, hy, hye⟩ := hsub (x : D.what₂.LL)
  have hyx : y = (x' : D'.what₂.LL) := D'.what₂.embLL.injective (hye.trans hxx')
  have hint : IsIntegral ℤ (⟨(x' : D'.what₂.LL), hyx ▸ hy⟩ : ↥D'.LL0) :=
    (isIntegral_algebraMap_iff ).1 (RingOfIntegers.isIntegral_coe x')
  let z : 𝓞 ↥D'.LL0 := ⟨⟨(x' : D'.what₂.LL), hyx ▸ hy⟩, hint⟩
  have hz : algebraMap (𝓞 ↥D'.LL0) (𝓞 D'.what₂.LL) z = x' := by
    apply RingOfIntegers.ext
    rfl
  rw [← hz, ← GlobalTheory.TwistChoice.val_pos_iff_mem, ← GlobalTheory.TwistChoice.val_pos_iff_mem]
  exact h12 z

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix

namespace GlobalTheory.SeeSaw.TwLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def RatAt (Q : Finset (HeightOneSpectrum (𝓞 E))) : Set (GL (Fin n) (AfE F E)) :=
  {z | ∀ P : Q, ∀ i j, ∃ e : E, adAt F P.1 ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ e}

variable [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))}


variable (hc : CMData F E) in
def RdLevOn {K : Type} [Field K] (A : Set (GL (Fin n) (AfE F E))) (U : Subgroup (GL (Fin n) (AfE F E))) (chi : U →* ℂˣ)
    (Λ : LevFam E K n SG) (emb : K →+* ℂ) (Q : Finset (HeightOneSpectrum (𝓞 E)))
    (HQ : ∀ P : Q, Subgroup (GL (Fin n) (𝓞 E ⧸ P.1.asIdeal))) (lamQ : ∀ P : Q, HQ P →* ℂˣ) : Prop :=
  ∀ z ∈ A, ∀ hz : z ∈ St (1 : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    (z ∈ U ↔ (∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) ∧ ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P) ∧
      ∀ (hU : z ∈ U) (h : ∀ w : SG, redAt 1 w.1 ⟨z, hz⟩ ∈ (Λ w).H) (h' : ∀ P : Q, redAt 1 P.1 ⟨z, hz⟩ ∈ HQ P),
        ((chi ⟨z, hU⟩ : ℂˣ) : ℂ) =
          (∏ w : SG, (emb (((Λ w).lam ⟨_, h w⟩ : Kˣ) : K))⁻¹) * ∏ P : Q, ((lamQ P ⟨_, h' P⟩ : ℂˣ) : ℂ)

end GlobalTheory.SeeSaw.TwLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharEqOfOverOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.SatForced

theorem resChar_eq_of_overOne (D : D7) {v v' : D.what₂.places.Pl} (h : GlobalTheory.TwistChoice.OverOne D v v') :
    D.what₂.places.resChar v = D.what₂.places.resChar v' := by
  have hp := D.what₂.places.resChar_prime v
  have h1 := GlobalTheory.TwistChoice.val_resChar_pos D v
  have h2 := (h ((D.what₂.places.resChar v : ℕ) : 𝓞 ↥D.LL0)).1 (by simpa using h1)
  exact GlobalTheory.TwistChoice.eq_resChar_of_pos D v' hp (by simpa using h2)

theorem mem_W1F_of_overOne : ∀ (K : Ctx) (D : D7) (v v' : D.what₂.places.Pl), GlobalTheory.TwistChoice.OverOne D v v' →
    v ∈ placesWithNonzeroContentOrConj D (F0K K.s D) → v' ∈ placesWithNonzeroContentOrConj D (F0K K.s D) := by
  intro K D v v' h hv
  obtain ⟨j, y, hy, hne⟩ := hv
  have key : D.what₂.places.resChar (D.plEq.symm y) = D.what₂.places.resChar v := by
    rcases hy with e | e
    · rw [e, Equiv.symm_apply_apply]
    · rw [e]; exact GlobalTheory.Mem.NonzeroPlacesOverPrimes.resChar_symm_conjPl D v
  refine ⟨j, D.plEq v', Or.inl rfl, ?_⟩
  have e2 : F0K K.s D (D.plEq v') j = F0K K.s D y j := by
    unfold F0K
    rw [key, Equiv.symm_apply_apply, resChar_eq_of_overOne D h]
  rw [e2]; exact hne

end GlobalTheory.Mem.SatForced
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowBasisCongruenceLengthsOtherLaterStages
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.R3.Rw.rr_eta_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m) (R : RealDat3 a.D A3 Ks) (F : Face3 a.D A3), letI := alg b iK; (∀ j v, etaOf (real3 b R) (face3 b F) j v = etaOf R F j ((v))) ∧ ∀ (y : Hd R.toRealDat) (y' : Hd (real3 b R).toRealDat) (bb : Bool) (E : Hs) jE jE' n c Xo, HEq jE' jE → RrT F y bb (E := E) jE n c Xo → RrT (face3 b F) y' bb (E := E) jE' n c ((Xo)) := by
  intro B C a b G _ _ Pl0 I0 T Ks _ _ iK A3 R F
  letI := alg b iK
  refine ⟨fun j v => ?_, fun y y' bb E jE jE' n c Xo hj h => ?_⟩
  · classical
    exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A3.fam3.amb3 => (
        if hj : 1 ≤ j ∧ j ≤ a.D.R.m then
          if a.D.plEq (((v :))) ∈ R.twPl then
            A3.A.fam.etaJ F.P0 F.ψ0 (A3.fam3.toSub2 X.zs) ⟨j - 1, by omega⟩ (R.mu (a.D.plEq (((v :))))) (a.D.plEq (((v :))))
          else 0
        else 0) = etaOf R F j ((by with_unfolding_all exact (v :)))) (toCx3_eq b R F)) (by with_unfolding_all rfl)) :))
  · have e : jE' = jE := eq_of_heq hj
    subst jE'
    exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun u : Parts R => ∃ h : n = ((cxW R F u).data F.cr bb).D,
      (∀ x : Fin n → a.D.what₂.LL, jE (∑ i, a.D.what₂.embLL (x i) • c i) =
        PiTensorProduct.lift (R.HE.e (Tw.out (s := twAt a.D.what₂.embLL A3.A.v0) (E := R.HE.H)
          ((cxW R F u).iC F.cr bb A3.A.μ0 (cpt A3.A.v0.embedding (x ∘ Fin.cast h.symm)))))) ∧
      ∀ v, Xo v = (((cxW R F u).data F.cr bb).XE v).submatrix (Fin.cast h) (Fin.cast h) ∧ IsUnit (Xo v).det) (parts_eq b R F)) h) :))

end
end

