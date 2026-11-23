module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
public import Formalism.LocalToGlobal.Columns.Bundle0026
public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Formalism.LocalToGlobal.Columns.RecLevelLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTopRowSym
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeLev

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def badB (B : Base) : Set (HeightOneSpectrum (𝓞 B.host.F)) :=
  {v | (B.host.g 0 : 𝓞 B.host.F) ∈ v.asIdeal ∨ (B.host.g 1 : 𝓞 B.host.F) ∈ v.asIdeal}

theorem mem_badB {v : HeightOneSpectrum (𝓞 B.host.F)} : v ∈ badB B ↔ ∃ j, (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal := by
  rw [Fin.exists_fin_two]; rfl

theorem not_mem_both {A : Type} [CommRing A] {P : Ideal A} (hP : P.IsPrime) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    (a : (p : A) ∈ P) (b : (q : A) ∈ P) : False := by
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 h)).map (Int.castRingHom A)
  refine hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by simpa using a)) (Ideal.mul_mem_left _ _ (by simpa using b))

theorem T_notMem (hPr : (B.primes X).Ok) (u : B.Word) {v : HeightOneSpectrum (𝓞 B.host.F)} (hv : v ∈ badB B) :
    (B.T u : 𝓞 B.host.F) ∉ v.asIdeal := fun h => by
  obtain ⟨j, hj⟩ := mem_badB.1 hv
  exact not_mem_both v.isPrime (hPr.T_prime u) (hPr.g_prime j) (hPr.T_ne_g u j) h hj

theorem piT_dvd (hPr : (B.primes X).Ok) (u : B.Word) :
    X.piT u ∣ algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) := by
  rw [map_natCast]
  exact ⟨_, (hPr.piT_norm u).symm⟩

theorem under_notMem (hPr : (B.primes X).Ok) (u : B.Word) {P : HeightOneSpectrum (𝓞 B.host.E)} (h : X.piT u ∈ P.asIdeal) :
    underPl B.host.F P ∉ badB B := fun hv =>
  T_notMem hPr u hv (Ideal.mem_comap.2 (Ideal.mem_of_dvd _ (piT_dvd hPr u) h))

local instance isEmpty_Q : IsEmpty (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; infer_instance

local instance neZero_top (R : Ranks) : NeZero (R.N R.m) := ⟨by have := N_m_succ R; omega⟩

local instance neZero_rankPred (R : Ranks) : NeZero (R.N R.m - 1) := ⟨by have := rank_X'_eq R; have := rSym_rSD R; unfold rSym at this; omega⟩


set_option maxHeartbeats 1000000 in
theorem rdM (hPr : (B.primes X).Ok) (u : B.Word) {Lb U chi y st k}
    (h : I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k) (c : (I.stp u I.mu0 B.R.m).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi (badB B) (levGTop I.Ch I.Ps) B.embLL := by
  have hd : Disjoint (B.primes X).vGs (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; exact Finset.disjoint_empty_right _
  have h0 : ∀ q : (I.stp u I.mu0 B.R.m).D c.1, cosetIn q = fun _ => ∅ := fun q => by
    have h1 := q.2
    rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)] at h1
    funext P
    unfold cosetIn
    rw [Set.mem_singleton_iff.1 h1]
    simp
  have := rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := badB B)
    (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1) (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1)
    B.embLL (U := U) (chi := chi) (IsPtOf.of_extTo (I.Q_subset_SQ _) hd (h.pt c))
    (fun v hv => h.k_off () v (T_notMem hPr u hv) (fun ⟨P, hP, _⟩ => isEmptyElim (⟨P, hP⟩ : I.Q I.mu0)) (Or.inl rfl))
    (fun P hP => under_notMem hPr u ((mem_divs (fun e => (hPr.T_prime u).ne_zero (by
      have := hPr.piT_norm u
      rw [show (B.primes X).piT u = 0 from e, zero_mul] at this
      exact Nat.cast_eq_zero.1 this.symm)) P).1 hP))
    (fun x q hq => (h.lev c x q hq).trans (exists_congr fun κ => and_congr_right fun _ => and_iff_left ((h0 _).trans (h0 _).symm)))
    (fun x κ h1 h2 => h.chr c x κ h1 h2)
  rwa [levGAt_of_le _ _ _ _ le_rfl, topLev_levG_m] at this


set_option maxHeartbeats 1000000 in
theorem rdP {Lb U chi y lat st} (h : I.ReadsP I.mu0 Lb U chi y lat st) (c : (I.stX I.mu0).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi (badB B) (rowTyG I.Ch I.Ps) B.embLL :=
  rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := badB B) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup I.mu0))
    B.embLL (U := U) (chi := chi) (y := y c) (k := 1) (p := ((I.stX I.mu0).rep c).1.1) (by rw [mul_one]; exact h.pt c)
    (fun v _ => map_one _) (fun P hP => absurd hP (Finset.notMem_empty _))
    (fun x q hq => h.lev c x q (by rwa [mul_one] at hq))
    (fun x κ h1 h2 => h.chr c x κ h1 (by rwa [mul_one] at h2))

theorem cmp_base (hPr : (B.primes X).Ok) (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG) :
    Nonempty (Cmp G (B.primes X).vGs) := by
  classical
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∀ w, w ∈ (B.primes X).vGs ↔ ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := fun w => by
    unfold Primes.vGs Primes.vG
    simp only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two]
  refine nonempty_cmp B.host B.sp.cm (levOk_base B X) G hPr.g_ne (fun w hw => ?_) fun j w hw => (hm w).2 ⟨j, ?_⟩
  · obtain ⟨i, hi⟩ := (hm w).1 hw
    exact ⟨i, (hPr.piG_norm i) ▸ Ideal.mul_mem_left _ _ hi⟩
  · rw [hG] at hw
    exact hw

theorem exists_nat (hPr : (B.primes X).Ok) (w : (B.primes X).vGs) (c : 𝓞 B.fields.E ⧸ w.1.asIdeal) : ∃ n : ℕ, c = n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w.1 ∈ (B.primes X).vG i := by
    rw [Fin.exists_fin_two]
    exact Finset.mem_union.1 w.2
  have hc : Nat.card (𝓞 B.fields.E ⧸ w.1.asIdeal) = (B.primes X).g i := by
    rw [← hPr.vG_norm i _ hi, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have := Fact.mk (hPr.g_prime i)
  have : Nontrivial (𝓞 B.fields.E ⧸ w.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.1.isPrime.ne_top
  have : Finite (𝓞 B.fields.E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have h := zmultiples_eq_top_of_prime_card hc (one_ne_zero (α := 𝓞 B.fields.E ⧸ w.1.asIdeal))
  obtain ⟨n, hn⟩ := mem_multiples_iff_mem_zmultiples.2 (h ▸ AddSubgroup.mem_top c : c ∈ AddSubgroup.zmultiples (1 : 𝓞 B.fields.E ⧸ w.1.asIdeal))
  exact ⟨n, by simpa using hn.symm⟩


set_option maxHeartbeats 1000000 in
theorem main_base (hPr : (B.primes X).Ok) (u : B.Word) (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG)
    (hψ : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal)))
    (hχ : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ (s : Fin B.R.m) (n : ℕ)
      (c : (𝓞 B.fields.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 B.fields.E ⧸ w.1.asIdeal) = n →
      G.chiB j v h s.1 (n : kv B.host.F v) = B.embLL ((I.Ch.chi s w c : B.LLˣ) : B.LL))
    {J J' T T' f f'} (hJ : J = 1) (hJ' : J' = 1) (S : StepLevel B.host.F B.host.E B.sp.cm.sig (n := B.R.N B.R.m) J T f (badB B))
    (S' : StepLevel B.host.F B.host.E B.sp.cm.sig (n := B.R.N B.R.m - 1) J' T' f' (badB B))
    (hL : ∀ x, x ∈ S.Lb ↔ x ∈ baseL B _ (X.piT u)) (hL' : ∀ x, x ∈ S'.Lb ↔ x ∈ baseL B _ 1)
    (hR : RdLev (E := B.fields.E) B.sp.cm S.U S.chi (badB B) (levGTop I.Ch I.Ps) B.embLL)
    (hR' : RdLev (E := B.fields.E) B.sp.cm S'.U S'.chi (badB B) (rowTyG I.Ch I.Ps) B.embLL) :
    ∃ lamM lamP, ∃ (VM : GLevH S G (fun _ v _ => JSymG (kv B.host.F v) _ B.R.k (rSD B.R) B.R.t true) lamM)
      (VP : GLevH S' G (fun _ v _ => JSymG (kv B.host.F v) _ B.R.k (rSD B.R) B.R.t false) lamP),
      (∀ j v h M, ((lamM j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧
      (∀ j v h M, ((lamP j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧
      (∀ j v h, VP.fr j v h = 1) ∧ ∀ j v h, (VM.fr j v h).1 = diagonal fun i => if i.1 + 1 = B.R.N B.R.m then
        G.phi j v h (inclE (F := B.host.F) (v.adicCompletion B.host.F) (X.piT u : B.host.E)) else 1 := by
  obtain ⟨C⟩ := cmp_base hPr G hG
  have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := (rSym_rSD B.R).symm
  have ht : 0 < B.R.t := B.R.t_odd.pos
  have hn := rank_X'_eq B.R
  have hN := N_m_succ B.R
  have e1 : ∀ j v h x, G.psi0 j v h ((C.e j v h).toRingHom x) = B.embLL (I.Ch.psi0 (C.W j v h) x) := fun j v h x => by
    obtain ⟨n, rfl⟩ := exists_nat hPr _ x
    rw [map_natCast]
    exact hψ j v h _ (C.ov j v h) n
  have e2 : ∀ j v h s, s < B.R.m → ∀ c : (𝓞 B.fields.E ⧸ (C.W j v h).1.asIdeal)ˣ, G.chiB j v h s ((C.e j v h).toRingHom c) =
      B.embLL ((chiAt I.Ch (C.W j v h) s c : B.LLˣ) : B.LL) := fun j v h s hs c => by
    obtain ⟨n, hn⟩ := exists_nat hPr _ c.1
    rw [hn, map_natCast, show chiAt I.Ch (C.W j v h) s = I.Ch.chi ⟨s, hs⟩ (C.W j v h) from dif_pos hs]
    exact hχ j v h _ (C.ov j v h) ⟨s, hs⟩ n c hn
  have hM := fun j v h => by
    letI := (C.W j v h).1.isMaximal
    letI := Ideal.Quotient.field (C.W j v h).1.asIdeal
    exact exists_lam (k := B.R.k) (rS := rSD B.R) (t := B.R.t) (zl := true) (C.e j v h) B.embLL (levGTop I.Ch I.Ps (C.W j v h))
      (lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m)
      (by rw [levGTop_PsymF]; exact GlobalTheory.MemXSym.memX _ _ _ _ _ _ _ _ hr ht (by omega))
      (by
        rw [levGTop_PsymF]
        exact fun M => GlobalTheory.LamRead.lamJsym_read _ _ _ (C.e j v h).toRingHom B.embLL _ _ _ _ _ _ _ _ _ _ _ hr ht (by omega)
          (e1 j v h) (e2 j v h) ⟨M.1, M.2.1⟩)
  have hP := fun j v h => by
    letI := (C.W j v h).1.isMaximal
    letI := Ideal.Quotient.field (C.W j v h).1.asIdeal
    exact exists_lam (k := B.R.k) (rS := rSD B.R) (t := B.R.t) (zl := false) (C.e j v h) B.embLL (rowTyG I.Ch I.Ps (C.W j v h))
      (lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m)
      (GlobalTheory.mem_HJsym_iff_JSymG _ _ _ _ _ _ _ _ hr ht hn)
      (fun M => GlobalTheory.LamRead.lamJsym_read _ _ _ (C.e j v h).toRingHom B.embLL _ _ _ _ _ _ _ _ _ _ _ hr ht hn.ge
          (e1 j v h) (e2 j v h) M)
  choose lamM m1 m2 m3 using hM
  choose lamP p1 p2 p3 using hP
  have hu : ∀ j v h, IsUnit (C.ρ j v h (oToS B.host.F B.host.E (X.piT u))) := fun j v h => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, C.e_eq, resS_oToS, map_ne_zero_iff _ (C.e j v h).injective, Ne,
      Ideal.Quotient.eq_zero_iff_mem]
    intro h'
    refine under_notMem hPr u h' ?_
    rw [C.ov]
    exact mem_badB.2 ⟨j, h⟩
  obtain ⟨VM, hVM⟩ := exists_gLevH hJ S C (fun _ => mem_badB)
    (fun v hv => locL_eq v hL (T_notMem hPr u hv) (piT_dvd hPr u)) hR _ lamM (fun j v h => lastDiag _ (hu j v h).unit) m2 m3
    fun j v h M hM => lastDiag_commute _ _ hM
  obtain ⟨VP, hVP⟩ := exists_gLevH hJ' S' C (fun _ => mem_badB)
    (fun v hv => locL_eq v hL' (T_notMem hPr u hv) (one_dvd _)) hR' _ lamP (fun j v h => 1) p2 p3
    fun j v h M hM => by rw [map_one]; exact Commute.one_left _
  refine ⟨lamM, lamP, VM, VP, m1, p1, fun j v h => by rw [hVP, map_one], fun j v h => ?_⟩
  rw [hVM]
  refine (Matrix.diagonal_map (map_zero _)).trans (congrArg diagonal (funext fun i => ?_))
  split_ifs
  · refine (C.ρ_eq j v h _).trans (congrArg _ ?_)
    exact Formalism.UG.P.afsplit_prV_inclE v _
  · exact map_one _

theorem frExt_of {D : D7} (hiX : ∀ x j, iXc D x j = if h : j.1 < D.R.N D.R.m - 1 then x ⟨j.1, h⟩ else 0) (p : D.host.E)
    (G : GLoc D.host.F D.host.E (sigD D) D.host.g) {frm frp} (h3 : ∀ j v h, frp j v h = 1)
    (h4 : ∀ j v h, Units.val (frm j v h) = diagonal fun i : Fin (D.R.N D.R.m) => if i.1 + 1 = D.R.N D.R.m then
      G.phi j v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) p) else 1) :
    FrExtFr (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then p else 0) G frm frp := by
  refine fun j v h => ⟨fun x b b' hb => ?_, fun x t ht => ?_⟩
  · have hb2 := b.2
    rw [h3, h4, Units.val_one, Matrix.mul_one, Matrix.map_apply, iXm, LinearMap.toMatrix'_apply, hiX, diagonal_apply]
    by_cases hx : x = b'
    · subst hx
      rw [if_pos rfl, if_neg (by omega), dif_pos (hb ▸ hb2), Pi.single_apply, if_pos (Fin.ext hb.symm), map_one]
    · rw [if_neg hx]
      split_ifs with h5
      · rw [Pi.single_apply, if_neg (fun e : (⟨x.1, h5⟩ : Fin _) = b => hx (Fin.ext ((congrArg Fin.val e).trans hb))), map_zero]
      · rw [map_zero]
  · rw [h4, diagonal_apply]
    beta_reduce
    by_cases hx : x = t
    · subst hx
      rw [if_pos rfl, if_pos ht, if_pos ht]
    · rw [if_neg hx, if_neg fun e => hx (Fin.ext (by omega)), map_zero, map_zero]

end GlobalTheory.Mem.Col2.TypeLev

end


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.levels_top_row_sym : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (KP : ClsPTied (D := (I.rec7 l Z)) u), I.IdG l Z G → (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) → ∃ (lamM : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → HSym (I.rec7 l Z) (B.R.N B.R.m) true v →* ℂˣ) (lamP : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → HSym (I.rec7 l Z) (B.R.N B.R.m - 1) false v →* ℂˣ) (VM : GLevH K.lev G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N B.R.m) true v) lamM) (VP : GLevH KP.lev G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N B.R.m - 1) false v) lamP), (∀ j v h M, ((lamM j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧ (∀ j v h M, ((lamP j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧ (∀ j v h, VP.fr j v h = 1) ∧ FrExtFr (D := (I.rec7 l Z)) (fun j => if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) G VM.fr VP.fr := by
  intro B X I hI hP l Z u G K KP hG ⟨k, hK⟩ hKP
  obtain ⟨-, gP, hiX, hN⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨c, -⟩ := K.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨c', -⟩ := KP.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨lamM, lamP, VM, VP, h1, h2, h3, h4⟩ := TypeLev.main_base I l.pr u G hG.piG hG.psi hG.chi (hN _ le_rfl).1 gP K.lev KP.lev
    (hK.lb ()) hKP.lb (TypeLev.rdM I l.pr u hK c) (TypeLev.rdP I hKP c')
  exact ⟨lamM, lamP, VM, VP, h1, h2, h3, TypeLev.frExt_of (D := I.rec7 l Z) hiX _ G h3 h4⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymFrame

variable {D : D7}

def EwAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ y ∈ X.B.I.Lf, (1 - X.ew) • y ∈ wLf X w


open Classical in
def epsW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.k → VA X.B.I :=
  if EwAt X w then X.bw else fun i => X.bwd (Fin.rev i)

def symVec (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Fin D.R.r → VA X.B.I :=
  GlobalTheory.SeeConjRead.flagV D.R.rS D.R.k D.R.r X.e0 X.f0 (epsW X w) X.z0

def IsMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} (u : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf)
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) : Prop :=
  ∀ i, X.B.I.fmat x *ᵥ u i - ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • u j ∈ wLf X w

end GlobalTheory.Mem.SymFrame

end

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_perm {D : D7} {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    (s : Fin D.R.r → VA X.B.I) (x : X.B.I.Gf) (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)) (π : Equiv.Perm (Fin D.R.r))
    (hN : IsMatIn X w (fun j => s (π.symm j)) x N) : IsMatIn X w s x (N.submatrix π π) := by
  intro i
  have h1 := hN (π i)
  rw [← Equiv.sum_comp π] at h1
  simpa [Matrix.submatrix_apply] using h1

theorem mem_unipSym_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r ρ k : ℕ} (u : GL (Fin r) κ) :
    Formalism.UG.bc (f : κ →+* κ') u ∈ unipSym κ' r ρ k ↔ u ∈ unipSym κ r ρ k := by
  have e : ∀ i j, ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j =
      f ((u : Matrix (Fin r) (Fin r) κ) i j) := fun _ _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have := h1 hij; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
    · have := h2 i; rw [e] at this; exact f.injective (this.trans (map_one f).symm)
    · have := h3 i j ha hb hc; rw [e] at this; exact f.injective (this.trans (map_zero f).symm)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · show ((Formalism.UG.bc (f : κ →+* κ') u : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = 0
      rw [e, h1 hij, map_zero]
    · rw [e, h2 i, map_one]
    · rw [e, h3 i j ha hb hc, map_zero]

theorem edgeSum_bc {κ κ' : Type} [CommRing κ] [CommRing κ'] (f : κ ≃+* κ') {r : ℕ} (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (u : GL (Fin r) κ) : edgeSum Ed (Formalism.UG.bc (f : κ →+* κ') u) = f (edgeSum Ed u) := by
  unfold edgeSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · rw [map_zero]

end GlobalTheory.Mem.SymFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownPointPreservesIndexFramesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveDown_point_preserves_index_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F)), IsOver v P.1 → conjPrime₂ P.1 ≠ P.1 → IsOver v (conjPrime₂ P.1) → (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧ Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  first | exact @GlobalTheory.Mem.Col2.PtY.mv_dn_facts | exact GlobalTheory.Mem.Col2.PtY.mv_dn_facts | (intros; apply GlobalTheory.Mem.Col2.PtY.mv_dn_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionEqBasePiMulIntegralStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeProjection_eq_basePi_mul_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.L2.Herm.intAf F E → (∀ P ∈ ST, Valued.v (adAt F P z) < 1) → ∃ s ∈ intV E v, prV (E := E) v z = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s := by
  first | exact @GlobalTheory.Mem.Col2.prV_eq_pi_mul | exact GlobalTheory.Mem.Col2.prV_eq_pi_mul | (intros; apply GlobalTheory.Mem.Col2.prV_eq_pi_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtLat

theorem latS_deco_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q S k t y p ht hS hp x
  have hp0 : IsPtOf hc (y * (k * t)) (extTo ∅ p) :=
    hp.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)
  obtain ⟨hg, hd⟩ := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ _ _ rfl).1 hp0
  have hd' : p.deco.1 = decoRaw ST SG (y * (k * t)) := hd
  have hcar := decoRaw_carries hc n ST SG hg x
  rw [hd']
  refine hcar.trans ?_
  have hst := mirabolicLevel_le_stabilizer_base hc n ST (principal_le_congruence_subgroup hc n ST SG (Subgroup.inv_mem _ ht))
  have e : (((y * (k * t))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
      ((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  exact ((hst _).symm).trans (hS _).symm

end GlobalTheory.Mem.Col2.PtLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeEigenvalueInvNormalisedEqEsymm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatEigArith

theorem esymm_map_mul_const' (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (· * c)).esymm k = c ^ k * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    (Multiset.mem_powersetCard.1 ht).2, Multiset.map_id', mul_comm]

theorem exponent_eq (q n k : ℕ) (hq : 0 < q) (hk : k ≤ n) :
    (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (k * (n - 1)))⁻¹ * (q : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) =
      ((q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) ^ k := by
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
  have h2 : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    have h0 := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    have e : ((k * (k - 1) / 2 * 2 : ℕ) : ℂ) = ((k * (k - 1) : ℕ) : ℂ) := by rw [h0]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e
    rw [eq_div_iff two_ne_zero, e, Nat.cast_sub (show 1 ≤ k from hk1)]
    push_cast
    ring
  have h3 : ((k * (n - 1) : ℕ) : ℂ) = (k : ℂ) * ((n : ℂ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hQ,
    ← Complex.cpow_add _ _ hQ, ← Complex.cpow_mul_nat, h2, h3]
  congr 1
  push_cast
  ring

theorem satEig_inv_normalised : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  intro q n k hq hk α
  rw [esymm_map_mul_const', GlobalTheory.LFun.satEig, ← mul_assoc, ← mul_assoc, exponent_eq q n k hq hk]
  congr 2
  simp [Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val]

end GlobalTheory.SatEigArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


open Classical in
noncomputable def GlobalTheory.AutPart.jumpOf (a : ℕ) (z : ℂ) : ℤ :=
  if h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 then -h.choose else 0

theorem GlobalTheory.AutPart.jumpOf_spec (a : ℕ) (z : ℂ) (h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ((GlobalTheory.AutPart.jumpOf a z : ℤ) : ℂ) = -z + ((a : ℂ) - 1) / 2 := by
  unfold GlobalTheory.AutPart.jumpOf
  rw [dite_eq_left h]
  conv_rhs => rw [h.choose_spec]
  push_cast; ring

end

