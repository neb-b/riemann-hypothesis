module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameReducesToBasisModPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameMatrixMemUnipotentIffColumnSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc.Coords

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA PIW.AdelClassFin

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p m : ℕ}

theorem rep_of_int (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    {c : Fin m → ℤ} (h : v - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w) :
    RepV w p u v (fun j => (c j : ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j -
      ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    rw [← sub_smul]
    refine Wq_smul ?_ (hu j)
    have hk : c j - ((((c j : ZMod p)).val : ℕ) : ℤ) = (c j / p) * p := by
      rw [ZMod.val_intCast, Int.emod_def]; ring
    have e : (c j : I.E ⊗[I.F] Af I.F) - ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) =
        ((c j / p : ℤ) : I.E ⊗[I.F] Af I.F) * (p : I.E ⊗[I.F] Af I.F) := by
      have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hk
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using this
    rw [e]
    exact Wq_mul (natCast_Wq hp hcard) (intCast_int _)
  have := add_mem h h2
  show v - _ ∈ _
  convert this using 1
  abel

theorem int_comb (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) (S : Set (Fin m))
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w) :
    ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧ y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
  classical
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
  have key : ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧
      y1 - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    clear hy
    induction hy1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e : j = i => hj (by rw [e]; exact hi)) _, ?_⟩
      rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
      simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨d, hd0, hd⟩ := hz
      refine ⟨c + d, fun j hj => by simp [hc0 j hj, hd0 j hj], ?_⟩
      have := add_mem hc hd
      convert this using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      abel
    | smul s x _ hx =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨_, t, -, ht⟩ := congW_exists (w := w) hp hcard s.2
      refine ⟨fun j => t * c j, fun j hj => by simp [hc0 j hj], ?_⟩
      have h1 := (Lq I w).smul_mem s hc
      have h2 : ((s : I.E ⊗[I.F] Af I.F) - (t : I.E ⊗[I.F] Af I.F)) •
          ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
        refine Wq_smul ht (sum_mem fun j _ => ?_)
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (hu j) _
      have := add_mem h1 h2
      convert this using 1
      show (s : I.E ⊗[I.F] Af I.F) • x - _ = (s : I.E ⊗[I.F] Af I.F) • (x - _) + _
      simp only [Int.cast_mul, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul]
      abel
  obtain ⟨c, hc0, hc⟩ := key
  refine ⟨c, hc0, ?_⟩
  have := add_mem hc hy2
  convert this using 1
  abel

theorem cols_iff (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) (P : GL (Fin m) (ZMod p))
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F}
    (hP : ∀ j, RepV w p (fun k => iv I (b k)) (u j) (fun k => (P : Matrix (Fin m) (Fin m) (ZMod p)) k j))
    (A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (N : Matrix (Fin m) (Fin m) (ZMod p))
    (i : Fin m) (hN : RepV w p u (A *ᵥ u i) (fun j => N j i)) (S : Set (Fin m)) :
    (∀ j, j ∉ S → N j i = (1 : Matrix (Fin m) (Fin m) (ZMod p)) j i) ↔
      (A - 1) *ᵥ u i ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hu : ∀ j, u j ∈ I.Lf := fun j => by
    have h1 : u j - _ ∈ I.Lf := lamAf_mono I (wLat0_le I w) (hP j)
    have h2 : ∑ k, ((((P : Matrix (Fin m) (Fin m) (ZMod p)) k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ I.Lf :=
      sum_mem fun k _ => by
        rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (DictLat.iv_mem I (hb.1 k)) _
    simpa using add_mem h1 h2
  have e1 : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j = u i := by
    rw [Fintype.sum_eq_single i (fun j hj => by simp [Matrix.one_apply_ne hj])]
    simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    have h1 : ∑ j, (((N j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j - u i ∈
        Submodule.span (IntAf I.F I.E) (u '' S) := by
      rw [← e1, ← Finset.sum_sub_distrib]
      refine sum_mem fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        have hm : u j ∈ Submodule.span (IntAf I.F I.E) (u '' S) := Submodule.subset_span ⟨j, hj, rfl⟩
        exact sub_mem (nsmul_mem hm _) (nsmul_mem hm _)
      · rw [h j hj, sub_self]; exact zero_mem _
    have := Submodule.add_mem_sup h1 hN
    convert this using 1
    abel
  · intro h j hj
    obtain ⟨c, hc0, hc⟩ := int_comb hp hcard hu S h
    have h2 : A *ᵥ u i - ∑ l, (((c + Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l ∈ Lq I w := by
      convert hc using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      rw [Fintype.sum_eq_single i (f := fun l => (((Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l)
        (fun l hl => by simp [hl])]
      simp only [Pi.single_eq_same, Int.cast_one, one_smul]
      abel
    have h3 := rep_unique hp hcard hm hb (rep_comp hp hcard hb.1 hN hP)
      (rep_comp hp hcard hb.1 (rep_of_int hp hcard hu h2) hP)
    have h4 := congrArg (fun v => ((P⁻¹ : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) h3
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h4
    have h5 := congrFun h4 j
    simp only [Pi.add_apply, hc0 j hj, zero_add] at h5
    rw [h5]
    by_cases e : j = i
    · subst e; simp
    · simp [e]

theorem mem_unipSym_iff {κ : Type} [CommRing κ] {r ρ k : ℕ} (N : GL (Fin r) κ) :
    N ∈ unipSym κ r ρ k ↔ ∀ i j : Fin r, j ∉ {j | symAllowed ρ k i j} →
      (N : Matrix (Fin r) (Fin r) κ) j i = (1 : Matrix (Fin r) (Fin r) κ) j i := by
  constructor
  · rintro ⟨h1, h2⟩ i j hj
    rcases lt_trichotomy j i with h | h | h
    · obtain ⟨a, b, c⟩ : ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k := by
        by_contra hh
        exact hj ⟨h, hh⟩
      rw [h2 j i a b c, Matrix.one_apply_ne h.ne]
    · subst h
      rw [unip_diag h1, Matrix.one_apply_eq]
    · rw [unip_lower h1 h, Matrix.one_apply_ne h.ne']
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h j i (fun hh => by have := hh.1; omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (fun hh => lt_irrefl _ hh.1), Matrix.one_apply_eq]
    · rw [h j i (fun hh => hh.2 ⟨ha, hb, hc⟩), Matrix.one_apply_ne (fun e => by rw [e] at hb; omega)]

end GlobalTheory.Mem.GroupLoc.Coords

namespace GlobalTheory.Mem.GroupLoc


open Formalism.L2.SG.Pf.RowDictPf in
theorem mem_unipSym_iff_colCond : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  intro D X h hι hg k _ kv N hN
  choose b hb using fun kv => Formalism.L2.SG.Pf.AllRowsRhoX.exists_b X kv
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.Mem.SymFrameRed.symVec_red D X h hι b (fun kv => by
    unfold IsRedBasis
    rw [wLat_eq X]
    exact hb kv) hg 1
  rw [Coords.mem_unipSym_iff]
  unfold ColCond ModW
  refine forall_congr' fun i => ?_
  have hP' := hP kv
  have hN' := hN i
  unfold wLf at hP' hN' ⊢
  rw [wLat_eq X] at hP' hN' ⊢
  exact Coords.cols_iff (w := wB X (D.naut.plGw kv.1 kv.2)) (D.host.g_prime kv.1)
    (by rw [card_wB, card_res_host]) X.n_eq.symm (hb kv) (P kv) hP' (X.B.I.fmat k) _ i hN' _

end GlobalTheory.Mem.GroupLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnMemberLevelReadAtBasePoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.TopCh

theorem latS_mul_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {Lb L L' S : Submodule (𝓞 E) (Fin n → E)} {y y' k : GL (Fin n) (AfE F E)}
    (hyl : ∀ w : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb)
    (hL : L = L') (hy : y = y')
    (hl : ∀ w : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔ ((y' * k)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S)
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  subst hL hy
  have e1 : (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (y.1 *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e2 : ((y * k)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (y.1 *ᵥ x) = (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x := by
    have e : (y * k)⁻¹ * y = k⁻¹ := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e]
  have h1 := hyl (y.1 *ᵥ x)
  have h2 := hl (y.1 *ᵥ x)
  rw [e1] at h1
  rw [e2] at h2
  exact h1.symm.trans h2


set_option maxHeartbeats 2000000 in
theorem kread_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (k : Unit → GA B (B.R.N B.R.m)), I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k → let U : Subgroup (GA B (B.R.N B.R.m)) := K.lev.U; let Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E) := K.lev.Lb; let chi : U →* ℂˣ := K.lev.chi; (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U ↔ (k ())⁻¹ * x * k () ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp) ∧ (∀ (x : U) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = (k ())⁻¹ * x.1 * k () → redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h)) ∧ ∀ x : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F, x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) Lb ↔ ((k ())⁻¹ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)).1 *ᵥ x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) := by
  intro B X I hI hP l Z u a K k hR U Lb chi
  have hQ0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hG : (I.Tp a).levG B.R.m = (I.Tp I.mu0).levG B.R.m := by
    rw [TC.Tp, TC.Tp, topLev_levG_m, topLev_levG_m]
  obtain ⟨c₀⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u I.mu0).2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u I.mu0).1 c₀
  have hp := (hR.pt c₀).of_extTo (I.Q_subset_SQ I.mu0) (by rw [hQ0]; exact Finset.disjoint_empty_right _)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : GA B (B.R.N B.R.m), y₀ = (K.y c₀).1 := ⟨_, rfl⟩
  rw [← hy₀] at hp
  rw [hG]

  have hθ : ∀ θ : ((I.Tp I.mu0).levQ B.R.m).grp, θ = 1 := fun θ =>
    Subtype.ext (funext fun P => (Finset.notMem_empty P.1 (hQ0 ▸ P.2)).elim)

  have hD : ∀ q q' : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0), q.deco = q'.deco → q = q' :=
    fun q q' h => Subtype.ext (Prod.ext h (funext fun P => (Finset.notMem_empty P.1 (hQ0 ▸ P.2)).elim))
  have hgam : ∀ γ : UF B.host.E (B.R.N B.R.m), ufGL B.host.E (B.R.N B.R.m) γ = 1 → γ = 1 := fun γ h =>
    Subtype.ext ((toGLm B.host.E (B.R.N B.R.m)).injective (by show _ = toGLm B.host.E (B.R.N B.R.m) 1; rw [map_one]; exact h))
  have hmul : ∀ x : GA B (B.R.N B.R.m), y₀ * k () * ((k ())⁻¹ * x * k ()) = y₀ * x * k () := fun x => by group
  have hku : k () ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    obtain ⟨p₀, hp₀, -⟩ := hR.k_std ()
    exact hp₀.uni
  have hyu : y₀ ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    have := mul_mem hp.uni (inv_mem hku)
    rwa [mul_inv_cancel_right] at this

  have hact : ∀ h : ((I.Tp I.mu0).levG B.R.m).grp,
      (I.stp u I.mu0 B.R.m).gam c₀.1 (e.symm (1, h, 1)) = 1 ∧
      ((I.stp u I.mu0 B.R.m).act c₀.1 (e.symm (1, h, 1)) ((I.stp u I.mu0 B.R.m).rep c₀)).1.1 =
        ((1 : UF B.host.E (B.R.N B.R.m)), h.1, (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) • ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ∧
      cosetIn ((I.stp u I.mu0 B.R.m).act c₀.1 (e.symm (1, h, 1)) ((I.stp u I.mu0 B.R.m).rep c₀)) =
        cosetIn ((I.stp u I.mu0 B.R.m).rep c₀) ∧
      (I.stp u I.mu0 B.R.m).chr c₀.1 (e.symm (1, h, 1)) = ((I.Tp I.mu0).levG B.R.m).chr h := fun h => by
    obtain ⟨-, h1, h2, h3, h4, -⟩ := he (e.symm (1, h, 1))
    rw [e.apply_symm_apply] at h1 h2 h3
    refine ⟨by rw [h1]; exact map_one _, by rw [h3]; rfl, h4, by rw [h2, map_one, mul_one]⟩
  refine ⟨fun x hxu => ?_, fun x z h hz hred => ?_, fun x => ?_⟩
  · have hgu : y₀ * x * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := mul_mem (mul_mem hyu hxu) hku
    obtain ⟨q, hq⟩ := (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * x * k ()) 1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 1).2.2 hQ0 hgu
    have H2 := fun h => (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * k ()) ((k ())⁻¹ * x * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 q h).1 hp (by rw [hmul]; exact hq)
    have hq' := hq
    rw [hy₀] at hq'
    rw [hR.lev c₀ x q hq', levU, Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ1, hκq, -⟩
      obtain ⟨-, hg, -, h3, -⟩ := he κ
      have e1 : (e κ).1 = 1 := hgam _ (by rw [← hg]; exact hκ1)
      have hq2 : q = ((1 : UF B.host.E (B.R.N B.R.m)), (e κ).2.1.1, (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) •
          ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := by
        rw [← hκq, h3, e1, hθ (e κ).2.2]; rfl
      obtain ⟨hz, hred⟩ := (H2 (e κ).2.1.1).2 (by rw [hq2]; rfl)
      exact ⟨⟨_, hz⟩, by show redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hz⟩ ∈ ((I.Tp I.mu0).levG B.R.m).grp; rw [hred]; exact inv_mem (e κ).2.1.2, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have hz : (k ())⁻¹ * x * k () ∈ J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) := hwz ▸ w.2
      have hw' : redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w ∈ ((I.Tp I.mu0).levG B.R.m).grp := hw
      have hd := (H2 (redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w)⁻¹).1
        ⟨hz, by rw [inv_inv]; congr 1; exact Subtype.ext hwz.symm⟩
      have hq2 : q = ((1 : UF B.host.E (B.R.N B.R.m)), (redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w)⁻¹,
          (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) • ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := hD _ _ hd
      obtain ⟨g1, g2, g3, -⟩ := hact ⟨_, inv_mem hw'⟩
      refine ⟨e.symm (1, ⟨_, inv_mem hw'⟩, 1), g1, ?_, g3⟩
      rw [g2, hq2]
  · have hz' : (k ())⁻¹ * x.1 * k () ∈ J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) := hz ▸ z.2
    have hred' : redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hz'⟩ = h.1⁻¹ := by
      rw [← hred]; congr 1; exact Subtype.ext hz.symm
    have hpt := (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * k ()) ((k ())⁻¹ * x.1 * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 h.1).2.1 hQ0 hp hz' hred'
    rw [hmul] at hpt
    obtain ⟨g1, g2, -, g4⟩ := hact h
    have := hR.chr c₀ x (e.symm (1, h, 1)) g1 (by rw [g2, ← hy₀]; exact hpt)
    rw [g4] at this
    exact Units.ext this
  · have hS : ∀ w : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F,
        w ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) ↔
        ((1 : GA B (B.R.N B.R.m))⁻¹ : GA B (B.R.N B.R.m)).1 *ᵥ w ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) :=
      fun w => by
        have e : ((1 : GA B (B.R.N B.R.m))⁻¹ : GA B (B.R.N B.R.m)).1 *ᵥ w = w := by rw [inv_one, Units.val_one, Matrix.one_mulVec]
        rw [e]
    have hp1 : IsPtOf B.sp.cm (y₀ * k () * (1 * 1)) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := by rw [mul_one, mul_one]; exact hp
    have hl := GlobalTheory.T.pointLattice_iff_baseLattice_decorated B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) 1 1 (y₀ * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 (one_mem _) hS hp1
    have hc := (((spaces_in_coordinates I hI hP l Z).2.2.2 B.R.m le_rfl).2.2 u I.mu0).1 c₀
    exact latS_mul_iff (K.y_lat c₀) hc hy₀.symm hl x

end GlobalTheory.Mem.Col2.TopCh
end

