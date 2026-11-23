module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

def CongE {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g g' : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  ∀ x ∈ stdAt E n P, (((qOf P : ℕ) : E) ^ c)⁻¹ • (g x - g' x) ∈ stdAt E n P

theorem congE_refl {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (c : ℕ)
    (g : Sp E n ≃ₗ[E] Sp E n) : CongE P c g g := fun x _ => by
  rw [sub_self, smul_zero]
  exact Submodule.zero_mem _

theorem CongE.symm {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    {g g' : Sp E n ≃ₗ[E] Sp E n} (h : CongE P c g g') : CongE P c g' g := fun x hx => by
  rw [← neg_sub, smul_neg]
  exact Submodule.neg_mem _ (h x hx)

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

abbrev sm : Seam (I.rec7 l Z) B.fields := seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G

abbrev SBof (a : I.ι) : Finset (HeightOneSpectrum (𝓞 B.fields.E)) := rowSG (B.primes X) I.sel (I.tup a)

abbrev Charts (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) {Ch : Type}
    (chOf : (I.stp u a i).Cl → Ch) : Type 1 :=
  ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
    (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))

abbrev ReadsAt {u : B.Word} {a : I.ι} {i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch} (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)) : Prop :=
  I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
    (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k

def ChiFin {T i : ℕ} {hi : i ≤ B.R.m} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ κ : S.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → S.chi κ ^ n = 1

def FrNear (a : I.ι) {n : ℕ} (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E) : Prop :=
  ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) ∧
    GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P))⁻¹ * k)

def LiftsInv {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (κ : (I.stp u a i).G b) (P : SBof I a)
    (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) : Prop :=
  g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧
    (∀ h : P.1 ∈ (B.primes X).vGs, ∀ x ∈ stdAt B.fields.E (B.R.N i) P.1,
      redV P.1 (g x) = ((κ.2.1.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 x)) ∧
    ∀ h : P.1 ∈ I.Q a, g = ((κ.2.2.1 ⟨P.1, h⟩)⁻¹).1

abbrev MidAt {u : B.Word} {a : I.ι} {i : ℕ} (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a)
    (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K) : Prop :=
  GlobalTheory.TwU.MidLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i (Idx.get b hi) P) g z

def Keeps {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (κ : (I.stp u a i).G b) (p : (I.stp u a i).D b) : Prop :=
  (I.stp u a i).gam b κ = 1 ∧ cosetIn ((I.stp u a i).act b κ p) = cosetIn p

theorem keeps_one {u : B.Word} {a : I.ι} {i : ℕ} {b : (I.stp u a i).β} (p : (I.stp u a i).D b) :
    Keeps I (1 : (I.stp u a i).G b) p :=
  ⟨map_one _, congrArg cosetIn (@one_smul _ _ _ ((I.stp u a i).actD b) p)⟩

end GlobalTheory.Mem.Col2.AdT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInte
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocBasisBasR

open Matrix

theorem norm_det_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {N : ℕ}
    (g : Matrix (Fin N) (Fin N) K) (hg : ∀ a b, ‖g a b‖ ≤ 1) : ‖g.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, norm_prod]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hg _ _)

theorem main : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm M hL hM
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  have hp : p.Prime := Fact.out
  have hns : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact GlobalTheory.KapSplitNorm.norm_natCast_eq_one p s hs
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := (Bm : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAdef
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E).map ρ with hAidef
  have hAAi : A * Ai = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hAiA : Ai * A = 1 := by
    rw [hAdef, hAidef, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hMu : IsUnit M.det := Ne.isUnit hM.1

  have hcoord : ∀ x ∈ L, ∀ a, ‖(Ai *ᵥ fun i => ρ (x i)) a‖ ≤ 1 := by
    intro x hx a
    obtain ⟨s, hs, hint⟩ := (hL x).1 ⟨1, hp.not_dvd_one, by simpa using hx⟩
    obtain ⟨c, hc⟩ := hint a
    have e : (Ai *ᵥ fun i => ρ (x i)) a = ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) := by
      rw [RingHom.map_mulVec]; rfl
    have hs1 := hns s hs
    have hs0 : ρ (s : D.host.E) ≠ 0 := by intro h; rw [h, norm_zero] at hs1; exact zero_ne_one hs1
    have e2 : ρ ((((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a) =
        (ρ (s : D.host.E))⁻¹ * ρ (algebraMap (𝓞 D.host.E) D.host.E c) := by
      rw [hc, map_mul]; field_simp
    rw [e, e2, norm_mul, norm_inv, hs1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ c
  have hg : ∀ a b, ‖(Ai * M) a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hcol⟩ := hM.2.2 b
    have : (Ai * M) a b = ∑ k, r k * (Ai *ᵥ fun i => ρ (x k i)) a := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hcol, hρ, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hr k) (norm_nonneg _) (hcoord _ (hx k) a)
  refine ⟨Ai * M, hg, ?_, ?_⟩
  · have hh : ∀ b a, ‖(M⁻¹ * A) b a‖ ≤ 1 := by
      intro b a
      let x : Fin N → D.host.E := fun j => (Bm : Matrix (Fin N) (Fin N) D.host.E) j a
      have hxe : x = (Bm : Matrix (Fin N) (Fin N) D.host.E) *ᵥ Pi.single a 1 := by
        funext j; simp [x, Matrix.mulVec_single]
      have hrhs : ∃ s : ℕ, ¬ p ∣ s ∧ ∀ c, (s : D.host.E) *
          (((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) c ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        refine ⟨1, hp.not_dvd_one, fun c => ?_⟩
        rw [hxe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
          Nat.cast_one, one_mul, Pi.single_apply]
        split_ifs
        · exact ⟨1, map_one _⟩
        · exact ⟨0, map_zero _⟩
      obtain ⟨s, hs, hmem⟩ := (hL x).2 hrhs
      have h := hM.2.1 _ hmem b
      rw [hρ] at h
      have e : (fun j => ρ (((s : D.host.E) • x) j)) = ρ (s : D.host.E) • fun j => ρ (x j) := by
        funext j
        change ρ ((s : D.host.E) * x j) = ρ (s : D.host.E) * ρ (x j)
        rw [map_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, hns s hs, one_mul] at h
      convert h using 2
      simp [A, x, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hprod : (Ai * M) * (M⁻¹ * A) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul, hAiA]
    have hd := congrArg Matrix.det hprod
    rw [Matrix.det_mul, Matrix.det_one] at hd
    have hn := congrArg norm hd
    rw [norm_mul, norm_one] at hn
    have h1 := norm_det_le_one _ hg
    have h2 := norm_det_le_one _ (fun b a => hh b a)
    by_contra hne
    have hlt : ‖(Ai * M).det‖ < 1 := lt_of_le_of_ne h1 hne
    have : ‖(Ai * M).det‖ * ‖(M⁻¹ * A).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hlt
    linarith
  · rw [hρ, ← Matrix.mul_assoc]
    change M = A * Ai * M
    rw [hAAi, Matrix.one_mul]

end GlobalTheory.LocBasisBasR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → Formalism.L2.Rows.LowerMapTieS F :=
  fun I hO hP l Z u Ch chOf F hS =>
    fun _ ψ c P _ h => lowerMap_std I hO hP l Z u Ch chOf F hS ψ c P h

end GlobalTheory.Mem.Col2.LowerTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTwGen
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_tw_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hO : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} {Tw : TwForms (I.rec7 l Z)}
    (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (he : Tw = I.tw l l0 Z) (hC : I.StdC l Z C) (hTw : I.StdTw l Z l0 (he ▸ t))
    (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) (ha : a ≠ (I.rec7 l Z).what₂.mu0) (h1 : 1 ≤ (I.rec7 l Z).R.m) :
    IsUnit (Formalism.L2.Forms.bZ u (t.pt.til u a ha h1).z0).det → ∀ (ψ : ((I.rec7 l Z).PTw u a).Wz) (c : (Tw.fm u a).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      P ∈ Formalism.L2.Forms.CSpan (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) →
      (∀ s, t.ptE.eWz u a ψ c s =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (Formalism.L2.Forms.mZ u (t.pt.til u a ha h1).z0) P
          (Formalism.L2.Forms.twYS t.ch C.forms u a (I.rec7 l Z).R.m le_rfl s)) →
      (t.pt.val u a ha).eW (((I.rec7 l Z).PTw u a).lowerMap ψ) c =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by

  subst he
  obtain ⟨hW, hLv, hPd⟩ := hTw
  intro _ ψ c P _ hψ
  have hS := hC u
  have hPd' : I.StdP l Z l0 t.pt t.ptE := hPd
  have hW' : I.StdW l Z l0 t.forms := hW
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace (C.forms u).valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1' : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hPd'.eWz, hl', hPd'.z0 u a ha h1, mZ_std I l Z u hO hP (TC.z0 X u) (fun j => rfl)] at h
    refine h.trans ?_
    have h2 : (Formalism.L2.Forms.twYS t.ch C.forms u a (I.rec7 l Z).R.m le_rfl s).1 = s.1 := by
      simp only [Formalism.L2.Forms.twYS, Equiv.trans_apply, hW'.eY, Equiv.refl_symm, Equiv.refl_apply]
      rw [Formalism.L2.Forms.eYS_end _ _ _ (Or.inr rfl)]
      exact hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1']
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hPd'.eW u a ha _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

end GlobalTheory.Mem.Col2.LowerTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMap
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.WWUnique

theorem aeval_map_nablaX {Lt : Type} [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.aeval (R := ℂ_[l]) (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2)) :
          MvPolynomial (KM.XZ Lt N0 N1) ℂ_[l]))
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N1 nu I)) =
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.Gxz N0 N1 nu I) := by
  simp only [KM.nablaX, KM.Gxz, KM.minorXZ, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp [MvPolynomial.map_X, MvPolynomial.aeval_X, map_sum, map_mul]

theorem ww_unique : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  intro D p _ N0 N1 hN nu hnu Th ph ph' κ Q hQ h I
  classical
  haveI : Finite (KM.ColChoice N1 nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N1 nu) := Fintype.ofFinite _
  let J : ((Bool × HH D) × Fin N0 × Fin N1 →₀ ℕ) → ℂ_[p] :=
    fun m => (m.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff m Th
  let σ : (Bool × HH D) × ℕ × Fin N1 → MvPolynomial (KM.XZ (Bool × HH D) N0 N1) ℂ_[p] :=
    fun v => ∑ a : Fin N0, MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2))
  let L : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) :=
    ph ∘ₗ GlobalTheory.KFormCore.jetL J ∘ₗ (MvPolynomial.aeval (R := ℂ_[p]) σ).toLinearMap
  have hL : ∀ J' : KM.ColChoice N1 nu, L (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu J')) =
      ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu J')) := by
    intro J'
    simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, σ]
    rw [aeval_map_nablaX, GlobalTheory.KFormCore.applyAt0_eq]
  have hLD : ∀ y, L (GL3Columns.DeX N1 nu y) = GL3Columns.applyQ p N0 N1 Th Q y := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GL3Columns.ww_holds D p N0 N1 nu Th ph Q hQ y, GL3Columns.wwCB_holds D ℂ_[p] N1 nu y, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, hL, smul_eq_mul]
  let ψ : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) := ph' - κ • L
  have hψ : ∀ y, ψ (GL3Columns.DeX N1 nu y) = 0 := by
    intro y
    let e := Equiv.ofBijective (tauPl D) (tauPl_bij D)
    let y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p] := fun τ => Matrix.of fun a b => y (e.symm τ) a b
    have hy : GL3Columns.DeX N1 nu y = GL3Columns.DeX N1 nu (fun s => GL3Columns.colsOf (y' (tauPl D s))) := by
      unfold GL3Columns.DeX
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
      congr 1
      ext i j
      have hj : (j : ℕ) < N1 :=
        lt_of_lt_of_le j.2 ((YoungDiagram.colLen_anti _ 0 c (Nat.zero_le _)).trans ((hnu s).trans hN))
      have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
      simp [GL3Columns.colsOf, hj, y', hs]
    rw [hy]
    simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, h, hLD, smul_eq_mul, sub_self]
  have h4 := GL3Columns.wwInj_holds D p N1 nu ψ hψ I
  simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h4
  exact sub_eq_zero.mp h4

end GlobalTheory.KForm.WWUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormSignExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FinDatum

theorem isRoots_sign {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {r n N : ℕ} {L : Lt E r} {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (ε : ℤˣ) (hN : l.M ∣ N)
    {Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E} (h : IsRoots l L ((ε : ℤ) • mk) N Y) :
    IsRoots l L mk l.M fun q => (ε : ℤ) • Y q := by
  intro q b
  obtain ⟨⟨a, ha, h1, h2⟩, j, hj⟩ := h q b
  obtain ⟨m, rfl⟩ := hN
  refine ⟨⟨a, ha, h1, ?_⟩, j, fun s hs => ?_⟩
  · have h3 := zsmul_mem h2 (ε : ℤ)
    rw [smul_sub, LinearMap.smul_apply, smul_comm (l.M : E)⁻¹, smul_smul, ← Units.val_mul, Int.units_mul_self,
      Units.val_one, one_smul] at h3
    exact h3
  · obtain ⟨u, hu, e⟩ := hj s hs
    refine ⟨(ε : ℤ) • m • u, zsmul_mem (nsmul_mem hu m) _, ?_⟩
    show s • (ε : ℤ) • Y q b = _
    rw [smul_comm s, e, smul_comm (2 * l.M), smul_smul (2 * l.M), mul_assoc]

variable {D : D7}

theorem lat_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) :
    LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, h', -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatIsom V (T.Q.Dw ((i : ℕ) + 1)).EF
        (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) ∧ LatIsom (Wc D i) (T.Q.Dw ((i : ℕ) + 1)).EF (iotaW T i) := by
    rintro V hr rfl h h'
    exact ⟨h, h'⟩
  exact key _ hr hV h h'

theorem latR_range {E : Type} [Field E] [NumberField E] {m r : ℕ} (hr : m = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    GlobalTheory.AdTh.latR hr (LinearMap.range (LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι)) = LinearMap.range ι := by
  subst hr
  unfold GlobalTheory.AdTh.latR
  rw [← LinearMap.range_comp]
  rfl

theorem splitOffBad_one (V : HSp D) : SplitOffBad V 0 1 := by
  refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩, zero_mul _⟩,
    fun _ h => absurd h (Finset.notMem_empty _), fun i j => ?_⟩
  rw [show Formalism.L2.Theta.mt V 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]

theorem isFinOf_finR (S T : HSp D) {r : ℕ} (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) :
    GlobalTheory.AdTh.colsR hr (y.submatrix id (Fin.cast hr))ᵀ = y ∧
      GlobalTheory.AdTh.IsFinOf S T (y.submatrix id (Fin.cast hr))ᵀ (finR S hr y) := by
  subst hr
  exact ⟨rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

theorem mem_std_star (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {n : ℕ} (v : Fin n → D.host.E)
    (h : v ∈ Formalism.L2.Pj.stdLat D.host.E n) : (fun j => star (v j)) ∈ Formalism.L2.Pj.stdLat D.host.E n := by
  intro j _
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h j trivial)
  exact Submodule.mem_one.2 ⟨H.bar a, (H.bar_eq a).trans (congrArg star ha)⟩

theorem smul_eq_zero_of_smul_rep {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (q : LevQ Dw l) (s : 𝓞 E) (z : Dw.La) (hz : s • (cSep l • levRep q) = l.M • z) :
    s • q = 0 := by
  have hrep : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  rw [← hrep, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hM : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))
  have e : s • levRep q = (l.M : 𝓞 E) • z - (cSep l - 1) • s • levRep q := by
    rw [Nat.cast_smul_eq_nsmul, ← hz, sub_smul, one_smul, smul_comm s, sub_sub_cancel]
  rw [e]
  exact sub_mem (Submodule.smul_mem_smul hM trivial) (Submodule.smul_mem_smul (LevelPairing.cSep_spec _).2 trivial)


end GlobalTheory.OneMapRef.FinDatum
end

