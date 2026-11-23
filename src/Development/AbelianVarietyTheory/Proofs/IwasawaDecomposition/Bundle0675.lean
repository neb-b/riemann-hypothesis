module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0665

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.ChiWExt

section Move

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

theorem m_eq (hP : B'.toPre = B.toPre) : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  exact (by with_unfolding_all exact ((Eq.refl (w.st Z).toD7.R.m) :))

theorem gc_eq (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) : Gc B' px' = Gc B px := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  exact (by with_unfolding_all exact ((Eq.refl (Gc B px)) :))

theorem prod_move (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {Pg : Finset (Pl (w.st Z).toD7.host.E)} {Pg' : Finset (Pl (w'.st Z').toD7.host.E)} (hPg : HEq Pg' Pg)
    {eG : Gc B px ≃* G0 Pg (w.st Z).toD7.R.r} {eG' : Gc B' px' ≃* G0 Pg' (w'.st Z').toD7.R.r} (heG : HEq eG' eG)
    {χ : ∀ PP : Pl (w.st Z).toD7.host.E, (kP PP)ˣ →* ℂˣ} {χ' : ∀ PP : Pl (w'.st Z').toD7.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (χ' PP') (χ PP)) {g : Gc B px} {g' : Gc B' px'} (hg : HEq g' g) :
    ∏ PP : Pg', ((χ' PP (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((χ PP (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (eG')) ((by with_unfolding_all exact ((eG) :))) (eG') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (eG')) (eG') (((eG))) (((heG)))).symm : _))
  clear (heG)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  have e : ∀ PP : Pl (w.st Z).toD7.host.E, PP ∈ Pg → HEq (χ' ((by with_unfolding_all exact (PP :)))) (χ PP) :=
    fun PP hm => hχ ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact congrArg (fun c : ℂˣ => (c : ℂ)) (DFunLike.congr_fun (eq_of_heq (e PP.1 PP.2)) _)

end Move


set_option maxHeartbeats 1000000 in
theorem grp_chiW_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS hL
  have hc := z.pins.char.base.grp.chiW
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  intro i' g'
  have hm := m_eq (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1
  let i : Fin (w.st Z).toD7.R.m := ⟨i', by have := i'.2; omega⟩
  have hi : (i : ℕ) = i' := rfl
  let g : Gc B w.px := cast (gc_eq hE.1 hpx) g'
  have hg : HEq g' g := (cast_heq _ _).symm
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -, hW, -⟩ := hS'
  have hWi := hW i i' hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hWι⟩ := hWi
  have hch := (hWι ι hι).2.2.1 g' g hg
  rw [hch, hι, hc i g]
  exact (prod_move hE.1 hpx hPg heG (fun PP' PP h hm => (hL.1 i i' hi).2 PP' PP h hm) hg).symm

end GlobalTheory.Mem.R3.Rw.ChiWExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoefficientsAgreeEnlargedBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt


set_option maxHeartbeats 2000000 in
theorem idemSame_of_keep : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → GrpTrue Z.N f → GrpTrue Z'.N f' → RSideW z Wt' R' →
  ∀ cG : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd, Keep R'.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 cG → IdemSame z Xg := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hp hG hG' hR cG hK g' g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -⟩ := hR
  have hB := hE.1
  cases B
  cases B'
  dsimp only at hB
  subst hB
  cases hf
  have hpx : w'.px = w.px := eq_of_heq hp
  cases w'
  dsimp only at hpx
  subst hpx
  cases hg
  obtain ⟨plg, iso, hpl, hid, -, hbc⟩ := z.pins.keep.grp
  obtain ⟨plg2, iso', hpl', hid', -, hbc'⟩ := hK.grp
  refine (hid' g).trans (Eq.trans ?_ (hid g).symm)
  refine Eq.trans ?_ (TypesTrue.typeIdempotent_coeff_across_layers hG hG' ((z.R.eG.trans z.cG) g))
  congr 1
  funext kv'
  obtain ⟨k, v'⟩ := kv'
  obtain ⟨v, rfl⟩ : ∃ v, v' = plEquiv Z.N.naut Z'.N.naut k v := ⟨_, (Equiv.apply_symm_apply _ v').symm⟩
  show _ = ((z.R.eG.trans z.cG) g) ⟨k, (plEquiv Z.N.naut Z'.N.naut k).symm (plEquiv Z.N.naut Z'.N.naut k v)⟩
  rw [Equiv.symm_apply_apply]
  have hP : R'.Pg = z.R.Pg := eq_of_heq hPg
  have hQ : (plg2 ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩).1 = (plg ⟨k, v⟩).1 := by
    rw [hpl', hpl]
    exact TypesTrue.plGw_plEquiv hG hG' k v
  exact GlobalTheory.Mem.R3.DefLatBC.bc_eq_of_heq hP z.R.eG R'.eG heG g _ _ hQ (iso ⟨k, v⟩)
    (iso' ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩) _ _ (hbc g ⟨k, v⟩) (hbc' g ⟨k, plEquiv Z.N.naut Z'.N.naut k v⟩)

end GlobalTheory.Mem.R3.Rw.WeilExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowers
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GoodPrimeSelection

theorem heq_sigma_app {P P' Tw Tw' Y Y' : Type} (hP : P = P') (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {twI : P → Tw} {twI' : P' → Tw'} (h1 : HEq twI twI') {Q : P → Finset Y} {Q' : P' → Finset Y'} (h2 : HEq Q Q')
    {k : P → ℕ} {k' : P' → ℕ} (h3 : HEq k k')
    {psi : ∀ w, RCG (twI w) (Q w) →* (Ok (twI w) (k w))ˣ} {psi' : ∀ w, RCG' (twI' w) (Q' w) →* (Ok' (twI' w) (k' w))ˣ}
    (h4 : HEq psi psi') {w : P} {w' : P'} (hw : HEq w w') :
    HEq (⟨twI w, Q w, k w, psi w⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨twI' w', Q' w', k' w', psi' w'⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hP hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases h1; cases h2; cases h3; cases h4; cases hw
  rfl

theorem heq_sigma_pow {Tw Tw' Y Y' : Type} (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {p : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ} {p' : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ}
    (hp : HEq p p') (b : Bool) (c : ℤ) :
    HEq (⟨p.1, p.2.1, p.2.2.1, BlochKatoReduction.Gen.psiAt b (p.2.2.2 ^ c)⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨p'.1, p'.2.1, p'.2.2.1, BlochKatoReduction.Gen.psiAt b (p'.2.2.2 ^ c)⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases hp
  rfl

theorem disjoint_of_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H')
    {A B : Finset (PlE H)} {A' B' : Finset (PlE H')} (hA : HEq A A') (hB : HEq B B') (h : Disjoint A B) : Disjoint A' B' := by
  subst hR; cases hH; cases hA; cases hB; exact h

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem auxiliaryPrime_eq_of_same_ranks_host {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) : AbsolutelyIrreducibleSpan.q0 D = AbsolutelyIrreducibleSpan.q0 D' := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem discr_eq {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) :
    (NumberField.discr D.host.E).natAbs.primeFactors = (NumberField.discr D'.host.E).natAbs.primeFactors := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem mem_avD_iff {D : D7} (i : D.ntw.Tw) (v : PlE D.host) :
    v ∈ avD D (avDesign D) i ↔ ∃ p ∈ avPrimes D ∪ avPrimesDesign D i, v ∈ placesOver D.host.E p := by
  classical
  unfold avD
  rw [Finset.mem_union, mem_avRec, mem_avDesign]
  constructor
  · rintro (⟨p, hp, hv⟩ | ⟨p, hp, hv⟩)
    · exact ⟨p, Finset.mem_union_left _ hp, hv⟩
    · exact ⟨p, Finset.mem_union_right _ hp, hv⟩
  · rintro ⟨p, hp, hv⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Or.inl ⟨p, hp, hv⟩
    · exact Or.inr ⟨p, hp, hv⟩

theorem avD_heq {D D' : D7} (h : SameExport D D') {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') :
    HEq (avD D (avDesign D) i) (avD D' (avDesign D') i') := by
  have hl : D.ntw.l i = D'.ntw.l i' := ((same_basic h.gal h.set h.frm).2.2.2.2 i i' hi).1
  have hd : avPrimesDesign D i = avPrimesDesign D' i' := by
    unfold avPrimesDesign
    rw [hl, auxiliaryPrime_eq_of_same_ranks_host h.gal.R h.gal.host, discr_eq h.gal.R h.gal.host]
  refine heq_places h.gal.R h.gal.host (s := avPrimes D ∪ avPrimesDesign D i) (mem_avD_iff i) ?_
  intro v
  rw [mem_avD_iff i' v, h.av, hd]

def normE {D : D7} (xd : ThData D) (h : XdAll xd) : IntegralHeckeForms.XD D where
  Dat0 i j b := if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅
  theta_base_equivariant i j b a ha u := by
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · exact xd.thetaBase_invariant_action i j b a (by rw [h i j b hj.1 hj.2]; trivial) u
    · rw [if_neg hj] at ha
      exact ha.elim

theorem normE_eq {D : D7} (xd : ThData D) (h : XdAll xd) :
    ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (normE xd h).Dat0 i j b = (twEOf xd).Dat0 i j b := by
  intro i j hj b
  rw [Finset.mem_Icc] at hj
  show (if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅) = xd.xd0 i j b
  rw [if_pos hj, h i j b hj.1 hj.2]

theorem heq_ite_univ {T T' : Type} (hT : T = T') {Dat : T → ℕ → Bool → Type} {Dat' : T' → ℕ → Bool → Type}
    (hD : HEq Dat Dat') {m m' : ℕ} (hm : m = m') :
    HEq (fun i j b => (if 1 ≤ j ∧ j ≤ m then Set.univ else ∅ : Set (Dat i j b)))
      (fun i j b => (if 1 ≤ j ∧ j ≤ m' then Set.univ else ∅ : Set (Dat' i j b))) := by
  subst hT hm; cases hD; rfl

theorem normE_heq {D D' : D7} (h : SameExport D D') (xd : ThData D) (hx : XdAll xd) (xd' : ThData D') (hx' : XdAll xd') :
    HEq (normE xd hx).Dat0 (normE xd' hx').Dat0 :=
  heq_ite_univ (eq_of_heq h.set.Tw) h.frm.Dat (by rw [h.gal.R])

theorem goodTw_swap {D : D7} {E E' : IntegralHeckeForms.XD D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = E'.Dat0 i j b)
    {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)}
    {A Q : Finset (PlE D.host)} {k : ℕ} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ}
    (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E' N0 i e S A Q k ψ := by
  unfold IntegralHeckeForms.GoodTw at h ⊢
  obtain ⟨h1, ⟨eB, h0, hs, hI⟩, h3, h4⟩ := h
  refine ⟨h1, ⟨eB, h0, hs, fun j hj b => ?_⟩, fun j hj b => ?_, h4⟩
  · have := hI j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]
  · have := h3 j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]

theorem ok_swap {D : D7} {I I' : TwIn D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, I.E.Dat0 i j b = I'.E.Dat0 i j b)
    (hS : I.S = I'.S) {i : D.ntw.Tw} (h : I.Ok i) : I'.Ok i := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj b => ?_, fun j hj b => ?_⟩
  · have := h1 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ IntegralHeckeForms.FullRk at this ⊢
    rw [← hE i j hj b]
    exact this
  · have := h2 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ at this ⊢
    rw [← hE i j hj b, ← hS]
    exact this

theorem good_pack {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    {A : Finset (PlE D.host)} {A' : Finset (PlE D'.host)} (hA : HEq A A')
    (hg : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) A p.2.1 p.2.2.1 p.2.2.2) :
    IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) A' p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 hA h4 k h6 hg

theorem psiAt_pow_pow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (a c : ℤ) :
    ∃ e : ℤ, e.natAbs = a.natAbs * c.natAbs ∧ BlochKatoReduction.Gen.psiAt b ((ψ ^ a) ^ c) = ψ ^ e := by
  obtain ⟨e, he, h⟩ := Formalism.MainNotions.N.TwAll.psiAt_side_zpow true b ψ (a * c)
  refine ⟨e, by rw [he, Int.natAbs_mul], ?_⟩
  rw [← zpow_mul, h]
  simp [BlochKatoReduction.Gen.psiAt]

theorem goodO_of_seed : ∀ (D₁ D₂ D₃ : D7) (A : D₁.ntw.Tw → Finset (PlE D₁.host)) (σ : Seed D₁ A) (C₂ : NChoice D₂)
    (C₃ : NChoice D₃) (xd : ThData D₃) (u : D₃.what₂.places.Pl → D₁.what₂.places.Pl), SameExport D₁ D₂ → Kept C₂ C₃ →
    avPrimes D₂ = avPrimes D₃ → D₂.what₂.places.Pl = D₃.what₂.places.Pl → XdAll xd → (∀ i, avD D₁ (avDesign D₁) i ⊆ A i) →
    (∀ v₂ v₃, HEq v₂ v₃ → TwistedAt D₃ v₃ → TwistedAt D₁ (u v₃) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v₃))) ∧
      HEq (rawPack C₂ v₂) (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v₃)))) → GoodO D₃ C₃ xd := by
  intro D₁ D₂ D₃ A σ C₂ C₃ xd u h12 hK hav hPl hxd hA hu
  have h23 : SameExport D₂ D₃ := ⟨hK.gal, hK.set, hK.forms, hK.br, hav⟩
  have h13 : SameExport D₁ D₃ := h12.trans h23
  obtain ⟨hTw, -, hSS, hcomp, hsame⟩ := same_basic h13.gal h13.set h13.frm
  have hY : PlE D₁.host = PlE D₃.host := plE_eq h13.gal.R h13.gal.host

  have key : ∀ v, TwistedAt D₃ v → TwistedAt D₁ (u v) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v))) ∧
      HEq (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v))) (rawPack C₃ v) := by
    intro v hv
    obtain ⟨ht, a, ha, hp⟩ := hu (cast hPl.symm v) v (cast_heq _ _) hv
    refine ⟨ht, a, ha, hp.symm.trans ?_⟩
    exact heq_sigma_app (RCG := D₂.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₂.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₂.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₂.ntw.crOk) (cO' := D₃.ntw.crOk)
      hPl (eq_of_heq hK.set.Tw) (plE_eq hK.gal.R hK.gal.host) hK.set.RCG hK.set.grpRCG hK.set.Ok hK.set.crOk
      hK.twI hK.Q hK.k hK.psi (cast_heq _ _)
  have hN0 : (D₁.ntw.Tw → ℕ) = (D₃.ntw.Tw → ℕ) := by rw [hTw]
  let I₁ : TwIn D₁ := ⟨normE σ.xd σ.all, σ.N0, σ.S⟩
  let In : TwIn D₃ := ⟨normE xd hxd, cast hN0 σ.N0, cast hSS σ.S⟩
  let I₃ : TwIn D₃ := ⟨twEOf xd, cast hN0 σ.N0, cast hSS σ.S⟩
  have hE : HEq I₁.E.Dat0 In.E.Dat0 := normE_heq h13 σ.xd σ.all xd hxd
  have hN : HEq I₁.N0 In.N0 := (cast_heq _ _).symm
  have hS : HEq I₁.S In.S := (cast_heq _ _).symm
  have h1n : ∀ i, ∀ j ∈ Finset.Icc 1 D₁.R.m, ∀ b, (twEOf σ.xd).Dat0 i j b = (normE σ.xd σ.all).Dat0 i j b :=
    fun i j hj b => (normE_eq σ.xd σ.all i j hj b).symm
  have h3n : ∀ i, ∀ j ∈ Finset.Icc 1 D₃.R.m, ∀ b, In.E.Dat0 i j b = I₃.E.Dat0 i j b := normE_eq xd hxd

  have pw : ∀ v, TwistedAt D₃ v → ∀ c : ℤ, Nat.Coprime c.natAbs (D₃.ntw.l (C₃.twI v)) →
      ∀ (B₁ : Finset (PlE D₁.host)) (B₃ : Finset (PlE D₃.host)), HEq B₁ B₃ → B₁ ⊆ A (σ.s (u v)) →
      I₃.Ok (C₃.twI v) ∧ IntegralHeckeForms.GoodTw D₃.nexp (BlochKatoReduction.bk0 D₃) I₃.E I₃.N0 (C₃.twI v) (twEps D₃ (C₃.twI v)) (I₃.S (C₃.twI v)) B₃
        (C₃.Q v) (C₃.k' v) (BlochKatoReduction.Gen.psiAt (C₃.sd v) (C₃.psi' v ^ c)) := by
    intro v hv c hc B₁ B₃ hB hBA
    obtain ⟨ht, a, ha, hp⟩ := key v hv
    have hl : D₁.ntw.l (σ.s (u v)) = D₃.ntw.l (C₃.twI v) := (hsame _ _ (hcomp _ _ hp).1).1
    have hq := heq_sigma_pow (RCG := D₁.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₁.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₁.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₁.ntw.crOk) (cO' := D₃.ntw.crOk)
      hTw hY h13.set.RCG h13.set.grpRCG h13.set.Ok h13.set.crOk hp (C₃.sd v) c
    obtain ⟨e, he, hpe⟩ := psiAt_pow_pow (C₃.sd v) (σ.ψ (σ.s (u v))) a c
    have hce : Nat.Coprime e.natAbs (D₁.ntw.l (σ.s (u v))) := by
      rw [he]
      exact Nat.Coprime.mul_left ha (hl ▸ hc)
    obtain ⟨hok, hg⟩ := σ.good (u v) ht
    have g1 := goodTw_swap h1n (hg e hce)
    rw [← hpe] at g1
    have g2 : IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) I₁.E I₁.N0 (σ.s (u v)) (twEps D₁ (σ.s (u v))) (I₁.S (σ.s (u v))) B₁
        (σ.Q (σ.s (u v))) (σ.k (σ.s (u v))) (BlochKatoReduction.Gen.psiAt (C₃.sd v) ((σ.ψ (σ.s (u v)) ^ a) ^ c)) :=
      expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩) hBA g1
    have ok1 : I₁.Ok (σ.s (u v)) := ok_swap (I := ⟨twEOf σ.xd, σ.N0, σ.S⟩) (I' := I₁) h1n rfl hok
    have g3 := good_pack h13 hE hN hS hq hB g2
    have ok3 := (SameExport.good h13 hE hN hS hq
      ⟨ok1, expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩)
        ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _)) g1⟩).1
    exact ⟨ok_swap h3n rfl ok3, goodTw_swap h3n g3⟩
  refine ⟨⟨I₃, rfl, fun v hv => ?_, fun v hv _ => ?_⟩, fun v v' hv hv' hne => ?_⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    exact ⟨(pw v hv 1 (by simp) _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).1,
      fun c hc => (pw v hv c hc _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).2⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    have h := (pw v hv 1 (by simp) _ _ (avD_heq h13 (hcomp _ _ hp).1) (hA _)).2
    rw [zpow_one] at h
    exact h
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    obtain ⟨ht', a', ha', hp'⟩ := key v' hv'
    obtain ⟨hi, hQ, -, -⟩ := hcomp _ _ hp
    obtain ⟨hi', hQ', -, -⟩ := hcomp _ _ hp'
    refine disjoint_of_heq h13.gal.R h13.gal.host hQ hQ' (σ.sep (u v) (u v') ht ht' fun he => hne ?_)
    exact eq_of_heq ((hi.symm.trans (heq_of_eq he)).trans hi')

end GlobalTheory.HeightCounting.Up.GoodPrimeSelection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkRow_move (Rl : RealDat3 D A3 Ks) {i' i : Fin D.R.m} (h : i' = i) (k : ℕ) (P : PlE D.host)
    (u v : Fin (Rl.nW i') → D.what₂.LL) (u' v' : Fin (Rl.nW i) → D.what₂.LL) (hu : HEq u u') (hv : HEq v v')
    (hec : ∀ (α : GA D (Wc D i')) (R : Finset (GA D (Wc D i'))), IsHeckeAt (Wc D i') P k α →
      Bridge.IsDC (levG (Wc D i') (Rl.βW i') (Rl.datWp i' Rl.triv)) α R →
      (Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) u) =
        hkNorm Rl i' k P • heckeOn (Rl.MW i' (sg0 D A3.A)) R ((Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) v))) :
    ∀ (α : GA D (Wc D i)) (R : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R →
      (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) u') =
        hkNorm Rl i k P • heckeOn (Rl.MW i (sg0 D A3.A)) R ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) v')) := by
  subst h
  cases hu
  cases hv
  exact hec

theorem hkRow_of_ad (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (Y : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG _ Y) (Sb : Finset (PlE D.host))
    (hfi : ∀ i x, HEq ((Y.fi i).e x) x) (hS : ∀ i, Sb ⊆ D.ntw.S0 i)
    (hec : ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat Rl Sb (idxOf D j) k P α Rr → ∀ x : Fin (Rl.nW (idxOf D j)) → D.what₂.LL,
      (Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) (H.hL j k P x)) =
        hkNorm Rl (idxOf D j) k P • heckeOn (Rl.MW (idxOf D j) (sg0 D A3.A)) Rr
          ((Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) x))) :
    NExpHeckeRowX Rl cG _ Y H fun _ => LinearMap.id := by
  refine ⟨fun i k P hsp _ hoff h2 hkr α R hα hR x _ => ?_⟩
  obtain ⟨i', hi'⟩ := hoff
  exact hkRow_move Rl (idxOf_succ D i) k P (H.hL ((i : ℕ) + 1) k P x) x ((Y.fi i).e (H.hL ((i : ℕ) + 1) k P x)) ((Y.fi i).e x)
    (hfi i _).symm (hfi i _).symm
    (fun α' R' hα' hR' => hec ((i : ℕ) + 1) k P α' R' (by omega) (by have := i.2; omega)
      ⟨hsp, fun h => hi' (hS i' h), h2, hkr, hα', hR'⟩ x) α R hα hR

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

end GlobalTheory.HeightCounting.Fin3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernIntegralEqCovolumeMulFlagDegree
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.LieBase

theorem hasChernIntegral_covol_flagDeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → HasChernIntegral Eb (openPart j) (lieGram e U hj f₀ A₀) R (GlobalTheory.TrueCx.covol (U.X k) * Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL la R hR
  have h3 := GlobalTheory.LieBase.hasChernIntegral_pointPoly_covol E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have h := GlobalTheory.GoodMetric.hasChernIntegral_of_eq_mul Eb (openPart j) (lieGram e U hj f₀ A₀) R (pointPoly H Dw) _
    (GlobalTheory.TrueCx.covol (U.X k))
    (fun y hy c' hc A hA => GlobalTheory.PointHodge.pointwise_hodge E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
      la R hR y hy c' hc A hA) h3
  rw [mul_comm] at h
  convert h using 3

end GlobalTheory.LieBase
end

