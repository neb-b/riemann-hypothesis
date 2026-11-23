module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

variable {D : D7}

section Rescale

variable {S S₀ : HSp D} {ρ : ℕ}

theorem sandwich {m n : ℕ} (A : Matrix (Fin S.rank) (Fin m) D.host.E) (B : Matrix (Fin S.rank) (Fin n) D.host.E)
    (P : Matrix (Fin m) (Fin m) D.host.E) (Q : Matrix (Fin n) (Fin n) D.host.E) :
    (A * P)ᴴ * S.gram * (B * Q) = Pᴴ * (Aᴴ * S.gram * B) * Q := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def diagDec (d : HypDec S S₀ ρ) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * diagonal l
  e' := d.e' * diagonal fun a => (star (l a))⁻¹
  i₀ := d.i₀
  ee := by rw [sandwich, d.ee, Matrix.mul_zero, Matrix.zero_mul]
  e'e' := by rw [sandwich, d.e'e', Matrix.mul_zero, Matrix.zero_mul]
  e'e := by
    rw [sandwich, d.e'e, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    intro a
    simpa only [Pi.star_apply, star_inv₀, star_star] using inv_mul_cancel₀ (hl a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

theorem perp_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0)
    (x : Fin S.rank → D.host.E) (hx : ((e * diagonal l)ᴴ * S.gram).mulVec x = 0) : (eᴴ * S.gram).mulVec x = 0 := by
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← mulVec_mulVec] at hx
  funext j
  have := congrFun hx j
  rw [mulVec_diagonal] at this
  simp only [Pi.zero_apply, Pi.star_apply, mul_eq_zero, star_eq_zero] at this
  rcases this with h | h
  · exact absurd h (hl j)
  · exact h

theorem flagGen_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) (g : GA D S)
    (hg : (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = (e.map (incA D)).mulVec a) :
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => (e * diagonal l) k i) = ((e * diagonal l).map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = ((e * diagonal l).map (incA D)).mulVec a := by
  have hmv : ∀ a : Fin ρ → AE D, ((e * diagonal l).map (incA D)).mulVec (fun j => incA D (l j)⁻¹ * a j) =
      (e.map (incA D)).mulVec a := fun a => by
    funext k
    simp only [mulVec, dotProduct, Matrix.map_apply, mul_diagonal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc, ← mul_assoc (incA D (l j)), ← map_mul, mul_inv_cancel₀ (hl j), map_one, one_mul]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := hg.1 i
    refine ⟨fun j => incA D (l j)⁻¹ * (incA D (l i) * a j), fun j hj => ?_, ?_⟩
    · show incA D (l j)⁻¹ * (incA D (l i) * a j) = 0
      rw [ha0 j hj, mul_zero, mul_zero]
    have hcol : (ratV fun k => (e * diagonal l) k i) = incA D (l i) • ratV fun k => e k i := by
      funext k
      show incA D ((e * diagonal l) k i) = incA D (l i) * incA D (e k i)
      rw [mul_diagonal, map_mul, mul_comm]
    rw [hcol, mulVec_smul, ha, ← mulVec_smul, ← hmv]
    rfl
  · have h1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) = (e * diagonal l)ᴴ := rfl
    have h2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e = eᴴ := rfl
    rw [h1] at hx
    obtain ⟨a, ha⟩ := hg.2 x (by rw [h2]; exact perp_diag l hl x hx)
    exact ⟨_, ha.trans (hmv a).symm⟩

theorem nFlag_diag (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) :
    NFlag S (e * diagonal l) = NFlag S e := by
  have hl' : ∀ a, (l a)⁻¹ ≠ 0 := fun a => inv_ne_zero (hl a)
  have e0 : diagonal l * diagonal (fun a => (l a)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hl a)
  have e1 : e * diagonal l * diagonal (fun a => (l a)⁻¹) = e := by
    rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  unfold NFlag
  congr 1
  ext g
  refine ⟨fun h => ?_, fun h => flagGen_diag l hl g h⟩
  have := flagGen_diag (e := e * diagonal l) (fun a => (l a)⁻¹) hl' g h
  rwa [e1] at this

def trMeas {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) : Measure N' := h ▸ ν

def trSet {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (𝓝 : Set N) : Set N' := h ▸ 𝓝

theorem isUnit_trans {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) (𝓝 : Set N)
    (hu : ν.IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν ∧ ν 𝓝 = 1) :
    (trMeas h ν).IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N') (trSet h 𝓝) (trMeas h ν) ∧
      trMeas h ν (trSet h 𝓝) = 1 := by
  subst h
  exact hu

def volNOf {S₀' : HSp D} {ρ' : ℕ} {d : HypDec S S₀ ρ} {d' : HypDec S S₀' ρ'} (h : NFlag S d.e = NFlag S d'.e)
    (v : VolN d) : VolN d' :=
  ⟨trMeas h v.ν, trSet h v.𝓝, isUnit_trans h v.ν v.𝓝 v.unit⟩

end Rescale

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj

variable {T : Type}

noncomputable def splitFam {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).Fam S → p.Fam S × q.Fam S
  | _, .nil, d => (d, ())
  | _, .snoc _ q, d => ((splitFam q d.1).1, ((splitFam q d.1).2, d.2))

theorem all_splitFam {S : Arrow T → Type} (P : ∀ a, S a → Prop) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S), Path.Fam.All P d →
      Path.Fam.All P (splitFam q d).1 ∧ Path.Fam.All P (splitFam q d).2
  | _, .nil, _, h => ⟨h, trivial⟩
  | _, .snoc _ q, d, h => ⟨(all_splitFam P q d.1 h.1).1, (all_splitFam P q d.1 h.1).2, h.2⟩

noncomputable def getD {S : Arrow T → Type} (t : T) (i : ℕ) : ∀ (n : ℕ), (downPath t i n).Fam S → ∀ j, j < n → S (.down t i j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, j, h =>
    if hj : j < n then getD t i n (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2 j hj
    else (show n = j by omega) ▸ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2

theorem getD_all {S : Arrow T → Type} (P : ∀ a, S a → Prop) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S), Path.Fam.All P d → ∀ j (h : j < n), P (.down t i j) (getD t i n d j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, hd, j, h => by
    have hs := all_splitFam P (p := Path.one (.down t i n)) (downPath t i n) d hd
    unfold getD
    split_ifs with hj
    · exact getD_all P t i n _ hs.2 j hj
    · have hnj : n = j := by omega
      subst j
      change P (.down t i n) (splitFam (downPath t i n) d).1.2
      exact hs.1.2

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


variable (G) in
theorem givenLevel_inner (t : T) (w : Pl D.host.E) : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 →
    givenLevel G t w X = GlobalTheory.SplitWeil.KO (Kw w) _
  | (_ + 1, _ + 1), _, _ => rfl
  | (0, _), h, _ => absurd h (by omega)
  | (_ + 1, 0), _, h => absurd h (by omega)

theorem inBasis_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin n') (Kw w))) (hK : K = GlobalTheory.SplitWeil.KO (Kw w) (Fin n')) (hx : inBasis h β w x ∈ K) :
    inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n) := by
  subst h; subst hK; exact hx

theorem isFrame_grid (S : GridChoice W U) : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (S.B.β i D.R.m) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => S.B.isFrame (i + 1) D.R.m (by omega) hi le_rfl

theorem isSelfDual_grid : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).sd

theorem levRow_mem_St (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    finG (G.V (.grid D.R.m D.R.m)) k ∈ St (S.B.β D.R.m D.R.m) := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hfr := isFrame_grid S hm le_rfl
  have hsd := isSelfDual_grid (G := G) hm le_rfl
  have hU : finG (G.V (.grid D.R.m D.R.m)) k ∈ UA D.sp.cm (G.V (.grid D.R.m D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
  have hP : ∀ w0 ∈ locPl G t, inBasis rfl (S.B.β D.R.m D.R.m) w0 (finG (G.V (.grid D.R.m D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w0) _ := fun w0 hw0 =>
    inBasis_KO _ _ _ _ _ (givenLevel_inner G t w0 (D.R.m, D.R.m) hm hm) (Subgroup.mem_iInf.1 h1 ⟨w0, hw0⟩)
  refine GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis _ _ fun w => ?_
  by_cases hw : ∃ w0 ∈ locPl G t, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
  · obtain ⟨w0, hw0, e⟩ := hw
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
    · exact hP w hw0
    · exact _root_.GlobalTheory.ConjPlaceUnitary.inBasis_conjPl_mem_KO _ _ _ hfr (GlobalTheory.AdIsom.dualL_eq hsd) _ hU w0 (hP w0 hw0)
  · push_neg at hw
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw

theorem hat_stab_of_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (z : Fin n → Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ M.val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  refine ⟨GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M hβ hM z, fun h => ?_⟩
  have e : (M⁻¹).val *ᵥ (M.val *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← e]
  exact GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M⁻¹ hβ (inv_mem hM) _ h

theorem hat_stab_conj (V : HSp D) (u k : GA D V) (Λ M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ (Lev.finE V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hk : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V k).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin V.rank → Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔
      (Lev.finE V (u⁻¹ * k * u)).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have e : (Lev.finE V u).val *ᵥ ((Lev.finE V (u⁻¹ * k * u)).val *ᵥ v) =
      (Lev.finE V k).val *ᵥ ((Lev.finE V u).val *ᵥ v) := by
    rw [map_mul, map_mul, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  refine (hu v).trans ((hk _).trans ?_)
  rw [← e]
  exact (hu _).symm

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Moves V g Λ Λ (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (Formalism.L2.Theta.mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) :=
    GlobalTheory.Core.Mi.FrameMove.mulVec_mem_ideal _ hy
  constructor
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y h1)
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy ?_
    have h2 := GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _ h1
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat] at h2
    exact (h _).2 h2

theorem moves_neg (V : HSp D) (g : GA D V) (Λ : Lat V) {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves V g Λ Λ P) :
    Moves (negSp V) (negGA V g) Λ Λ P := h

theorem moves_cast (S : GridChoice W U) : ∀ (i : ℕ) (e : D.R.m = i) (g : FinPt G (.grid D.R.m D.R.m)),
    Moves (G.V (.grid D.R.m D.R.m)) g.1 (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m)))
      (fun _ => True) →
    Moves (G.V (.grid i D.R.m)) (e ▸ g : FinPt G (.grid i D.R.m)).1 (colLat (S.N.fr (.grid i D.R.m)))
      (colLat (S.N.fr (.grid i D.R.m))) (fun _ => True) := by
  rintro i rfl g h
  exact h

end GlobalTheory.LastRowLat

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

theorem rowPt_mem_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)),
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hk' := hat_stab_of_St _ _ _ (isFrame_grid S hm le_rfl) (levRow_mem_St S t k hk)
  have hg := hat_stab_conj (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1 k.1 _ _
    (S.N.u_lat _ hX) hk'
  have mv : Moves (G.V (.grid D.R.m D.R.m)) ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m)).1
      (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m))) (fun _ => True) :=
    moves_of_hat _ _ _ hg
  have mv2 := moves_cast S _ (lastIx_succ D) _ mv
  have mvS : Moves (G.pS (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).1⁻¹ (S.N.latS (.chi (lastIx D) D.R.m))
      (S.N.latS (.chi (lastIx D) D.R.m)) (fun _ => True) :=
    GlobalTheory.VacMove.moves_inv (moves_neg _ _ _ mv2)
  have mvT : Moves (G.pT (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).2⁻¹ (S.N.latT (.chi (lastIx D) D.R.m))
      (S.N.latT (.chi (lastIx D) D.R.m)) (fun _ => True) := by
    have e2 : (rowPt S k).2 = 1 := rfl
    rw [e2, inv_one]
    intro y _
    rw [GlobalTheory.VacMove.mt_one₀, Matrix.one_mulVec]
  have hl := (lastIx D).2
  have sdS : IsSelfDualC (G.pS (.chi (lastIx D) D.R.m : Pair T)) (S.N.latS (.chi (lastIx D) D.R.m)) :=
    isSelfDualC_neg (OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩))
  have sdT : IsSelfDualC (G.pT (.chi (lastIx D) D.R.m : Pair T)) (S.N.latT (.chi (lastIx D) D.R.m)) :=
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩)
  exact (GlobalTheory.VacMove.mem_latO_iff_actO sdS sdS sdT sdT mvS mvT x).symm

end GlobalTheory.LastRowLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridModulusExactOrderWitness
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
namespace GlobalTheory.ChiGrid.GridData

theorem modul_witness : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), ∀ v ∈ G.pl.S0,
  (∃ m ∈ G.modul, m ∉ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1)) ∧ ∃ m ∈ G.modul, m ∉ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := by
  intro D T L sc G v hv
  classical
  obtain ⟨e, he⟩ := G.pl.w_split v (Finset.mem_insert.2 (G.pl.mem_S0_of_sum_eq.1 hv))
  have hconj : Formalism.DivisionValues.conjPl (G.pl.w v) ≠ G.pl.w v := GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt he

  have eqOf : ∀ (v' : HeightOneSpectrum (𝓞 D.host.F)) (Q : HeightOneSpectrum (𝓞 D.host.E)),
      (G.pl.w v').asIdeal ≤ Q.asIdeal → G.pl.w v' = Q := fun v' Q h =>
    HeightOneSpectrum.ext ((G.pl.w v').isMaximal.eq_of_le Q.isPrime.ne_top h)
  have hmod : G.modul = ∏ v' ∈ G.pl.S0, (G.pl.w v').asIdeal ^ G.pl.depth sc v' := rfl
  refine ⟨?_, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (G.pl.w v).asIdeal ^ (G.pl.depth sc v + 1) := fun m hm => hcon m hm
    rw [hmod, ← Finset.mul_prod_erase _ _ hv] at hle
    set J := ∏ v' ∈ G.pl.S0.erase v, (G.pl.w v').asIdeal ^ G.pl.depth sc v'
    have hd : (G.pl.w v).asIdeal ^ G.pl.depth sc v * (G.pl.w v).asIdeal ∣
        (G.pl.w v).asIdeal ^ G.pl.depth sc v * J := by
      rw [← pow_succ]; exact Ideal.dvd_iff_le.2 hle
    have hJ : (G.pl.w v).asIdeal ∣ J :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ (G.pl.w v).ne_bot)).1 hd
    have hJle : J ≤ (G.pl.w v).asIdeal := Ideal.le_of_dvd hJ
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (G.pl.w v).isPrime).1 hJle
    have hvv := Finset.mem_erase.1 hv'S
    have := eqOf v' (G.pl.w v) (Ideal.IsPrime.le_of_pow_le hpow)
    apply hvv.1
    rw [← G.pl.under_w hvv.2, ← G.pl.under_w hv, this]
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hle : G.modul ≤ (Formalism.DivisionValues.conjPl (G.pl.w v)).asIdeal := fun m hm => hcon m hm
    rw [hmod] at hle
    obtain ⟨v', hv'S, hpow⟩ := (Ideal.IsPrime.prod_le (Formalism.DivisionValues.conjPl (G.pl.w v)).isPrime).1 hle
    have h1 := eqOf v' _ (Ideal.IsPrime.le_of_pow_le hpow)
    have h2 : v' = v := by
      rw [← G.pl.under_w hv'S, ← G.pl.under_w hv, h1, GlobalTheory.ChainTw.ParInv.under_conjPl]
    subst h2
    exact hconj h1.symm

end GlobalTheory.ChiGrid.GridData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem isIdemAt_idemAt {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    Formalism.L2.NTheta.IsIdemAt (idemAt w) w := by
  have h : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w := by
    rcases Good.locPl_cases hw with ⟨a, b⟩ | ⟨-, -, b⟩
    · exact b ▸ G.pl.w_split _ a
    · first
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b h
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h)
  exact Classical.epsilon_spec h

theorem chi_charUnramAt (G : GridData L sc) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∉ G.pl.S0) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.ch.chi k) v :=
  GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw =>
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq k h1 h2) w).2 (G.ch.unr k h1 h2 w (by rwa [hw]))

theorem eta_charUnramAt {μ₀ : T} (hL : L.Is μ₀) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D L.eta v :=
  GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)

theorem attChr_charUnramAt {χ η : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hχ : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ v) (hη : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D η v) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.attChr χ η n) v := by
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul hχ (GlobalTheory.SeeSaw.WeilLines.charUnram_inv hη)
  · exact hχ

theorem notMem_S0_of_no_place_above (G : GridData L sc) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) : v ∉ G.pl.S0 := by
  classical
  intro h
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl
    exact Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ h)
  exact hv _ hw (G.pl.under_w h)

end GlobalTheory.RowVacScalar

theorem GlobalTheory.RowVacScalar.vacScalar_eq_prod : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i : ℕ), i + 1 ≤ D.R.m →
    ∀ q : GA D (G.pS (.chi i D.R.m)) × GA D (G.pT (.chi i D.R.m)), q.1 ∈ GfC (G.pS (.chi i D.R.m)) → q.2 ∈ GfC (G.pT (.chi i D.R.m)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latS (.chi i D.R.m) : Set (Fin (G.pS (.chi i D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ q.1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latS (.chi i D.R.m) : Set (Fin (G.pS (.chi i D.R.m)).rank → D.host.E))) →
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latT (.chi i D.R.m) : Set (Fin (G.pT (.chi i D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ q.2).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi i D.R.m) : Set (Fin (G.pT (.chi i D.R.m)).rank → D.host.E))) →
    ∀ c : ℂ, W.om (.chi i D.R.m) q (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) →
    c = ∏ w : locPl G t, GlobalTheory.RowVacScalar.splitScal G (.chi i D.R.m) w.1 q.1 q.2 := by
  intro D T L sc G W U S μ₀ hL t i hi q hq1 hq2 hS hT c hc
  classical
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have hW := W.om_is (.chi i D.R.m) hp
  have sd := GlobalTheory.RowVertexInv.FactorTheta.selfDual S hi
  have hv := (S.Z.vac_is (.chi i D.R.m) ⟨hi, rfl⟩).2
  have key := _root_.GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW sd.1 sd.2 (locPl G t) (fun w hw => isIdemAt_idemAt hL G t hw)
    (Good.under_injOn hL G t) (fun v hv' => by
      have hχ := chi_charUnramAt G (k := D.R.m - i) (by omega) (by omega) (notMem_S0_of_no_place_above G t hv')
      exact ⟨attChr_charUnramAt hχ (eta_charUnramAt hL v) _, attChr_charUnramAt hχ (eta_charUnramAt hL v) _⟩)
    q.1 hq1 q.2 hq2 hS hT _ hv.theta hv.lat
  have hne := GlobalTheory.RowVertexInv.FactorTheta.vac_ne_zero S hi
  have e1 : c • S.Z.vac (.chi i D.R.m) = (∏ w ∈ locPl G t, splitScal G (.chi i D.R.m) w q.1 q.2) • S.Z.vac (.chi i D.R.m) :=
    hc.symm.trans key
  rw [Finset.prod_coe_sort (locPl G t) (fun w => splitScal G (.chi i D.R.m) w q.1 q.2)]
  exact smul_left_injective ℂ hne e1
end
end

