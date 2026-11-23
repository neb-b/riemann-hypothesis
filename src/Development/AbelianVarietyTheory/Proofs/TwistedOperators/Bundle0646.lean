module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0384
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedFiniteDatumEqHeisenbergCombinationVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MovedComb

open GlobalTheory.FinPl (Moves Lat)

variable {D : D7}

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ M : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M) :
    Moves V g Λ M (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := fun i => GlobalTheory.VacMove.mulVec_mem_idAt _ hy i
  constructor
  · intro hyΛ
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V M _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y hyΛ)
  · intro hyM
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ y hy ?_
    refine (h _).2 ?_
    rw [← GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact GlobalTheory.LatVHat.latV_mem_hatL D V M _ _ hyM

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  exact hg

theorem datum_fixed {S T : HSp D} {e a a' : AE D} (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0)
    {b : GA D S} {b' : GA D T} (hb : SuppAt a S b) (hb' : SuppAt a' T b') {Φ : WO S T → ℂ} (hΦ : ∀ x, Φ x ≠ 0 → IsHalf e x) :
    (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) = Φ := by
  funext x
  by_cases hx : IsHalf e x
  · rw [GlobalTheory.StdHalfLat.actO_eq_self_of_half ha ha' (GlobalTheory.StdHalfLat.suppAt_inv' hb) (GlobalTheory.StdHalfLat.suppAt_inv' hb') hx]
  · have h0 : Φ x = 0 := by
      by_contra hne
      exact hx (hΦ x hne)
    rw [h0]
    by_contra hne
    exact hx (GlobalTheory.MovedVac.halfBack D S T _ _ e x (hΦ _ hne))

private theorem actO_actO_inv_inv (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ u) = u := by
  have h1 : mt T h * mt T h⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  have h2 : mt S g * mt S g⁻¹ = 1 := by
    rw [← GlobalTheory.VacMove.mt_mul₀, mul_inv_cancel, GlobalTheory.VacMove.mt_one₀]
  rw [GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
    Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem actO_two_nsmul' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, GlobalTheory.VacMove.actO_eq, GlobalTheory.VacMove.actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : Moves S b Λ M fun _ => True)
    (hb' : Moves T b' Λ' M' fun _ => True) {f₀ : WO S T → ℂ} (hf : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f₀) := by
  obtain ⟨hv1, hv2⟩ := hv
  have key : ∀ w c : WO S T, actO S T b b' c = w → heisO ψ S T c f₀ = f₀ →
      heisO ψ S T w (om (b, b') f₀) = om (b, b') f₀ := by
    intro w c hc hfix
    rw [← hc, ← hW.om_heis b b' c f₀ hf, hfix]
  refine ⟨fun u hu => ?_, fun e he u hu hue => ?_⟩
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    refine key _ (2 • actO S T b⁻¹ b'⁻¹ u) ?_ (hv1 _ hu0)
    rw [actO_two_nsmul', actO_actO_inv_inv]
  · have hu0 := GlobalTheory.VacMove.actO_mem_latO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb') hu
    have hc : IsHalf e (actO S T b⁻¹ b'⁻¹ u) := by
      apply GlobalTheory.MovedVac.halfBack D S T b b' e
      rw [actO_actO_inv_inv]
      exact hue
    exact key u _ (actO_actO_inv_inv S T b b' u) (hv2 e he _ hu0 hc)

theorem om_eq_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e a a' : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (ha : e * (a + cA D a) = 0) (ha' : e * (a' + cA D a') = 0) (hs : SuppAt a S b) (hs' : SuppAt a' T b')
    {Φ f₀ f g : WO S T → ℂ} (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (hg : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) Φ g) :
    om (b, b') f = g := by
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨θ, hθ⟩ := hstd.2.1
  have hfT : IsThetaFunO ψ S T f := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hstd hθ hf hf₀
  have hth := GlobalTheory.VacMove.isThetaAt_moveLat D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b hbf b' hbf' hb hb' e Φ f₀ f
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum he) hf₀ hfT hf
  rw [datum_fixed ha ha' hs hs' hΦ.1] at hth
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm, hg.2 Tm hTm]

private theorem isThetaFunO_and_isLatVac_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT ΛS ΛT f) :
    IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f := by
  exact ⟨h.2.theta, h.2.lat⟩

private theorem moves_negSp_negGA_of_moves {V : HSp D} {g : GA D V} {Λ M : Lat V} (h : Moves V g Λ M fun _ => True) :
    Moves (negSp V) (negGA V g) Λ M fun _ => True := by
  intro y hy
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h y hy

private theorem suppAt_negSp_negGA_of_suppAt {V : HSp D} {a : AE D} {g : GA D V} (h : SuppAt a V g) :
    SuppAt a (negSp V) (negGA V g) := by
  intro i j
  rw [GlobalTheory.ChiGrid.mt_negGA]
  exact h i j

private theorem moved_core_lemma_3 {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hbf : b ∈ GfC S) (hbf' : b' ∈ GfC T)
    (hb : Moves S b Λ M fun _ => True) (hb' : Moves T b' Λ' M' fun _ => True) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (hk : ∃ a, e * (a + cA D a) = 0 ∧ SuppAt a S b)
    (hk' : ∃ a', e * (a' + cA D a') = 0 ∧ SuppAt a' T b') {Φ f₀ f : WO S T → ℂ}
    (hΦ : IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ) (hf₀ : IsThetaFunO ψ S T f₀)
    (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f)
    (c : WO S T →₀ ℂ)
    (hc : ∀ g₀, IsThetaFunO ψ S T g₀ → IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) g₀ →
      IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 g₀ Φ (comb ψ S T c g₀)) :
    om (b, b') f = comb ψ S T c (om (b, b') f₀) := by
  obtain ⟨a, ha, hs⟩ := hk
  obtain ⟨a', ha', hs'⟩ := hk'
  exact om_eq_of_isThetaAt hW hΛ hM hΛ' hM' hbf hbf' hb hb' he ha ha' hs hs' hΦ hf₀ hf
    (hc _ (hW.om_pres _ _ hf₀) (isLatVac_move hW hΛ hM hΛ' hM' hb hb' hf₀ hv))

theorem movedVec_eq_comb : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (d : FinDatum ch.G t p) (c : WO (ch.G.pS p) (ch.G.pT p) →₀ ℂ), d.z = 1 → ch.S.Z.HasVec d → IsCombOf ch.W d c → movedVec t ch.S.toGridChoice d = comb ch.W.ψ _ _ c (ch.W.om p (ch.G.toPair p (ch.S.N.u p.small).1 (ch.S.N.u p.big).1) (ch.S.Z.vac p)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hset ch _ t p hp d c hz hvec hcomb
  have hL := hset.core.lev
  have hnodes := GlobalTheory.FunObj.DefPair.nodes hp
  obtain ⟨f, hf⟩ := hvec
  have hvd : ch.S.Z.vec d = f := by
    unfold GlobalTheory.FunObj.Normal.vec
    rw [GlobalTheory.FunObj.FinDatum.vec_eq ch.W hf, hz, ← Prod.one_eq_mk, map_one]
    rfl
  unfold movedVec
  rw [hvd]
  cases p with
  | chi i j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.chi i j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.chi i j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.Std.selfDual ch.S.N hY))
      (GlobalTheory.ChiGrid.isSelfDualC_neg (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (negGA_mem_GfC _ (ch.S.N.u _).2) (ch.S.N.u _).2
      (moves_negSp_negGA_of_moves (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX))
      d.e_is
      (by
        obtain ⟨a, ha, hs⟩ := GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY
        exact ⟨a, ha, suppAt_negSp_negGA_of_suppAt hs⟩)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      d.sb hf₀ hv hf c hcomb.2.2
  | mu t' i j => exact False.elim hp
  | core i => exact False.elim hp
  | top t' j =>
    have hX := hnodes.1
    have hY := hnodes.2
    obtain ⟨hf₀, hv⟩ := isThetaFunO_and_isLatVac_of_isVacO (ch.S.Z.vac_is (.top t' j) hp)
    exact moved_core_lemma_3 (ch.W.om_is (.top t' j) (by simp only [DefPair, Pair.InRange, Node.InRange] at hp ⊢; omega))
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hX) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hX)
      (GlobalTheory.FunObj.Std.selfDual ch.S.N hY) (GlobalTheory.FunObj.DefNode.selfDual ch.G hL hY)
      (ch.S.N.u _).2 (ch.S.N.u _).2
      (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hX)) (moves_of_hat _ _ _ _ (ch.S.N.u_lat _ hY))
      d.e_is (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hX)
      (GlobalTheory.StdHalfLat.exists_kill ch.S.N (Set.mem_univ t) d hY)
      d.sb hf₀ hv hf c hcomb.2.2

end GlobalTheory.MovedComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)


open Classical in
def PlaceCl (s : ℤˣ) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (ζ : ℂ) : Prop :=
  ∀ e, IsIdemSum e {w} → ∀ (M : Vol ch.G) (hM : M.Is t) (r r₀ h : Pts ch.G),
    OneLoc t w e r (fun j => if j ∈ idx D then sgnAt ch.G t s w j * (repsAt ch.G t w).elt β (D.R.m, j) else 1) →
    OneLoc t w e r₀ (fun j => if j = 0 then (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) j)⁻¹ else 1) →
    (∀ j, j ≤ D.R.m → ∃ δ, IsTilt ch.G j δ ∧ δ⁻¹ * h j ∈ GlobalTheory.FinPl.grpOff _ (· = w.under (𝓞 D.host.F))) →
    ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w).rank b.tgt)) (Fin ((locGrid ch.G t w).rank b.src)) (Kw w) → ℂ),
      (∀ i j x, φ (.ex i j) x = 1) → ∀ v f : SchDown ch.G t, (∀ j, IsThetaFunO ch.W.ψ _ _ (v j)) →
      (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (v j) (fun y => if IsHalf e y then φ (.theta D.R.m j)
        (ch.S.B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩
          (y.map fun a => cpt w (toEAf D a))) else 0) (f j)) →
      ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : I → Combs ch.G),
        (∀ i ∈ S, ∀ j : Fin D.R.m, (d i j).e = e ∧ IsCombOf ch.W (d i j) ((c i).1 j)) →
        (∀ y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (y j)) →
          ∑ i ∈ S, x i * ∏ j, (d i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w) (unitVol w)
            (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt β)
              ((locGrid ch.G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.toGridChoice.colAt t w y) 0) →
        ∀ u, evT (conAt ch.W hM f (h * r)) 1 u 0 = ζ * ∑ i ∈ S, x i * evT (combC ch.W (c i) (conAt ch.W hM v (h * r₀))) 1 u 0

theorem placeAt_iff (s : ℤˣ) : PlaceAt ch s ↔ ∃ (κ : Pl D.host.E → ℂ) (z : T → Pl D.host.E → ℂˣ),
    (∀ t w, z t w ∈ xiVals R.toLevCh t) ∧ (∀ w, w ∉ ch.G.pl.W0 → κ w = 1) ∧
    ∀ t, ∀ w ∈ locPl ch.G t, ∀ β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w), ∃ ζ : ℂ,
      ((w ∈ ch.G.pl.W0 → ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid ch.G t w) (unifAt w) (cosExp ch.G w) (i + 1))) →
        ζ = κ w * (z t w : ℂ)⁻¹) ∧ PlaceCl ch s t w β ζ := Iff.rfl

end GlobalTheory.LocAsm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodGroupsSplitRealFiniteLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowGrpSplit

theorem grpAt_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : GrpAt ch := by
  intro j hj
  have hj' := List.mem_range'_1.1 hj
  obtain ⟨hi, hf, hc, he, hu, hrest⟩ := GlobalTheory.AdelicSplit.adelic_split D (ch.G.V (.grid D.R.m j))
  have hV := ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, by omega⟩ (fun k hk => by
    simp only [Node.grid.injEq] at hk; omega)
  have hlat := congLev_open_compact (ch.G.V (.grid D.R.m j))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (𝔪 := ⊤) top_ne_bot
  have hR : IsClosed ((rowGrp ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) ∧ (∀ a ∈ GinfC _, ∀ b ∈ GfC _, a * b ∈ rowGrp ch.G j → a ∈ rowGrp ch.G j ∧ b ∈ rowGrp ch.G j) ∧
      (∀ μ : Measure (rowGrp ch.G j), μ.IsHaarMeasure → μ.IsInvInvariant) ∧
      ∀ μ : Measure ((rowGrp ch.G j).subgroupOf (GfC _)), μ.IsHaarMeasure → μ.IsInvInvariant := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · rw [show rowGrp ch.G j = _ from dif_pos h1]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).1
      exact ⟨GlobalTheory.jacGrp_isClosed D _ _ _ _, a, b, c⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      rw [show rowGrp ch.G j = _ from (dif_neg h1).trans (dif_pos h2)]
      obtain ⟨a, b, c⟩ := (hrest _ _ _).2 _ _ _
      exact ⟨GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ _ _, a, b, c⟩
  exact
    { clA := hi
      clB := hf
      clR := hR.1
      comm := hc
      prod := he
      split := hR.2.1
      le := inf_le_left
      cpt := hlat.2
      opn := by
        have e : (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) :
            Set (GfC (ch.G.V (.grid D.R.m j)))) = Subtype.val ⁻¹'
            (((ch.G.levMax (.grid D.R.m j)).comap (Lev.finE _) : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) :
              Set (GA D (ch.G.V (.grid D.R.m j)))) := by
          ext x
          exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
        rw [e]
        exact hlat.1.preimage continuous_subtype_val
      uniR := hR.2.2.1
      uniRB := hR.2.2.2
      uniB := hu }

theorem grpAt_big : Big fun ch => GrpAt ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => grpAt_all ch⟩⟩

end GlobalTheory.RowGrpSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCellValueOfStepsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem defTot_smul {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    (M : Vol G) (c : ℂ) (σ : PolCol G × PolRow G →₀ ℂ) (τ : PureDat G t →₀ ℂ) (φ : Fn G (.top 0)) (F : Fn G (.grid 0 D.R.m)) :
    defTot t S M (c • σ) τ φ F = c * defTot t S M σ τ φ F := by
  unfold defTot
  rw [Finsupp.sum_smul_index (by intro P; simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  dsimp only
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring


set_option maxHeartbeats 1600000 in
theorem valAt_of_steps (ch : Choice R) (s : ℤˣ) (hFl : FlatAt ch s) (hT : TensAt ch) (hV : VolAt ch) (hW : WtAt ch s)
    (hFo : FockAt ch) (hB : BasicAt ch) (hO : OneAt ch) (hS : ∀ t a, ch.S.SumOK t (ch.Phi a)) : ValAt ch s := by
  obtain ⟨z1, hz1, hFl⟩ := hFl
  obtain ⟨z2, hz2, hFo⟩ := hFo
  obtain ⟨hBa, hBf, hBM, hBM', hBgood, hBgood', hBc⟩ := hB
  refine ⟨fun t => z1 t * z2 t, fun t => Subgroup.mul_mem _ (hz1 t) (hz2 t), ?_⟩
  intro ρ μ hρμ P p hp
  obtain ⟨c0, hc0⟩ := hW ρ μ hρμ
  obtain ⟨C, hCr, hC⟩ := hFl P.2 p hp
  obtain ⟨σ₀, hσ₀⟩ := hFo C hCr P.1
  refine ⟨c0 • σ₀, ?_⟩
  intro t a τ hτ M hM β hβ b hb M' τ' hM' hτ' y
  obtain ⟨cc, hcc⟩ := hBc t (ch.Phi a) β τ' hτ'
  obtain ⟨ζ, hζ, hid⟩ := hC t (ch.Phi a) τ hτ M hM β b hb τ' cc hτ' hcc
  have hζ' : ζ = ((z1 t : ℂˣ) : ℂ)⁻¹ := hζ (hO t _ β hβ)
  obtain ⟨sc, hsc, hwx⟩ := hc0 t (ch.Phi a) β b hb M M' hM hM'
  have hgood : ∀ d ∈ τ'.support, Good ch.W (combC ch.W (cc d) C) (combR ch.rm (cc d)) := fun d hd =>
    hBgood' C hCr (cc d) (fun j hj => ((hcc d hd).1 ⟨j, hj⟩).1)
  have h1 : tot ch.W hM P τ (colFn ch a) (formTop ch t y) (p * b) = ζ * τ'.sum fun d x =>
      x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    have key := hT t M (hBM t M hM) (colFn ch a) (formTop ch t y) (hBa a) (hBf t y)
      ((SchRow ch.G × SchDown ch.G t) ⊕ PureDat ch.G t) (τ.support.disjSum τ'.support)
      (Sum.elim (fun d => τ d) (fun d => -ζ * τ' d))
      (Sum.elim (fun d => conAt ch.W hM (fockD ch.W t d.2 P.2) (p * b)) (fun d => combC ch.W (cc d) C))
      (Sum.elim Prod.fst (fun d => combR ch.rm (cc d))) ?_ ?_ P.1
    · rw [Finset.sum_disjSum] at key
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib] at key
      unfold tot
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      linear_combination key
    · rintro (d | d) hd
      · exact hBgood t (ch.Phi a) τ hτ M hM d (Finset.inl_mem_disjSum.1 hd) P.2 (p * b)
      · exact hgood d (Finset.inr_mem_disjSum.1 hd)
    · intro u y'
      have e := hid u y'
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum] at e
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, mul_assoc, Finset.sum_neg_distrib]
      rw [e]
      ring
  have h2 : (τ'.sum fun d x => x * per ch.W M t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y)) =
      sProd D sc * τ'.sum fun d x => x * per ch.W M' t (combC ch.W (cc d) C) (combR ch.rm (cc d)) P.1 (colFn ch a) (formTop ch t y) := by
    rw [Finsupp.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hV t M M' sc (hBM t M hM) (hBM' t _ β M' hM') hsc (colFn ch a) (formTop ch t y) (hBa a) (hBf t y) _ _ (hgood d hd) P.1]
    ring
  have h3 := hσ₀ t a β M' (hBM' t _ β M' hM') (hS t a) τ' cc hτ' hcc y
  rw [h1, h2, h3, defTot_smul, hζ', Units.val_mul, mul_inv]
  linear_combination (((z1 t : ℂˣ) : ℂ)⁻¹ * ((z2 t : ℂˣ) : ℂ)⁻¹ *
    defTot t ch.S.toGridChoice M' σ₀ τ' (colFn ch a) (formTop ch t y)) * hwx

end

theorem valAt_big : Big fun ch => ∀ s, FlatAt ch s → TensAt ch → VolAt ch → WtAt ch s → FockAt ch → BasicAt ch → OneAt ch →
    (∀ t a, ch.S.SumOK t (ch.Phi a)) → ValAt ch s :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ s => valAt_of_steps ch s⟩⟩

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestFlippedFiniteTensorRowIsThetaFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlipRowTheta

theorem row_isThetaFunO : Big fun ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ d ∈ τ.support, ∀ i,
    IsThetaFunO ch.W.ψ _ _ (d.1 i) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t Φ τ hτ d hd i
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is
    ((hφ d hd).1 i).2 (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.FlipRowTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHeisenbergCombinationsJointRowGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowCombGood

theorem comb_good : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ C, IsRealFam ch.W C → ∀ c : Combs ch.G, (∀ j, j < D.R.m → IsFinComb (c.1 j)) →
    Good ch.W (combC ch.W c C) (combR ch.rm c) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro C hC c _
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hL := s.core.lev
  refine ⟨fun j hje hj => ?_, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := D.R.m_even
    obtain ⟨l, hl⟩ := hje
    obtain ⟨hv, hs⟩ := hC j ⟨l, hl⟩ hj
    have h1 : IsBiTheta ch.W.ψ _ _ _ (C j) :=
      GlobalTheory.FrComb.biTheta_of_vac (node_isV ch.G hL (X := .top j) (show j ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1)) (show j + 1 ≤ D.R.m by omega)).sd
        (node_isV ch.G hL (X := .top (j + 1 + 1)) (show j + 1 + 1 ≤ D.R.m by omega)).sd hv hs
    exact GlobalTheory.FrCombAny.biTheta_biComb D _ hψ _ _ _ _ h1 _ _
  · exact GlobalTheory.CombThetaAny.main D _ hψ _ _ _ _ (ch.rm.vX_is i D.R.m i.2 le_rfl).2.theta

end GlobalTheory.RowCombGood
end

