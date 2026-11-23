module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0605
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseLastInnerVertexInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport

noncomputable section

namespace GlobalTheory.TopLevelInv

theorem pairing_gl_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (κ : GL n k) (u y : n → k) :
    ∑ r, (∑ s, u s * κ.val s r) * (∑ t, (κ⁻¹).val r t * y t) = ∑ r, u r * y r := by
  change (u ᵥ* κ.val) ⬝ᵥ ((κ⁻¹).val *ᵥ y) = u ⬝ᵥ y
  rw [dotProduct_mulVec, vecMul_vecMul, Units.mul_inv, vecMul_one]

theorem phase_eq_of_lastMove {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hB : j + 2 = Γ.m)
    (κ : GL (Fin (topRank Γ (j + 1))) k) (x x' : ColArgs Γ) (e e' : Vars Γ) :
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → x' (j + 1) = x (j + 1) * κ.val →
    (∀ i : Fin (Γ.m - 1), i.val ≠ j → e' i = e i) →
    stepPt (x' j) (e' ⟨j, by omega⟩) = ((embX (Γ.m - 2 - j) κ)⁻¹).val * stepPt (x j) (e ⟨j, by omega⟩) →
    phase x e = phase x' e' := by
  intro hx hx1 he hst
  unfold phase
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  rcases Nat.lt_or_ge i.val j with h | h
  · have hxi : x' i = x i := hx _ (by omega) (by omega)
    have hei : e' i = e i := he _ (by omega)
    have hc : colVar x' e' i = colVar x e i := by
      funext r; simp only [colVar, hxi, hei]
    have hch : ch (stepPt (x' i) (e' i)) = ch (stepPt (x i) (e i)) := by rw [hxi, hei]
    rw [hch, hc]
    congr 1
    split_ifs with hev
    · have hr : rowVar x' e' (i + 1) = rowVar x e (i + 1) := by
        have hne : (i : ℕ) + 1 ≠ j := by
          intro h'
          rw [show Γ.m - 2 - (i : ℕ) = 1 by omega] at hev
          exact Nat.not_even_one hev
        funext s
        have h1 : x' (i + 1) = x (i + 1) := hx _ hne (by omega)
        simp only [rowVar, h1]
        split_ifs with h3
        · rw [he ⟨(i : ℕ) + 1, h3⟩ (by simpa using hne)]
        · rfl
      rw [hr]
    · rfl
  · obtain ⟨i, hi'⟩ := i
    have hij : i = j := by simp only at h hi; omega
    subst hij
    have h0 : Γ.m - 2 - i = 0 := by omega
    have hch : ∀ z : Matrix (Fin (topRank Γ (i + 1)) ⊕ Fin (Γ.m - 2 - i)) (Fin (topRank Γ i) ⊕ Fin (Γ.m - 2 - i + 1)) k,
        ch z = 0 := by
      intro z
      haveI : IsEmpty (Fin (Γ.m - 2 - i)) := ⟨fun l => by have := l.2; omega⟩
      simp [ch]
    rw [hch, hch, zero_add, zero_add]
    simp only [Fin.val_mk]
    rw [if_pos (by rw [h0]; exact ⟨0, rfl⟩), if_pos (by rw [h0]; exact ⟨0, rfl⟩)]
    have hrow : ∀ (z : ColArgs Γ) (f : Vars Γ) s, rowVar z f (i + 1) s = z (i + 1) (topLast Γ (i + 1 + 1)) s := by
      intro z f s
      simp only [rowVar]
      rw [dite_eq_right (by omega)]
    simp only [hrow, hx1, colVar, Fin.val_mk, hst, map_inv]
    rw [← map_inv]
    have hv : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inl b) = g.val a b := fun _ _ _ => rfl
    have hv2 : ∀ (g : GL (Fin (topRank Γ (i + 1))) k) a b,
        (embX (Γ.m - 2 - i) g).val (Sum.inl a) (Sum.inr b) = 0 := fun _ _ _ => rfl
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, hv, hv2, zero_mul, Finset.sum_const_zero, add_zero]
    exact (pairing_gl_inv κ _ _).symm

end GlobalTheory.TopLevelInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

open scoped Pointwise

namespace GlobalTheory.LevFrame

theorem gl_smul_pi_one {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] (k₀ : GL n 𝒪[k]) :
    Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ • (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) =
      Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) := by
  have A : ∀ h : GL n 𝒪[k], ∀ y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)),
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h • y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) := by
    intro h y hy
    have hy' : ∀ j, ∃ c : 𝒪[k], algebraMap 𝒪[k] k c = y j := fun j => Submodule.mem_one.1 (hy j (Set.mem_univ j))
    choose c hc using hy'
    intro i _
    refine Submodule.mem_one.2 ⟨∑ j, h.1 i j * c j, ?_⟩
    show _ = ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).1 *ᵥ y) i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hc]
    rfl
  refine Submodule.ext fun x => (Submodule.mem_smul_pointwise_iff_exists x _ _).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact A k₀ y hy
  · intro hx
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀⁻¹ • x, A _ x hx, ?_⟩
    rw [map_inv, smul_inv_smul]


set_option maxHeartbeats 2000000 in
theorem gl_mem_lev : All fun {D} _ _ {sc} {G} _ _ => ∀ (X : Node), IsSelfDualC (G.V X) (G.Λ X) → ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) → ∀ (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p (G.V X) n),
  β.IsLat (G.Λ X) (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ k₀ : GL n 𝒪[k],
  (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v) →
  β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) ∈ lev G X := by
  intro D hQ T L μ0 hL sc G W M hM X hsd v hv k _ _ _ _ p hpv hid n _ _ β hlat k₀ hk₀
  set g := β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) with hg
  have hff := GlobalTheory.FrameAt.frame_facts D k p (G.V X) n β
  have hgrp : g ∈ grpAt (G.V X) (· = p.v) := (hff.1 g).2 ⟨_, rfl⟩
  have hinK : InK (G.V X) (G.Λ X) (· = p.v) g := by
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hff.2.2.2.1 (G.Λ X) hsd
    have hΛeq : Λ₀ = Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) :=
      Submodule.ext fun x => (hΛ₀ x).trans (hlat x).symm
    rw [hg, hK, hΛeq]
    exact gl_smul_pi_one k₀
  have hsupp : ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) → ∀ i, y i ∈ idAt D (· = p.v) := fun y hy =>
    (((GlobalTheory.FinPl.localComponents D (· = p.v)).2 (G.V X)).2.2.2 (G.Λ X) y hsd.1).1 hy |>.1
  have hmov : ∀ κ, InK (G.V X) (G.Λ X) (· = p.v) κ → ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) →
      (mt (G.V X) κ - 1) *ᵥ y ∈ latV (G.V X) (G.Λ X) (· = p.v) := by
    intro κ hκ y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hκ.2 y (hsupp y hy)).1 hy) hy
  show g ∈ Lev.levA (G.V X) (G.levCong X)
  refine Lev.mem_levA.2 ⟨GlobalTheory.SplitHecke.Stab.mem_GfC p.split (β.gl_supp _), ?_⟩
  show Lev.finE (G.V X) g ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  refine mem_congLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g hgrp (hmov g hinK) x hx) hx
    rwa [sub_add_cancel] at h1
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g⁻¹ (inv_mem hgrp) (hmov g⁻¹ (inK_inv hinK)) _ hx) hx
    rwa [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h1
  · obtain ⟨⟨m, hm, hm'⟩, m₂, hm₂, hm₂'⟩ := _root_.GlobalTheory.ChiGrid.GridData.modul_witness G v hv
    refine GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.modul • G.Λ X) g hgrp (fun y hy => ?_) x hx
    have hz := hmov g hinK y hy
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hsplit : (mt (G.V X) g - 1) *ᵥ y = (fun i => p.e * ((mt (G.V X) g - 1) *ᵥ y) i) +
        (fun i => cA D p.e * ((mt (G.V X) g - 1) *ᵥ y) i) := by
      funext i
      rw [Pi.add_apply, ← add_mul, hsum]
      exact (((_root_.GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1 _).1 (hsupp _ hz i)).symm
    rw [hsplit]
    exact add_mem (_root_.GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem D k p (G.V X) (G.Λ X) n β hlat G.modul (G.pl.depth sc v)
      ⟨m, hm, _root_.GlobalTheory.SplitPtLev.dvd_of_mem_maxIdeal_pow D k p (G.pl.w v) hid _ m hm'⟩ k₀ hk₀ y hy) (_root_.GlobalTheory.ConjPlaceLat.cA_mul_mem_latV_smul D k p (G.pl.w v) hid (G.V X) (G.Λ X) G.modul ⟨m₂, hm₂, hm₂'⟩ _ hz)

end GlobalTheory.LevFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMove
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Outer

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_move (M : Vol G) {K : Subgroup (GL (Fin (G.V (.grid D.R.m D.R.m)).rank) (Lev.EAf D))}
    (hK : M.IsAt (.grid D.R.m D.R.m) K) (k : GA D (G.V (.grid D.R.m D.R.m))) (k' : GA D (G.V (.top D.R.m)))
    (hk : MeasurePreserving (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k) (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)))
    (hk' : Measurable (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k⁻¹))
    (ι : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top D.R.m)))
    (hι : ∀ h, ι h * k' = ι (h * k))
    (P P' : Fn G (.top D.R.m)) (S S' : Fn G (.grid D.R.m D.R.m))
    (hP : ∀ h, P (h * k') = P' h) (hS : ∀ h, S (h * k) = S' h)
    (hPl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, P (ι (γ * h)) = P (ι h))
    (hSl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, S (γ * h) = S h) :
    ∫ h in M.fd (.grid D.R.m D.R.m), P' (ι h) * S' h ∂M.ν (.grid D.R.m D.R.m) =
      ∫ h in M.fd (.grid D.R.m D.R.m), P (ι h) * S h ∂M.ν (.grid D.R.m D.R.m) := by
  rw [← setIntegral_fd_mul_right M hK k hk hk' (fun h => P (ι h) * S h) ?_]
  · congr 1
    funext h
    rw [← hP, ← hS, hι]
  · intro γ hγ h
    simp only [hPl γ hγ h, hSl γ hγ h]

end Outer

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem genPer_move (ch : Choice R)
    {μ0 : T} (hL : R.toLevCh.Is μ0) (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)
    (hMr : ∀ j : Fin D.R.m, ∃ K, M.IsAt (.top j) K) (hMc : ∀ i : Fin (D.R.m + 1), ∃ K, M.IsAt (.grid i D.R.m) K)
    (hd1 : ∀ j, ch.S.toGridChoice.Z.HasVec (d.1 j)) (hd2 : ∀ i, ch.S.toGridChoice.Z.HasVec (d.2 i))
    (hξ : ∀ ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g)
    (hη : ∀ η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (g : Gc D.what₂.Tau (rowSizes D)) (Q Q' : PolCol ch.G × PolRow ch.G)
    (h1 : ∀ j : Fin D.R.m, ch.W.om (.top t j) (ch.G.toPair (.top t j) (ptTop ch.W g j) (ptTop ch.W g (j + 1)))
        (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) =
      ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q'.1 j))
    (h2 : ∀ i : Fin D.R.m, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ptGrid ch.W g i) (ptGrid ch.W g (i + 1)))
        (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) =
      ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q'.2 i))
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) :
    genPer ch t a M d y Q' (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹)
      (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      genPer ch t a M d y Q ξ η := by

  have hfc : ∀ (P : PolCol ch.G) (j : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.top t j)) (ch.G.pT (.top t j))
      (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (P j)) := fun P j =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.top t j) j.2 (d.1 j) (hd1 j)).1 (P j)
  have hfr : ∀ (P : PolRow ch.G) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i D.R.m)) (ch.G.pT (.chi i D.R.m))
      (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (P i)) := fun P i =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.chi i D.R.m) ⟨i.2, rfl⟩ (d.2 i) (hd2 i)).1 (P i)

  have hφ' : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a) = fun x => (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (x * ptTop ch.W g 0) :=
    funext (pairVec_mul_real (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (ptTop_mem ch.W g 0))
  have hF' : formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      fun x => (formGen ch t y η) (x * ptGrid ch.W g 0) :=
    funext (formGen_mul_real ch t y η (ptGrid_mem ch.W g 0))

  have hcol := pathLift_column_translate ch.W M t (ptTop ch.W g) D.R.m le_rfl
    (fun j hj => by
      obtain ⟨K, hK⟩ := hMr ⟨j, hj⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptTop_lt ch.W g hj]
      exact kappa_fst_move ch.W g ⟨j, hj⟩ hK)
    _ _ (hfc Q.1) h1 (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ)
  have hrow := pathLift_row_translate ch.W M (ptGrid ch.W g) D.R.m le_rfl
    (fun i hi => by
      obtain ⟨K, hK⟩ := hMc ⟨i, by omega⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptGrid_le ch.W g (by omega : i < D.R.m + 1)]
      exact kappa_snd_move ch.W g ⟨i, by omega⟩ hK)
    _ _ (hfr Q.2) h2 (formGen ch t y η) (hη η)

  have htop : ∀ h, stabilizerEmbedding ch.G.sp.topDec h * ptTop ch.W g D.R.m = stabilizerEmbedding ch.G.sp.topDec (h * ptGrid ch.W g D.R.m) := by
    intro h
    rw [ptTop_m, kappaTop_apply, ptGrid_le ch.W g (Nat.lt_succ_self D.R.m), GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
    rfl

  obtain ⟨K, hK⟩ : ∃ K, M.IsAt (.grid D.R.m D.R.m) K := hMc (Fin.last D.R.m)
  have hmv : MeasurePreserving (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * ptGrid ch.W g D.R.m)
        (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) ∧
      Measurable (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * (ptGrid ch.W g D.R.m)⁻¹) := by
    rw [ptGrid_le ch.W g (Nat.lt_succ_self D.R.m)]
    exact kappa_snd_move ch.W g (Fin.last D.R.m) hK
  show defPer t ch.S.toGridChoice M Q' d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a))
      (formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹)) =
    defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)
  rw [hφ', hF']
  have hPl := fun (γ : GA D (ch.G.V (.grid D.R.m D.R.m))) (hγ : γ ∈ GQ (ch.G.V (.grid D.R.m D.R.m)))
      (h : GA D (ch.G.V (.grid D.R.m D.R.m))) =>
    (congrArg _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul ch.G.sp.topDec γ h)).trans
      (pathLift_column_leftInvariant ch.W M t D.R.m le_rfl _ (hfc Q.1) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ) _
        (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational ch.G.sp.topDec γ hγ) (stabilizerEmbedding ch.G.sp.topDec h))
  have hSl := pathLift_row_leftInvariant ch.W M D.R.m le_rfl _ (hfr Q.2) (formGen ch t y η) (hη η)
  exact outer_move M hK (ptGrid ch.W g D.R.m) (ptTop ch.W g D.R.m) hmv.1 hmv.2 (stabilizerEmbedding ch.G.sp.topDec) htop _ _ _ _
    hcol hrow hPl hSl

end Main

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridGivenPathTensorMemSubfield
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.GivenField

open GlobalTheory.StepData

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (F : Subfield ℂ)

theorem lam_principal_mem {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) ∈ F := by
  change ((1 : ℂˣ) : ℂ) ∈ F
  rw [Units.val_one]
  exact one_mem F

theorem lam_reindex_mem {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (g : (P.reindex e).J) : (((P.reindex e).lam g : ℂˣ) : ℂ) ∈ F :=
  hP _

theorem lam_step_mem {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F)
    (h : (P.step t μ hμ).J) : (((P.step t μ hμ).lam h : ℂˣ) : ℂ) ∈ F := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact mul_mem (mul_mem (hP _) (inv_mem (hμF _))) (hμF _)

theorem lam_iter_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) : ∀ g, (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) ∈ F := by
  induction j with
  | zero => exact lam_reindex_mem F P _ hP
  | succ j ih => exact lam_reindex_mem F _ _ (lam_step_mem F _ _ _ ih (hμF _))

theorem Phi_mem {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F) (hμF : ∀ x, ((μ x : ℂˣ) : ℂ) ∈ F) (x : Matrix (a ⊕ t) a k) :
    P.Phi t μ x ∈ F := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact mul_mem (hP _) (inv_mem (hμF _))

theorem iterPhi_mem {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, ((P.lam g : ℂˣ) : ℂ) ∈ F)
    (hμF : ∀ j x, ((μ j x : ℂˣ) : ℂ) ∈ F) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    P.iterPhi t μ hμ j x ∈ F :=
  Phi_mem F _ _ (lam_iter_mem F P μ hμ hP hμF j) (hμF _) _

theorem parPhi_mem {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ) (hδ : ∀ x, ((δ x : ℂˣ) : ℂ) ∈ F)
    (x : Matrix (r ⊕ s) (r ⊕ s') k) : parPhi δ x ∈ F := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact zero_mem F
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact inv_mem (hδ _)

theorem indicator_one_mem {X : Type*} (S : Set X) (x : X) : S.indicator (1 : X → ℂ) x ∈ F := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact one_mem F
  · exact zero_mem F

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (w : Pl D.host.E)

theorem muBase_mem (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (c : ℕ) (x : (Kw w)ˣ) :
    (((muBase L c).loc w x : ℂˣ) : ℂ) ∈ F := by
  rcases c with _ | c
  · simp [muBase, HChar.loc]
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simp [HChar.loc]

variable {t : T} (hmu : ∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) (hxi : ∀ x, ((L.xiH t).loc w x : ℂ) ∈ F)
include hmu hxi

theorem stepFn_mem (j : ℕ) (x) : stepFn L t w j x ∈ F := by
  unfold stepFn
  split_ifs
  · refine iterPhi_mem F _ _ _ (lam_principal_mem F) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (muBase_mem F w hmu c y)
  · refine parPhi_mem F _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (hxi y)
  · exact indicator_one_mem F _ _

theorem givenDatum_mem (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : givenDatum t w B Φ b x ∈ F := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_mem F w hmu hxi _ _
    · simp only [givenDatum]
      exact zero_mem F
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_mem F _ _
      · exact zero_mem F
    · simp only [givenDatum]
      exact zero_mem F

end Global

theorem tensor_givenStage_mem : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Subfield ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, ((L.C.mu0 j).loc w x : ℂ) ∈ F) → (∀ x, ((L.xiH t).loc w x : ℂ) ∈ F) → ∀ z : (locGrid G t w).Args, (givenStage t w B Φ).tensor z ∈ F := by
  intro D T L sc G F B t Φ w hmu hxi z
  show ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod ∈ F
  refine list_prod_mem fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact givenDatum_mem F w hmu hxi B Φ b _

end GlobalTheory.GivenField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormPhase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem nfPhase_of_sumOKK : SumOKK → NFPhase := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs _ => ?_⟩⟩
  exact (letI := hS.fin; GlobalTheory.PhaseField.phases_core hS.core.lev ch.S.toGridChoice (GlobalTheory.RowClaim.Test.pde_ne_q hS) hIs.guard)

end GlobalTheory.RowEx

end
end

