module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegTwo
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.WeilBound.CoreStatements.PublishedTheorems.SegmentRepresentations.IsIrreduciblePiTensorSegTerm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0334
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0373

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.ExistsPermOfIsSubquotientJac
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.Perm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_zero_or_d {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i))) :
    ∀ i j, b.1 i j = 0 ∨ b.1 i j = d := by
  intro i j
  by_contra hne
  push_neg at hne
  obtain ⟨h0, hdj⟩ := hne
  have hcusp : IsCuspidal (segTerm σ.ρ l i) :=
    GlobalTheory.LocGL.isCuspidal_twist hσ (GlobalTheory.LocGL.isSmoothChar_absPow _)
  have hsum := b.2.1 i
  simp only [Fintype.card_fin] at hsum
  obtain ⟨j', hj'ne, hj'0⟩ : ∃ j', j' ≠ j ∧ b.1 i j' ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hdj
    rw [Finset.sum_eq_single j (fun j' _ hj' => hall j' hj') (by simp)] at hsum
    exact hsum
  have hpos : 0 < b.1 i j := Nat.pos_of_ne_zero h0
  have hpos' : 0 < b.1 i j' := Nat.pos_of_ne_zero hj'0
  have hbot : unipRad k (f i) ≠ ⊥ := by
    rw [GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff]
    rcases lt_or_gt_of_ne hj'ne with h | h
    · exact ⟨f i ⟨j', ⟨0, hpos'⟩⟩, f i ⟨j, ⟨0, hpos⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩
    · exact ⟨f i ⟨j, ⟨0, hpos⟩⟩, f i ⟨j', ⟨0, hpos'⟩⟩, by rw [blk_apply, blk_apply]; exact h⟩
  have hsub := hcusp.2 l (b.1 i) (f i) hbot
  obtain ⟨S, g, hg⟩ := hs i
  have hnt : ∀ j, Nontrivial (s i j).V := by
    intro j
    haveI := (s i j).irr
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (bot_ne_top : (⊥ : Subrepresentation (s i j).ρ) ≠ ⊤)
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  haveI := GlobalTheory.ProdSupport.nontrivial_piTensor (fun j => (s i j).V) hnt
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (PiTensorProduct ℂ fun j => (s i j).V)
  obtain ⟨x', rfl⟩ := hg x
  obtain ⟨y', rfl⟩ := hg y
  apply hxy
  have : x' = y' := Subtype.ext (Subsingleton.elim _ _)
  rw [this]





end PositivityTheory.Pf1.SegRepC.Perm

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.Published

namespace PositivityTheory.RgGu.NR

namespace RedC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irr_congr {h N : ℕ} {x x' : Fin h → IrrGL (k := k)} (e : x = x') (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (x' a).1 = N, ((prodIrr x hd).IsIrreducible ↔ (prodIrr x' hd').IsIrreducible) := by
  subst e
  exact ⟨hd, Iff.rfl⟩

theorem irr_tw {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (s : ℂ)
    (hi : (prodIrr x hd).IsIrreducible) : (prodIrr (fun a => (x a).nu s) hd).IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv (prodIrrTwistEquiv x hd (absPow k s) (isSmoothChar_absPow s))
    (isIrreducible_twist hi _)

end RedC

open RedC in
set_option maxHeartbeats 800000 in
theorem redCl_ofC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : SomeRed k) (h2 : CuspUnit k) (h3 : GlobalTheory.BZSeg.CuspPairIrr k) : RedCl k := by
  intro y hy N hd hirr
  obtain ⟨ρ, z, hρ, hu, rfl⟩ := h2 y hy
  obtain ⟨s, hs0, hs⟩ := h1 ρ hρ hu
  have hpos : 0 < ρ.1 := hρ.1
  have hs2 : s = 1 / 2 := by
    by_contra hne
    have hd0 : ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 = ∑ a, (![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] a).1 := rfl
    refine hs _ hd0 (h3 _ _ _ hd0 (hρ.nu _) (hρ.nu _) ?_ ?_)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) + 1 = ((-s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      exact hne (by linarith)
    · intro e
      rw [IrrGL.nu_nu, show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring,
        show (s : ℂ) + 1 = ((s + 1 : ℝ) : ℂ) by push_cast; ring] at e
      have := (IrrGL.nu_ofReal_inj hpos).1 e
      linarith
  set t : ℂ := -((z : ℂ) + 1 / 2) with ht
  have key : (fun a => (![ρ.nu (z : ℂ), (ρ.nu (z : ℂ)).nu 1] a).nu t) = ![ρ.nu (-(s : ℂ)), ρ.nu (s : ℂ)] := by
    funext a
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
      rw [IrrGL.nu_nu, IrrGL.nu_nu, hs2, ht]
      congr 1
      push_cast
      ring
  obtain ⟨hd', hiff⟩ := irr_congr key hd
  exact hs N hd' (hiff.1 (irr_tw _ hd t hirr))

theorem rhoNuRho_ofC (h : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    RedCl k) : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := by
  intro k _ _ _ _ d hd σ hσ hirr
  set y : IrrGL (k := k) := IrrGL.of σ.ρ σ.smooth σ.irr with hy
  have hyc : y.IsCusp := IrrGL.isCusp_of.2 ⟨hd, hσ⟩
  let x : Fin 2 → IrrGL (k := k) := fun a => y.nu ((a : ℕ) : ℂ)
  have hx1 : ∀ a, (x a).1 = d := fun _ => rfl
  have hdx : ∑ a, (x a).1 = 2 * d := by
    simp only [hx1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  let φ : ∀ a : Fin 2, (segTerm σ.ρ 2 a).Equiv (x a).rep := fun a =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irr) _).trans (y.twEquiv _ _)
  have E1 := multiProdEquiv (consecBlocks 2 d) φ
  have hdd : ∑ _a : Fin 2, d = 2 * d := by simp
  have hE : consecBlocks 2 d = stdBlocks (fun _ : Fin 2 => d) hdd := by
    ext ⟨a, i⟩
    rw [consecBlocks_val, stdBlocks_val]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have h3 : (prodIrr x hdx).IsIrreducible := by
    have h4 := GlobalTheory.Parabolic.isIrreducible_of_equiv E1 hirr
    rw [hE] at h4
    exact h4
  have e : x = ![y, y.nu 1] := by
    funext a
    fin_cases a
    · simp [x]
    · simp [x]
  obtain ⟨hd', hiff⟩ := RedC.irr_congr e hdx
  exact h k y hyc (2 * d) hd' (hiff.1 h3)

end PositivityTheory.RgGu.NR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SrEasy
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

private theorem isSmooth_segTerm_segment_jacquet_subquotients {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth ((isSmoothChar_absPow _).comp _ continuous_glDet)

theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have h := GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k l (l * d)
    (fun _ => d)
    (fun a => ⟨σ.V, segTerm σ.ρ l a, isSmooth_segTerm_segment_jacquet_subquotients σ a, isIrreducible_twist σ.irr _⟩)
    (consecBlocks l d)
  exact h

theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have h := hπ (v : V)
  convert h using 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hg
    exact congrArg Subtype.val hg
  · intro hg
    exact Subtype.ext hg

end SrEasy

open SrEasy

private theorem exists_irreducible_subrep_le_of_ne_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hwf : WellFoundedLT (Subrepresentation ρ))
    (T : Subrepresentation ρ) (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation ρ, S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  obtain ⟨S, ⟨hS0, hST⟩, hmin⟩ := hwf.has_min
    {S : Subrepresentation ρ | S.toSubmodule ≠ ⊥ ∧ S.toSubmodule ≤ T.toSubmodule} ⟨T, hT, le_rfl⟩
  refine ⟨S, ?_, hST⟩
  let img : Subrepresentation S.toRepresentation → Subrepresentation ρ := fun U =>
    ⟨U.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨S.toRepresentation g w, U.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hne : (⊥ : Subrepresentation S.toRepresentation) ≠ ⊤ := by
    intro h
    apply hS0
    rw [eq_bot_iff]
    intro v hv
    have h1 : (⟨v, hv⟩ : S.toSubmodule) ∈ (⊤ : Subrepresentation S.toRepresentation).toSubmodule :=
      show _ ∈ (⊤ : Submodule ℂ S.toSubmodule) from Submodule.mem_top
    rw [← h] at h1
    have h0 : (⟨v, hv⟩ : S.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 h1
    have h2 : v = 0 := congrArg Subtype.val h0
    rw [h2]
    exact Submodule.zero_mem _
  refine { exists_pair_ne := ⟨⊥, ⊤, hne⟩, eq_bot_or_eq_top := fun U => ?_ }
  by_cases hU : U.toSubmodule = ⊥
  · left
    exact Subrepresentation.ext hU
  · right
    have himg0 : (img U).toSubmodule ≠ ⊥ := by
      intro h
      apply hU
      apply Submodule.map_injective_of_injective S.toSubmodule.injective_subtype
      rw [Submodule.map_bot]
      exact h
    have himgS : img U ≤ S := by
      rintro _ ⟨w, _, rfl⟩
      exact w.2
    have heq : img U = S := by
      by_contra hne'
      exact hmin (img U) ⟨himg0, le_trans himgS hST⟩ (lt_of_le_of_ne himgS hne')
    apply Subrepresentation.ext
    apply eq_top_iff.2
    intro w _
    have hw : (w : V) ∈ (img U).toSubmodule := by
      rw [heq]
      exact w.2
    obtain ⟨u, hu, hu'⟩ := hw
    have : u = w := Subtype.ext hu'
    rw [← this]
    exact hu


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  have hfl := hasFiniteLength_prod (l := l) σ
  rw [hasFiniteLength_iff_wellFounded] at hfl
  exact exists_irreducible_subrep_le_of_ne_bot hfl.2 T hT


set_option synthInstance.maxHeartbeats 400000 in
theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  PositivityTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2

private theorem hasFiniteLength_subrepresentation {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : HasFiniteLength π) (S : Subrepresentation π) :
    HasFiniteLength S.toRepresentation :=
  GlobalTheory.ProdLength.hasFiniteLength_of_injective
    (LinearMap.intertwiningMap_of_isIntertwiningMap S.toRepresentation π S.toSubmodule.subtype
      (fun _ _ => rfl))
    (fun a b h => Subtype.ext h) hπ


set_option synthInstance.maxHeartbeats 400000 in
theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) (hasFiniteLength_subrepresentation (hasFiniteLength_prod σ) S)

end PositivityTheory.RgGu.SRC

end
end

