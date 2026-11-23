module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NegRightMulLetterShiftApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnit
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CentreChar

theorem continuous_and_norm_chz : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := fun _ _ _ hψ b₀ =>
  ⟨GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀⟩

end GlobalTheory.CompanionTheory.CentreChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.CentralChar

theorem chz_facts : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
    (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧
      (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  intro D ρ ψ hψ b₀
  refine ⟨fun z z' => ?_, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀, fun z hz => ?_, GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀⟩
  · have e : (HMul.hMul (b₀.1.map (incA D)) (z + z').1 : Mx D ρ ρ) =
        (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) + (HMul.hMul (b₀.1.map (incA D)) z'.1 : Mx D ρ ρ) :=
      Matrix.mul_add _ _ _
    have hadd : ∀ a c : AE D, halfTr (a + c) = halfTr a + halfTr c := fun a c => by
      simp only [halfTr, trA, map_add (f := _), mul_add]
    unfold chz
    rw [e, Matrix.trace_add, hadd, AddChar.map_add_eq_mul]
  · obtain ⟨Z, hZ⟩ := hz
    have hZ' : Z.map (incA D) = z.1 := hZ
    have e : Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) = incA D (Matrix.trace (b₀.1 * Z)) := by
      rw [← hZ', ← Matrix.map_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    unfold chz
    rw [e, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA]
    exact hψ.2.2.1 _

end GlobalTheory.CompanionTheory.FJE.CentralChar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionReal
section
noncomputable section

open Finset Formalism.REAL
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open GlobalTheory.CompanionTheory.PairMult.CenScal (UD Ds eb mi eu xl xl_apply xs_same levRel_xl leftMulLetter negRightMulLetterShift central_letters evB_intertwine
  mem_of_eb center_UD_le glHom glHom_comm glHom_single qdet_map)

namespace GlobalTheory.CompanionTheory.BlockCapelliWords

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

open UniversalEnvelopingAlgebra

variable {n : ℕ}

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (X : Fin n → Fin n → A) (f : Fin t → Fin n)
    (hf : Function.Injective f) (u : ℂ) : qminor X f f u = qdet (fun i k => X (f i) (f k)) u := by
  unfold qdet qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp [Tm, hf.eq_iff]

theorem qminor_of_size_zero {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (ht : t = 0) (X : Fin n → Fin n → A)
    (f : Fin t → Fin n) (u : ℂ) : qminor X f f u = 1 := by
  subst ht
  simp [qminor]

theorem blkE_injective (lev : Fin n → ℕ) (j : ℕ) : Function.Injective (blkE lev j) :=
  ((blk lev j).orderEmbOfFin rfl).injective

theorem lev_blkE (lev : Fin n → ℕ) (j : ℕ) (i : Fin (blk lev j).card) : lev (blkE lev j i) = j := by
  have h : blkE lev j i ∈ blk lev j := (blk lev j).orderEmbOfFin_mem rfl i
  exact (Finset.mem_filter.1 h).2

theorem exists_blkE (lev : Fin n → ℕ) (a : Fin n) : ∃ i, blkE lev (lev a) i = a := by
  refine ⟨((blk lev (lev a)).orderIsoOfFin rfl).symm ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩, ?_⟩
  exact congrArg Subtype.val (((blk lev (lev a)).orderIsoOfFin rfl).apply_symm_apply
    ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩)

abbrev numLev (lev : Fin n → ℕ) : ℕ := univ.sup lev + 1

abbrev bd (lev : Fin n → ℕ) : Fin (numLev lev) → ℕ := fun i => (blk lev i).card

def blkEquiv (lev : Fin n → ℕ) : (Σ i, Fin (bd lev i)) ≃ Fin n :=
  Equiv.ofBijective (fun p => blkE lev p.1 p.2) (by
    constructor
    · rintro ⟨i, p⟩ ⟨k, q⟩ h
      have h' : blkE lev i p = blkE lev k q := h
      have hik : i = k := Fin.ext ((lev_blkE lev i p).symm.trans ((congrArg lev h').trans (lev_blkE lev k q)))
      subst hik
      rw [blkE_injective lev i h']
    · intro a
      obtain ⟨i, hi⟩ := exists_blkE lev a
      exact ⟨⟨⟨lev a, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))⟩, i⟩, hi⟩)

def kpWord : FreeAlgebra ℂ (Bool × Fin n × Fin n) →ₐ[ℂ] FreeAlgebra ℂ (Bool × Fin n × Fin n) :=
  FreeAlgebra.lift ℂ fun p => if p.1 then FreeAlgebra.ι ℂ (true, p.2) - FreeAlgebra.ι ℂ (false, p.2)
    else FreeAlgebra.ι ℂ (true, p.2) + FreeAlgebra.ι ℂ (false, p.2)

theorem evLv_eq {V : Type} [AddCommGroup V] [Module ℂ V] (lev : Fin n → ℕ) (F1 F2 : Fin n → Fin n → Module.End ℂ V)
    (b : FreeAlgebra ℂ (Bool × Fin n × Fin n)) :
    evLv lev F1 F2 b = GlobalTheory.CompanionTheory.PairMult.evB lev F1 F2 (kpWord b) := by
  have h : evLv lev F1 F2 = (GlobalTheory.CompanionTheory.PairMult.evB lev F1 F2).comp kpWord := by
    apply FreeAlgebra.hom_ext
    funext x
    obtain ⟨s, p, q⟩ := x
    by_cases hpq : lev p = lev q
    · cases s <;> simp [evLv, kpWord, GlobalTheory.CompanionTheory.PairMult.evB, hpq, pA, kA]
    · cases s <;> simp [evLv, kpWord, GlobalTheory.CompanionTheory.PairMult.evB, hpq]
  rw [h]
  rfl

theorem isLevPairA_of_lRel {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
    {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h : GlobalTheory.CompanionTheory.PairMult.LRel lev F1 F2) : IsLevPairA lev F1 F2 :=
  fun a b c d h1 h2 => ⟨h.1 a b c d h1 h2, h.2.1 a b c d h1 h2, (h.2.2 a b c d h1 h2).eq⟩

theorem lRel_of_isLevPairA {V : Type} [AddCommGroup V] [Module ℂ V] {lev : Fin n → ℕ}
    {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h : IsLevPairA lev F1 F2) : GlobalTheory.CompanionTheory.PairMult.LRel lev F1 F2 :=
  ⟨fun a b c d h1 h2 => (h a b c d h1 h2).1, fun a b c d h1 h2 => (h a b c d h1 h2).2.1,
    fun a b c d h1 h2 => (h a b c d h1 h2).2.2⟩

theorem invLev_kpWord {lev : Fin n → ℕ} {b : FreeAlgebra ℂ (Bool × Fin n × Fin n)} (hb : InvLv lev b) :
    GlobalTheory.CompanionTheory.PairMult.InvLev lev (kpWord b) := by
  intro W _ _ X1 X2 hL p q hpq
  have h := hb W X1 X2 (isLevPairA_of_lRel hL) p q hpq
  rw [evLv_eq] at h
  exact h

theorem exists_rho {M : ℕ} {d : Fin M → ℕ} (e : (Σ i, Fin (d i)) ≃ Fin n) {lev : Fin n → ℕ}
    (he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ)) {W : Type} [AddCommGroup W] [Module ℂ W]
    {X1 X2 : Fin n → Fin n → Module.End ℂ W} (hL : GlobalTheory.CompanionTheory.PairMult.LRel lev X1 X2) :
    ∃ ρ : UD d →ₐ[ℂ] Module.End ℂ W, ∀ i p q, ρ (eb d i p q) = X1 (e ⟨i, p⟩) (e ⟨i, q⟩) := by
  have hl : ∀ i (p q : Fin (d i)), lev (e ⟨i, p⟩) = lev (e ⟨i, q⟩) := fun i p q => by rw [he, he]
  have hG : ∀ i, GlRel (fun p q : Fin (d i) => X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) := fun i a c f g => by
    have := hL.1 (e ⟨i, a⟩) (e ⟨i, c⟩) (e ⟨i, f⟩) (e ⟨i, g⟩) (hl _ _ _) (hl _ _ _)
    simpa only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and] using this
  have hC : ∀ i k, i ≠ k → ∀ (p q : Fin (d i)) (r v : Fin (d k)),
      Commute (X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) (X1 (e ⟨k, r⟩) (e ⟨k, v⟩)) := fun i k hik p q r v => by
    have := hL.1 (e ⟨i, p⟩) (e ⟨i, q⟩) (e ⟨k, r⟩) (e ⟨k, v⟩) (hl _ _ _) (hl _ _ _)
    have n1 : e ⟨i, q⟩ ≠ e ⟨k, r⟩ := fun h => hik (congrArg Sigma.fst (e.injective h))
    have n2 : e ⟨k, v⟩ ≠ e ⟨i, p⟩ := fun h => hik (congrArg Sigma.fst (e.injective h)).symm
    rw [if_neg n1, if_neg n2, sub_zero] at this
    exact sub_eq_zero.1 this
  refine ⟨lift ℂ (DirectSum.toLieAlgebra _
    (fun i => glHom (fun p q : Fin (d i) => X1 (e ⟨i, p⟩) (e ⟨i, q⟩)) (hG i))
    (fun i k hik Z Z' => glHom_comm _ _ (hC i k hik) Z Z')), fun i p q => ?_⟩
  simp only [eb, eu, GlobalTheory.CompanionTheory.PairMult.CenScal.mi_ι, lift_ι_apply]
  refine (GlobalTheory.EnvCentre.toLieAlgebra_of (fun i => GlobalTheory.CompanionTheory.PairMult.CenScal.Gl (d i)) _ _ i _).trans ?_
  exact glHom_single _ (hG i) p q

def capLetter (lev : Fin n → ℕ) (p : ℕ × ℂ) : UD (bd lev) :=
  if h : p.1 < numLev lev then
    mi (bd lev) ⟨p.1, h⟩ (qdet (eu (bd lev ⟨p.1, h⟩)) (p.2 + ((bd lev ⟨p.1, h⟩ : ℂ) - 1) / 2))
  else 1

def capWord (lev : Fin n → ℕ) : FreeAlgebra ℂ (ℕ × ℂ) →ₐ[ℂ] UD (bd lev) := FreeAlgebra.lift ℂ (capLetter lev)

theorem rho_capWord {lev : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W)
    (ρ : UD (bd lev) →ₐ[ℂ] Module.End ℂ W)
    (hρ : ∀ i p q, ρ (eb (bd lev) i p q) = F (blkE lev i p) (blkE lev i q)) (z : FreeAlgebra ℂ (ℕ × ℂ)) :
    ρ (capWord lev z) = evCap lev F z := by
  have h : ρ.comp (capWord lev) = evCap lev F := by
    apply FreeAlgebra.hom_ext
    funext x
    obtain ⟨j, u⟩ := x
    simp only [Function.comp_apply, AlgHom.comp_apply, capWord, evCap, FreeAlgebra.lift_ι_apply, capLetter]
    by_cases hj : j < numLev lev
    · rw [dite_eq_left hj]
      simp only [capS]
      rw [qminor_reindex _ _ (blkE_injective lev j), ← AlgHom.comp_apply, qdet_map]
      congr 1
      funext p q
      exact hρ ⟨j, hj⟩ p q
    · rw [dite_eq_right hj, map_one]
      have hc : (blk lev j).card = 0 := by
        refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun a _ ha => hj ?_)
        rw [← ha]
        exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
      exact (qminor_of_size_zero hc _ _ _).symm
  rw [← h]
  rfl

theorem mem_range_capWord (lev : Fin n → ℕ) {y : UD (bd lev)}
    (hy : y ∈ Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi (bd lev) i (qdet (eu (bd lev i)) u))) :
    ∃ z, capWord lev z = y := by
  have hle : Algebra.adjoin ℂ (⋃ i, Set.range fun u : ℂ => mi (bd lev) i (qdet (eu (bd lev i)) u)) ≤
      (capWord lev).range := by
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.1 hx
    refine ⟨FreeAlgebra.ι ℂ ((i : ℕ), u - ((bd lev i : ℂ) - 1) / 2), ?_⟩
    change capWord lev (FreeAlgebra.ι ℂ _) = _
    simp only [capWord, FreeAlgebra.lift_ι_apply, capLetter]
    rw [dite_eq_left i.2]
    simp
  obtain ⟨z, hz⟩ := hle hy
  exact ⟨z, hz⟩

theorem commutant_block_capelli_words : LeviCommutantWordReduction := by
  intro n lev _ b hb ν hν
  let e := blkEquiv lev
  have he : ∀ i p, lev (e ⟨i, p⟩) = (i : ℕ) := fun i p => lev_blkE lev i p
  let τ : Fin n → ℂ := fun a => (ν a : ℂ)
  have hτ : ∀ a c, lev a = lev c → τ a = τ c := fun a c h => by simp only [τ, hν a c h]
  have hb' := invLev_kpWord hb
  have hl : ∀ i (p q : Fin (bd lev i)), lev (e ⟨i, p⟩) = lev (e ⟨i, q⟩) := fun i p q => by rw [he, he]
  set y := GlobalTheory.CompanionTheory.PairMult.evB lev (leftMulLetter (xl e)) (negRightMulLetterShift (xl e) τ) (kpWord b) 1 with hy
  have hcen : y ∈ Subalgebra.center ℂ (UD (bd lev)) := by
    rw [Subalgebra.mem_center_iff]
    intro g
    have hg : g ∈ Subalgebra.centralizer ℂ {y} := mem_of_eb (bd lev) _ (fun i r v => by
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      have := central_letters (levRel_xl e he) hτ hb' _ _ (hl i r v)
      rw [xl_apply, xs_same] at this
      exact this.symm) g
    rw [Subalgebra.mem_centralizer_iff] at hg
    exact (hg _ rfl).symm
  obtain ⟨z, hz⟩ := mem_range_capWord lev (center_UD_le (bd lev) hcen)
  refine ⟨z, fun H _ _ F1 F2 hL h hh => ?_⟩
  have hL' := lRel_of_isLevPairA hL
  obtain ⟨ρ, hρ⟩ := exists_rho e he hL'
  have hρx : ∀ p q, lev p = lev q → ρ (xl e p q) = F1 p q := by
    intro p q hpq
    obtain ⟨⟨i, p⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨k, q⟩, rfl⟩ := e.surjective q
    rw [he, he] at hpq
    obtain rfl : i = k := Fin.ext hpq
    rw [xl_apply, xs_same, hρ]
  have hcomm : ∀ p q, lev p = lev q → ∀ u, Commute (ρ u) (F2 p q) := fun p q hpq u => by
    have hu : u ∈ (Subalgebra.centralizer ℂ {F2 p q}).comap ρ := mem_of_eb (bd lev) _ (fun i r v => by
      rw [Subalgebra.mem_comap, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      rw [hρ]
      exact (hL'.2.2 _ _ _ _ (hl _ _ _) hpq).eq.symm) u
    rw [Subalgebra.mem_comap, Subalgebra.mem_centralizer_iff] at hu
    exact (hu _ rfl).symm
  have e1 := evB_intertwine (x := xl e) (τ := τ) ρ F1 F2 h hρx hcomm hh (kpWord b) 1
  rw [map_one, Module.End.one_apply] at e1
  rw [evLv_eq, e1, ← hy, ← hz, rho_capWord F1 ρ hρ]

end GlobalTheory.CompanionTheory.BlockCapelliWords
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPartialFourierMean
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

open GlobalTheory.CompanionTheory.PcB (chz_norm continuous_chz)

variable {D : D7} {n ρ p : ℕ}

theorem continuous_adjMx : Continuous (adj : Mx D ρ p → Mx D p ρ) :=
  Continuous.matrix_transpose (Continuous.matrix_map continuous_id GlobalTheory.AnnihBox.continuous_cA')

theorem continuous_bT (hn : ρ + p = n) :
    Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => bT hn u.1 u.2.1 u.2.2 := by
  have h1 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.1 : Mx D ρ ρ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => u.2.1 :=
    continuous_fst.comp continuous_snd
  have h3 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => adj u.2.1 :=
    continuous_adjMx.comp h2
  have h4 : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p => (u.2.2 : Mx D p p) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hbl : Continuous fun u : hermA D ρ × Mx D ρ p × hermA D p =>
      bl hn (u.1 : Mx D ρ ρ) u.2.1 (adj u.2.1) (u.2.2 : Mx D p p) := by
    unfold bl
    exact (Continuous.matrix_fromBlocks h1 h2 h3 h4).matrix_submatrix _ _
  unfold bT
  exact hbl.subtype_mk _

theorem exists_bound_of_isPer (Φ : hermA D n → ℂ) (hΦ : Continuous Φ) (hper : IsPer Φ) :
    ∃ B : ℝ, ∀ x, ‖Φ x‖ ≤ B := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨B, fun x => ?_⟩
  obtain ⟨γ, hγ, hγx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hB _ hγx

private theorem eventually_uniform_continuity_of_isPer (Φ : hermA D n → ℂ) (hΦ : Continuous Φ) (hper : IsPer Φ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ a, ‖Φ (a + v) - Φ a‖ < ε := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  have hc : Continuous fun w : hermA D n × hermA D n => ‖Φ (w.2 + w.1) - Φ w.2‖ :=
    ((hΦ.comp (continuous_snd.add continuous_fst)).sub (hΦ.comp continuous_snd)).norm
  have hev : ∀ᶠ v in 𝓝 (0 : hermA D n), ∀ k ∈ K, ‖Φ (k + v) - Φ k‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have h0 : ‖Φ (k + 0) - Φ k‖ < ε := by
      simpa using hε
    exact (hc.tendsto ((0 : hermA D n), k)).eventually (gt_mem_nhds h0)
  filter_upwards [hev] with v hv a
  obtain ⟨γ, hγ, hγa⟩ := hcov a
  have h1 := hv _ hγa
  rwa [add_assoc, hper γ hγ, hper γ hγ] at h1

private theorem bT_add (hn : ρ + p = n) (z z' : hermA D ρ) (x x' : Mx D ρ p) (y y' : hermA D p) :
    bT hn (z + z') (x + x') (y + y') = bT hn z x y + bT hn z' x' y' := by
  apply Subtype.ext
  show bl hn (z + z').1 (x + x') (GlobalTheory.MixModel.adj (x + x')) (y + y').1 =
    bl hn z.1 x (GlobalTheory.MixModel.adj x) y.1 + bl hn z'.1 x' (GlobalTheory.MixModel.adj x') y'.1
  rw [GlobalTheory.CompanionTheory.PcB.blockMatrix_add', GlobalTheory.MixModel.adj_add]
  rfl

theorem continuous_pm (hn : ρ + p = n) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (hΦ : Continuous Φ)
    (hper : IsPer Φ) : Continuous (pm hn m ψ b₀ Φ) := by
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨B, hB⟩ := exists_bound_of_isPer Φ hΦ hper
    have hchz := continuous_chz hψ b₀
    have hnorm := chz_norm hψ b₀
    obtain ⟨-, -, hz1⟩ := m.hz
    obtain ⟨-, -, hμ1⟩ := m.hμ
    have hlz : m.lz.restrict m.𝓖 Set.univ < ⊤ := by
      rw [Measure.restrict_apply_univ, hz1]; exact ENNReal.one_lt_top
    have hμf : m.μ.restrict m.𝓕 Set.univ < ⊤ := by
      rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top
    haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨hlz⟩
    haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨hμf⟩
    have hrz : (m.lz.restrict m.𝓖 Set.univ).toReal = 1 := by
      rw [Measure.restrict_apply_univ, hz1, ENNReal.toReal_one]
    have hrμ : (m.μ.restrict m.𝓕 Set.univ).toReal = 1 := by
      rw [Measure.restrict_apply_univ, hμ1, ENNReal.toReal_one]
    haveI : OpensMeasurableSpace (Mx D ρ ρ) := ⟨le_rfl⟩
    haveI : OpensMeasurableSpace (Mx D ρ p) := ⟨le_rfl⟩
    haveI : OpensMeasurableSpace (hermA D ρ) := by
      apply Subtype.opensMeasurableSpace
    have hb0 : bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (0 : hermA D p) = 0 := by
      simpa using bT_add hn (0 : hermA D ρ) 0 (0 : Mx D ρ p) 0 (0 : hermA D p) 0
    have hgb : ∀ (x : Mx D ρ p) (y : hermA D p) (z : hermA D ρ),
        ‖Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ B := by
      intro x y z
      rw [norm_mul, Complex.norm_conj, hnorm, mul_one]
      exact hB _
    have hmz : ∀ (x : Mx D ρ p) (y : hermA D p),
        AEStronglyMeasurable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) := by
      intro x y
      have hc : Continuous fun z : hermA D ρ => ((z, (x, y)) : hermA D ρ × Mx D ρ p × hermA D p) :=
        continuous_id.prodMk continuous_const
      exact ((hΦ.comp ((continuous_bT hn).comp hc)).mul
        (Complex.continuous_conj.comp hchz)).aestronglyMeasurable
    have hint : ∀ (x : Mx D ρ p) (y : hermA D p),
        Integrable (fun z => Φ (bT hn z x y) * conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) := fun x y =>
      (integrable_const B).mono' (hmz x y) (ae_of_all _ fun z => hgb x y z)
    have hE : ∀ (y y' : hermA D p) (x x' : Mx D ρ p) (δ : ℝ),
        (∀ a, ‖Φ (a + bT hn 0 (x' - x) (y' - y)) - Φ a‖ ≤ δ) →
        ‖(∫ z in m.𝓖, Φ (bT hn z x' y') * conj (chz ψ b₀ z) ∂m.lz) -
          ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ δ := by
      intro y y' x x' δ hδ
      have hpt : ∀ z : hermA D ρ, ‖Φ (bT hn z x' y') * conj (chz ψ b₀ z) -
          Φ (bT hn z x y) * conj (chz ψ b₀ z)‖ ≤ δ := by
        intro z
        have hs : bT hn z x' y' = bT hn z x y + bT hn 0 (x' - x) (y' - y) := by
          have h := bT_add hn z 0 x (x' - x) y (y' - y)
          have h1 : x + (x' - x) = x' := by abel
          have h2 : y + (y' - y) = y' := by abel
          rw [add_zero, h1, h2] at h
          exact h
        rw [← sub_mul, norm_mul, Complex.norm_conj, hnorm, mul_one, hs]
        exact hδ _
      rw [← integral_sub (hint x' y') (hint x y)]
      have h2 : ‖∫ z, (Φ (bT hn z x' y') * conj (chz ψ b₀ z) -
          Φ (bT hn z x y) * conj (chz ψ b₀ z)) ∂(m.lz.restrict m.𝓖)‖ ≤
          δ * (m.lz.restrict m.𝓖 Set.univ).toReal :=
        norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
      rw [hrz, mul_one] at h2
      exact h2
    have hIB : ∀ (x : Mx D ρ p) (y : hermA D p),
        ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ B := by
      intro x y
      have h : ‖∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz‖ ≤
          B * (m.lz.restrict m.𝓖 Set.univ).toReal :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun z => hgb x y z)
      rwa [hrz, mul_one] at h
    have hIc : ∀ y : hermA D p,
        Continuous fun x : Mx D ρ p => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz := by
      intro y
      refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
      have hv : Tendsto (fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y)) (𝓝 x₀) (𝓝 0) := by
        have hc : Continuous fun x : Mx D ρ p => bT hn (0 : hermA D ρ) (x - x₀) (y - y) :=
          (continuous_bT hn).comp
            (continuous_const.prodMk ((continuous_id.sub continuous_const).prodMk continuous_const))
        simpa [hb0] using hc.tendsto x₀
      filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with x hx
      rw [dist_eq_norm]
      exact (hE y y x₀ x (ε / 2) fun a => (hx a).le).trans_lt (half_lt_self hε)
    have hin : ∀ y : hermA D p, Integrable
        (fun x => ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) (m.μ.restrict m.𝓕) := fun y =>
      (integrable_const B).mono' (hIc y).aestronglyMeasurable (ae_of_all _ fun x => hIB x y)
    unfold pm
    refine continuous_iff_continuousAt.2 fun y₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
    have hv : Tendsto (fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀)) (𝓝 y₀) (𝓝 0) := by
      have hc : Continuous fun y : hermA D p => bT hn (0 : hermA D ρ) (0 : Mx D ρ p) (y - y₀) :=
        (continuous_bT hn).comp
          (continuous_const.prodMk (continuous_const.prodMk (continuous_id.sub continuous_const)))
      simpa [hb0] using hc.tendsto y₀
    filter_upwards [hv.eventually (eventually_uniform_continuity_of_isPer Φ hΦ hper (half_pos hε))] with y hy
    rw [dist_eq_norm, ← integral_sub (hin y) (hin y₀)]
    have hpt : ∀ x : Mx D ρ p, ‖(∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) -
        ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz‖ ≤ ε / 2 := by
      intro x
      refine hE y₀ y x x (ε / 2) fun a => ?_
      rw [sub_self]
      exact (hy a).le
    have h2 : ‖∫ x, ((∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz) -
        ∫ z in m.𝓖, Φ (bT hn z x y₀) * conj (chz ψ b₀ z) ∂m.lz) ∂(m.μ.restrict m.𝓕)‖ ≤
        ε / 2 * (m.μ.restrict m.𝓕 Set.univ).toReal :=
      norm_integral_le_of_norm_le_const (ae_of_all _ hpt)
    rw [hrμ, mul_one] at h2
    exact h2.trans_lt (half_lt_self hε)
end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterOrthogonalityStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_character_orthogonality : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ, Summable (fun η => ‖a η‖) → Summable (fun η => ‖b η‖) → ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt η) * a η) * conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ) * b ξ) ∂m.μ = ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.parseval | exact GlobalTheory.CompanionTheory.FJE.parseval | (intros; apply GlobalTheory.CompanionTheory.FJE.parseval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDenseStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K_finite_vectors_dense : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), IsSubrep (R (latticeGL E a) μ) H → H ≤ (Submodule.span ℂ {F | F ∈ H ∧ IsKFinL2 μ F}).topologicalClosure := by
  first | exact @GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | exact GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite | (intros; apply GlobalTheory.CompanionTheory.DenseKFin.le_closure_span_K_finite <;> assumption)
end

