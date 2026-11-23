module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoGenericSubquotientsImpossible
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenCoreMain

theorem le_of_not_le_sup {V : Type} [AddCommGroup V] [Module ℂ V] (T A B : Submodule ℂ V)
    (hT : Module.rank ℂ (V ⧸ T) ≤ 1) (hA : ¬ A ≤ B ⊔ T) : B ≤ T := by
  intro b hb
  by_contra hbT
  obtain ⟨a, haA, haBT⟩ := SetLike.not_le_iff_exists.mp hA
  obtain ⟨v₀, hv₀⟩ := rank_le_one_iff.mp hT
  obtain ⟨r, hr⟩ := hv₀ (Submodule.Quotient.mk b)
  obtain ⟨s, hs⟩ := hv₀ (Submodule.Quotient.mk a)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hbT
    rw [zero_smul] at hr
    exact (Submodule.Quotient.mk_eq_zero T).mp hr.symm
  have hmk : Submodule.Quotient.mk (p := T) (a - (s * r⁻¹) • b) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← hr, ← hs, smul_smul,
      mul_assoc, inv_mul_cancel₀ hr0, mul_one, sub_self]
  have ht : a - (s * r⁻¹) • b ∈ T := (Submodule.Quotient.mk_eq_zero T).mp hmk
  apply haBT
  have : a = (s * r⁻¹) • b + (a - (s * r⁻¹) • b) := by abel
  rw [this]
  exact Submodule.add_mem_sup (B.smul_mem _ hb) ht

theorem nonempty_equiv_of_generic {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (T : Submodule ℂ V) (hT : Module.rank ℂ (V ⧸ T) ≤ 1)
    (hsup : ∀ X Y : Subrepresentation ρ,
      (X ⊔ Y).toSubmodule ⊓ T ≤ X.toSubmodule ⊓ T ⊔ Y.toSubmodule ⊓ T)
    (A B C D : Subrepresentation ρ) (hBA : B ≤ A) (hDC : D ≤ C)
    (hAB : (subQuot A B).IsIrreducible) (hCD : (subQuot C D).IsIrreducible)
    (hA : ¬ A.toSubmodule ≤ B.toSubmodule ⊔ T) (hC : ¬ C.toSubmodule ≤ D.toSubmodule ⊔ T) :
    Nonempty ((subQuot A B).Equiv (subQuot C D)) := by
  have hBT : B.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hA
  have hDT : D.toSubmodule ≤ T := le_of_not_le_sup T _ _ hT hC
  have hAT : ¬ A.toSubmodule ≤ T := fun h => hA (h.trans le_sup_right)
  have hCT : ¬ C.toSubmodule ≤ T := fun h => hC (h.trans le_sup_right)
  have hET : ¬ (A ⊓ C).toSubmodule ≤ T := GlobalTheory.T.inf_not_in_codim_one_submodule ρ T hT A C (hsup A C) hAT hCT
  have hEA : A ⊓ C ≤ A := inf_le_left
  have hEC : A ⊓ C ≤ C := inf_le_right
  have hEB : ¬ A ⊓ C ≤ B := fun h => hET (le_trans h hBT)
  have hED : ¬ A ⊓ C ≤ D := fun h => hET (le_trans h hDT)
  have hfillB := _root_.GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot ρ A B (A ⊓ C) hBA hAB hEA hEB
  have hfillD := _root_.GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot ρ C D (A ⊓ C) hDC hCD hEC hED
  obtain ⟨e₁⟩ := _root_.GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup ρ A B (A ⊓ C) hEA hfillB
  obtain ⟨e₂⟩ := _root_.GlobalTheory.CompanionTheory.RepSecondIso.subQuot_equiv_of_sup ρ C D (A ⊓ C) hEC hfillD
  have hiB : (subQuot (A ⊓ C) B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁.symm hAB
  have hiD : (subQuot (A ⊓ C) D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂.symm hCD
  have hnot : ¬ A ⊓ C ≤ (A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D := by
    intro h
    apply hET
    have h3 : ((A ⊓ C) ⊓ B ⊔ (A ⊓ C) ⊓ D).toSubmodule ≤ T := by
      rw [Subrepresentation.toSubmodule_sup, Subrepresentation.toSubmodule_inf,
        Subrepresentation.toSubmodule_inf]
      exact sup_le (inf_le_right.trans hBT) (inf_le_right.trans hDT)
    exact (fun v hv => h3 (h hv) : (A ⊓ C).toSubmodule ≤ T)
  obtain ⟨e₃⟩ := GlobalTheory.T.irreducible_subquotients_equiv_of_not_le ρ (A ⊓ C) B D hiB hiD hnot
  exact ⟨(e₁.symm.trans e₃).trans e₂⟩

end GlobalTheory.CompanionTheory.GenCoreMain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.TopCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  first
  | rfl
  | (ext; simp [GlobalTheory.BZMir.Leib.ePG])

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  have h : GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc a⟩ =
      ((Equiv.sumCongr (finSumFinEquiv.symm : Fin (i + 1) ≃ Fin i ⊕ Fin 1) (Equiv.refl (Fin t))).trans
        ((Equiv.sumAssoc (Fin i) (Fin 1) (Fin t)).trans
          ((Equiv.sumCongr (Equiv.refl (Fin i)) (Equiv.sumComm (Fin 1) (Fin t))).trans
            ((Equiv.sumAssoc (Fin i) (Fin t) (Fin 1)).symm.trans
              ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv)))))
        (Sum.inl (Fin.castSucc a)) := rfl
  rw [h]
  ext
  simp [finSumFinEquiv_symm_apply_castSucc]

theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq]
  exact Fin.castSucc_ne_last _

theorem mem (i t : ℕ) (x : Fin i → k) : uM k (i + t) (topV k i t x) ∈ HPG k i t := by
  show ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k)) ∈
    GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t)
  rw [GlobalTheory.SmGL.mem_parab_iff]
  intro a b p q hba
  cases a <;> cases b
  all_goals first
    | exact absurd hba (by decide)
    | (simp at hba; done)
    | skip
  have hne : GlobalTheory.BZMir.Leib.ePG i t ⟨true, p⟩ ≠ GlobalTheory.BZMir.Leib.ePG i t ⟨false, q⟩ := by
    intro h
    have h' : true = false := congrArg Sigma.fst ((GlobalTheory.BZMir.Leib.ePG i t).injective h)
    cases h'
  have hr := GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_eq i t p
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, Matrix.one_apply_ne hne, zero_add, hr]
  simp only [GlobalTheory.BZMir.colMat]
  split_ifs
  · rw [Fin.lastCases_castSucc]
    simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
  · rfl

theorem fst (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).1 = uM k i x := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = _
  have h1 : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      (1 : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b := by
    simp [Matrix.one_apply]
  have h2 : GlobalTheory.BZMir.colMat k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨false, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) =
      GlobalTheory.BZMir.colMat k i x a b := by
    simp only [GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.Leib.ePG_false_eq_last_iff]
    split_ifs with hb
    · induction a using Fin.lastCases with
      | last => rw [GlobalTheory.BZMir.Leib.ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast c =>
        rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_false_eq, Fin.lastCases_castSucc,
          Fin.lastCases_castSucc]
        simp [GlobalTheory.CompanionTheory.BZPsiPG.topV]
    · rfl
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry,
    GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry, h1, h2]

theorem snd (i t : ℕ) (x : Fin i → k) :
    (pgProj k i t ⟨uM k (i + t) (topV k i t x), mem i t x⟩).2 = 1 := by
  apply Units.ext
  ext a b
  change ((GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨true, b⟩) =
      (1 : Matrix (Fin t) (Fin t) k) a b
  rw [GlobalTheory.CompanionTheory.BZPsiPG.TopCol.entry]
  simp only [GlobalTheory.BZMir.colMat, if_neg (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.ePG_true_ne_last i t b), add_zero]
  simp [Matrix.one_apply]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (x : Fin i → k), ∃ h : uM k (i + t) (topV k i t x) ∈ HPG k i t, pgProj k i t ⟨_, h⟩ = (uM k i x, 1) := by
  intro k _ _ _ _ i t x
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.TopCol.mem i t x,
    Prod.ext (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.fst i t x)
      (GlobalTheory.CompanionTheory.BZPsiPG.TopCol.snd i t x)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.TopCol

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def firstEmb (d : Fin 2 → ℕ) : GL (Fin (d 0)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 0

def secondEmb (d : Fin 2 → ℕ) : GL (Fin (d 1)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 1

theorem firstEmb_comm (d : Fin 2 → ℕ) (g : GL (Fin (d 0)) k) (h : GL (Fin (d 1)) k) :
    firstEmb d g * secondEmb d h = secondEmb d h * firstEmb d g :=
  Pi.mulSingle_commute (f := fun a => GL (Fin (d a)) k) (by decide : (0 : Fin 2) ≠ 1) g h

variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

abbrev whitKer (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Submodule ℂ X :=
  twKer (J.comp (secondEmb d)) (unipB k (Fin (d 1))) (whitChar ψ (d 1))

theorem whitKer_le_comap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) : whitKer ψ d J ≤ (whitKer ψ d J).comap (J (firstEmb d g)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, J (firstEmb d g) v, ?_⟩
  simp only [map_sub, map_smul, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, firstEmb_comm]

def whit2 (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Representation ℂ (GL (Fin (d 0)) k) (X ⧸ whitKer ψ d J) where
  toFun g := (whitKer ψ d J).mapQ (whitKer ψ d J) (J (firstEmb d g)) (whitKer_le_comap ψ d J g)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

theorem whit2_mk (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) (v : X) :
    whit2 ψ d J g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J (firstEmb d g) v) := rfl

theorem whitKer_le_comap_map (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    whitKer ψ d J ≤ (whitKer ψ d J').comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, f v, ?_⟩
  simp [f.isIntertwining]

def whitMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    (whit2 ψ d J).IntertwiningMap (whit2 ψ d J') :=
  .mk ((whitKer ψ d J).mapQ (whitKer ψ d J') f.toLinearMap (whitKer_le_comap_map ψ d f)) (fun g => by
    ext v
    simp [whit2_mk, f.isIntertwining])

end

end GlobalTheory.CompanionTheory.BZNuPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankProductLeOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgGu

theorem rank_twJacquet_multiProd_le_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hH : GlobalTheory.BZMir.Leib.WhitHeredity k) (ψ : AddChar k Circle) (hc : Continuous ψ)
    (h1 : ψ ≠ 1) (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (X : Fin h → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (hs : ∀ a, IsSmooth (π a))
    (hr : ∀ a, Module.rank ℂ (TwJacquet (π a) (unipB k (Fin (d a))) (whitChar ψ (d a))) ≤ 1) :
    Module.rank ℂ (TwJacquet (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  obtain ⟨e⟩ := hH ψ hc h1 h N d hd X π hs
  exact e.rank_eq.le.trans (GlobalTheory.T.tensor_product_rank_le_one _ hr)

theorem rank_twJacquet_prodIrr_le_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k →
    ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (h N : ℕ) (x : Fin h → IrrGL (k := k))
      (hd : ∑ a, (x a).1 = N),
      Module.rank ℂ (TwJacquet (prodIrr x hd) (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 := by
  intro k _ _ _ _ hH hR ψ hc h1 h N x hd
  exact rank_twJacquet_multiProd_le_one hH ψ hc h1 h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)
    (fun a => hR ψ hc h1 (x a).1 (x a).2.rep.V (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)

end GlobalTheory.CompanionTheory.RgGu

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndex
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WittFrame

open Matrix

theorem length_le_wittIdx (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  have hc : ∀ {a : ℕ} (A : Matrix (Fin V.rank) (Fin a) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
    intro a A
    exact Matrix.ext fun i j => rfl
  have hxx : Xfᴴ * V.gram * Xf = 0 := by rw [← hc]; exact hW.xx
  have hxy : Xfᴴ * V.gram * Yf = 1 := by rw [← hc]; exact hW.xy
  have hG : V.gramᴴ = V.gram := by
    refine Matrix.ext fun a b => ?_
    exact V.herm.eq _ _
  have hyx : Yfᴴ * V.gram * Xf = 1 := by
    have h := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f : (Fin r → D.host.E) →ₗ[D.host.E] V.V := V.frame.equivFun.symm.toLinearMap.comp Xf.mulVecLin
  have hf : Function.Injective f := by
    refine V.frame.equivFun.symm.injective.comp (g := V.frame.equivFun.symm) (f := Xf.mulVec) fun v w hvw => ?_
    have := congrArg (Yfᴴ * V.gram).mulVec hvw
    simpa [mulVec_mulVec, hyx] using this
  refine le_csSup (GlobalTheory.SiegelFormula.Model.bddAbove_witt V) ⟨LinearMap.range f, by simpa using LinearMap.finrank_range_of_inj hf, ?_⟩
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  change V.hT (V.frame.equivFun.symm (Xf *ᵥ v)) (V.frame.equivFun.symm (Xf *ᵥ w)) = 0
  rw [GlobalTheory.ParallelWitt.form_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hxx]
  simp

end GlobalTheory.CompanionTheory.WittFrame
end

