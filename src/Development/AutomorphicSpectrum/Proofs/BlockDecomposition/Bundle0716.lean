module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMaximalCompactOpenCompact
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA GlobalTheory.CompanionTheory.ActTr
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.FactorAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

def fHm (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : Hf E a b →* H E a b :=
  (finGL E a).prodMap (finGL E b)

def epsS {S : Set (Pl E)} (a b : ℕ) : ∀ i : Slot S, GLw a i.pl × GLw b i.pl →* Hf E a b
  | .inl w => (locGL E a w.1).prodMap (locGL E b w.1)
  | .inr w => ((thF E a).comp (locGL E a w.1)).prodMap ((thF E b).comp (locGL E b w.1))

def selS {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : ∀ i : Slot S, LF a b i.pl
  | .inl w => φ₁ w.1
  | .inr w => φ₂ w.1

theorem continuous_thF (n : ℕ) : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

theorem continuous_loc (n : ℕ) (w : Pl E) : Continuous (locGL E n w) :=
  GlobalTheory.EulerTw.continuous_locGL_spl E n w

theorem continuous_epsS {S : Set (Pl E)} (i : Slot S) : Continuous (epsS a b i) := by
  rcases i with w | w
  · exact (continuous_loc a w.1).prodMap (continuous_loc b w.1)
  · exact ((continuous_thF a).comp (continuous_loc a w.1)).prodMap ((continuous_thF b).comp (continuous_loc b w.1))

theorem embT_prod (w : Pl E) : (embT a w).prodMap (embT b w) =
    (fHm E a b).comp (((thF E a).comp (locGL E a w)).prodMap ((thF E b).comp (locGL E b w))) := by
  refine MonoidHom.ext fun m => Prod.ext ?_ ?_
  · exact GlobalTheory.ThetaPull.thetaA_finGL _
  · exact GlobalTheory.ThetaPull.thetaA_finGL _

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) (G : H E a b → ℂ) :
    actS φ₁ φ₂ i G = act ((fHm E a b).comp (epsS a b i)) (K2 a b i.pl) (selS φ₁ φ₂ i) G := by
  rcases i with w | w
  · rfl
  · show act ((embT a w.1).prodMap (embT b w.1)) (K2 a b w.1) (φ₂ w.1) G = _
    rw [embT_prod]
    rfl

theorem pair_maximal_compact_open_compact (w : Pl E) : IsCompact (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsOpen (K2 a b w : Set (GLw a w × GLw b w)) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2,
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1⟩

theorem hecke_of_test {φ : ∀ w : Pl E, LF a b w} (h : IsTestP φ) (w : Pl E) :
    ∃ A : Subgroup (GLw a w × GLw b w), IsOpen (A : Set (GLw a w × GLw b w)) ∧ IsHecke A (φ w) := by
  obtain ⟨K₁, K₂, h₁, h₂, h₃⟩ := h
  exact ⟨(K₁ w).prod (K₂ w), (h₁.1 w).1.prod (h₂.1 w).1, h₃.1 w⟩

theorem hecke_sel {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) (i : Slot S) :
    ∃ A : Subgroup (GLw a i.pl × GLw b i.pl), IsOpen (A : Set (GLw a i.pl × GLw b i.pl)) ∧ IsHecke A (selS φ₁ φ₂ i) := by
  rcases i with w | w
  · exact hecke_of_test h₁ w.1
  · exact hecke_of_test h₂ w.1

theorem locGL_comm {n : ℕ} {w w' : Pl E} (h : w ≠ w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * locGL E n w' g' = locGL E n w' g' * locGL E n w g := by
  have key : ∀ v, GeneralLinearGroup.map (pLoc E v) (locGL E n w g * locGL E n w' g') =
      GeneralLinearGroup.map (pLoc E v) (locGL E n w' g' * locGL E n w g) := fun v => by
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL_of_ne h g', mul_one, one_mul]
    · rw [pLoc_locGL_of_ne hv g, mul_one, one_mul]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key v)

theorem thF_loc {n : ℕ} {w u : Pl E} (h : w = GlobalTheory.ThetaSatake.cw u) (g : GLw n w) :
    ∃ g₀ : GLw n u, thF E n (locGL E n w g) = locGL E n u g₀ := by
  subst h
  exact ⟨_, GlobalTheory.ThetaSatake.theta_locGL u g⟩

theorem cw_cw (w : Pl E) : w = GlobalTheory.ThetaSatake.cw (GlobalTheory.ThetaSatake.cw w) :=
  (GlobalTheory.ThetaPull.conjSrc_conjSrc w).symm

theorem comm_WT {n : ℕ} {w w' : Pl E} (h : w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    locGL E n w g * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * locGL E n w g := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w') g'
  rw [e]
  exact locGL_comm h g g₀

theorem comm_TT {n : ℕ} {w w' : Pl E} (h : GlobalTheory.ThetaSatake.cw w ≠ GlobalTheory.ThetaSatake.cw w') (g : GLw n w) (g' : GLw n w') :
    thF E n (locGL E n w g) * thF E n (locGL E n w' g') = thF E n (locGL E n w' g') * thF E n (locGL E n w g) := by
  obtain ⟨g₀, e⟩ := thF_loc (cw_cw w) g
  obtain ⟨g₁, e'⟩ := thF_loc (cw_cw w') g'
  rw [e, e']
  exact locGL_comm h g₀ g₁

theorem epsS_comm {S : Set (Pl E)} (hS : IsSection S) {i j : Slot S} (hij : i ≠ j)
    (x : GLw a i.pl × GLw b i.pl) (y : GLw a j.pl × GLw b j.pl) :
    epsS a b i x * epsS a b j y = epsS a b j y * epsS a b i x := by
  rcases i with w | w <;> rcases j with w' | w'
  · have hne : w.1 ≠ w'.1 := fun e => hij (congrArg Sum.inl (Subtype.ext e))
    exact Prod.ext (locGL_comm hne _ _) (locGL_comm hne _ _)
  · have hne : w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w'.2.1 w'.2.2 (show GlobalTheory.ThetaSatake.cw w'.1 ∈ S from e ▸ w.2)
    exact Prod.ext (comm_WT hne _ _) (comm_WT hne _ _)
  · have hne : w'.1 ≠ GlobalTheory.ThetaSatake.cw w.1 := fun e =>
      GlobalTheory.CompanionTheory.SuppFinTw.conj_not_mem hS w.2.1 w.2.2 (show GlobalTheory.ThetaSatake.cw w.1 ∈ S from e ▸ w'.2)
    exact Prod.ext (comm_WT hne _ _).symm (comm_WT hne _ _).symm
  · have hne : GlobalTheory.ThetaSatake.cw w.1 ≠ GlobalTheory.ThetaSatake.cw w'.1 := fun e =>
      hij (congrArg Sum.inr (Subtype.ext ((cw_cw w.1).trans ((congrArg GlobalTheory.ThetaSatake.cw e).trans (cw_cw w'.1).symm))))
    exact Prod.ext (comm_TT hne _ _) (comm_TT hne _ _)

theorem selS_conv {S : Set (Pl E)} (φ₁ φ₂ ψ₁ ψ₂ : ∀ w : Pl E, LF a b w) (i : Slot S) :
    selS (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (ψ₁ w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (ψ₂ w)) i =
      fun m => hint (K2 a b i.pl) fun m' => selS φ₁ φ₂ i m' * selS ψ₁ ψ₂ i (m'⁻¹ * m) := by
  rcases i with w | w <;> rfl

theorem actAlg : ActAlg := by
  intro E _ _ _ a b S hS φ₁ φ₂ ψ₁ ψ₂ hφ₁ hφ₂ hψ₁ hψ₂ G G' hG hG' i j
  have hGl : Lev (fHm E a b) G := hG
  have hGl' : Lev (fHm E a b) G' := hG'
  obtain ⟨hK, hKo⟩ := pair_maximal_compact_open_compact (a := a) (b := b) i.pl
  obtain ⟨hKj, hKoj⟩ := pair_maximal_compact_open_compact (a := a) (b := b) j.pl
  obtain ⟨A, hA, hf⟩ := hecke_sel (S := S) hφ₁ hφ₂ i
  obtain ⟨B, hB, hg⟩ := hecke_sel (S := S) hψ₁ hψ₂ i
  obtain ⟨B', hB', hg'⟩ := hecke_sel (S := S) hψ₁ hψ₂ j
  have ci := continuous_epsS (a := a) (b := b) i
  have cj := continuous_epsS (a := a) (b := b) j
  refine ⟨?_, fun c => ?_, fun hij => ?_, ?_⟩
  · rw [actS_eq]
    exact act_lev ci hK hKo hA hf hGl
  · simp only [actS_eq]
    exact act_add hK hKo hA hf (sm_of_lev ci hGl) (sm_of_lev ci hGl') c
  · simp only [actS_eq]
    refine act_comm hK hKo hA hKj hKoj hB' hf hg' (sm_of_lev ci hGl) (sm_of_lev cj hGl) fun x y => ?_
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, epsS_comm hS hij]
  · simp only [actS_eq]
    rw [selS_conv]
    exact act_conv hK hKo hA hB hf hg (sm_of_lev ci hGl)

end GlobalTheory.CompanionTheory.FactorAction

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSecondStep
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.PairT₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₂_eq {F : H E a b → ℂ} {m : GA E a} {φ : Sm E b} (h : φ.1 = fun x => F (m, x)) : sl₂ F m = φ := by
  have hx : ∃ φ : Sm E b, φ.1 = fun x => F (m, x) := ⟨φ, h⟩
  unfold sl₂
  rw [dite_eq_left hx]
  exact Subtype.ext (hx.choose_spec.trans h.symm)

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {F G : H E a b → ℂ}

theorem sl₂_val (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) (x : GA E b) :
    (sl₂ F m).1 x = F (m, x) :=
  congrFun ((hS E a b U₁ U₂ F hF).2 m).2 x

theorem sl₂_mem (hS : PairSlices) (hF : F ∈ pairSpace U₁ U₂) (m : GA E a) : sl₂ F m ∈ U₂ :=
  ((hS E a b U₁ U₂ F hF).2 m).1

theorem ap₂_add (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₂ T (F + G) = ap₂ T F + ap₂ T G := by
  funext x
  have e : sl₂ (F + G) x.1 = sl₂ F x.1 + sl₂ G x.1 := sl₂_eq (by
    funext y
    exact congrArg₂ (· + ·) (sl₂_val hS hF x.1 y) (sl₂_val hS hG x.1 y))
  change (T (sl₂ (F + G) x.1)).1 x.2 = _
  rw [e, map_add (f := _)]
  rfl

theorem ap₂_smul (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (c : ℂ) (hF : F ∈ pairSpace U₁ U₂) :
    ap₂ T (c • F) = c • ap₂ T F := by
  funext x
  have e : sl₂ (c • F) x.1 = c • sl₂ F x.1 := sl₂_eq (by
    funext y
    exact congrArg (c * ·) (sl₂_val hS hF x.1 y))
  change (T (sl₂ (c • F) x.1)).1 x.2 = _
  rw [e, map_smul]
  rfl

theorem ap₂_zero (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) (U₁ : Submodule ℂ (Sm E a))
    (U₂ : Submodule ℂ (Sm E b)) : ap₂ T (0 : H E a b → ℂ) = 0 := by
  have h := ap₂_smul hS T (0 : ℂ) (Submodule.zero_mem (pairSpace U₁ U₂))
  simpa using h

theorem ap₂_sum (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b) {α : Type} (s : Finset α)
    (f : α → H E a b → ℂ) (hf : ∀ j ∈ s, f j ∈ pairSpace U₁ U₂) :
    ap₂ T (∑ j ∈ s, f j) = ∑ j ∈ s, ap₂ T (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₂_zero hS T U₁ U₂
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ap₂_add hS T (hf j (Finset.mem_insert_self j s))
        (Submodule.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ap₂_rt (hS : PairSlices) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b)
    (x : H E a b) : ap₂ T (fun y => F (y * finH g)) x = ap₂ T F (x * finH g) := by
  have e : sl₂ (fun y => F (y * finH g)) x.1 = act (.fin g.2) (sl₂ F (x.1 * finGL E a g.1)) :=
    sl₂_eq (by
      funext y
      exact (sl₂_val hS hF _ _).trans rfl)
  change (T (sl₂ _ x.1)).1 x.2 = (T (sl₂ F (x.1 * finGL E a g.1))).1 (x.2 * finGL E b g.2)
  rw [e, hT _ _ (sl₂_mem hS hF _)]
  rfl

theorem rt_mem (hU : _root_.GlobalTheory.CuspRep.IsStable U₂) (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace (⊤ : Submodule ℂ (Sm E a)) U₂ := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, trivial, act (.fin g.2) φ₂, hU _ _ h₂, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add F G _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem ap₂_mem (hS : PairSlices) {U₂' : Submodule ℂ (Sm E b)} (T : Sm E b →ₗ[ℂ] Sm E b)
    (hTU : ∀ ψ ∈ U₂, T ψ ∈ U₂') (hF : F ∈ pairSpace U₁ U₂) : ap₂ T F ∈ pairSpace U₁ U₂' := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    refine Submodule.subset_span ⟨φ₁, h₁, T φ₂, hTU _ h₂, ?_⟩
    funext x
    have e : sl₂ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.1 = φ₁.1 x.1 • φ₂ := sl₂_eq rfl
    change (T (sl₂ _ x.1)).1 x.2 = _
    rw [e, map_smul]
    rfl
  | zero =>
    rw [ap₂_zero hS T U₁ U₂]
    exact Submodule.zero_mem _
  | add F G hF hG h₁ h₂ =>
    rw [ap₂_add hS T hF hG]
    exact Submodule.add_mem _ h₁ h₂
  | smul r F hF h =>
    rw [ap₂_smul hS T r hF]
    exact Submodule.smul_mem _ r h

theorem ap₂_type (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (fd₁ : FiniteDimensional ℂ W₁)
    (fd₂ : FiniteDimensional ℂ W₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) (hF : F ∈ pairSpace U₁ U₂)
    (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₂ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · have e : (fun y => F (y * finH ((u₁, u₂) : Hf E a b))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    have h := ap₂_rt hS T hT hF (u₁, u₂) x
    rw [e] at h
    exact h.symm
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ |
        ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2}) :=
      GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ fd₁ fd₂
    let ev : GA E b → Sm E b →ₗ[ℂ] ℂ := fun y =>
      (LinearMap.proj y : (GA E b → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E b).subtype
    have h := GlobalTheory.CompanionTheory.LimV.BlockTy.mem_of_separating
      (Submodule.span ℂ {f : Kinf E a × Kinf E b → ℂ | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k => w₁ k.1 * w₂ k.2})
      (fun k : Kinf E a × Kinf E b =>
        act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1)))) ev
      (fun m hm => Subtype.ext (funext hm)) (ev x.2 ∘ₗ T) (fun y => by
        have e : (fun k : Kinf E a × Kinf E b =>
            ev y (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))) =
            fun k => F ((x.1, y) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
          funext fun k => (sl₂_val hS hF _ _).trans rfl
        rw [e]
        exact hty.2 (x.1, y))
    convert h using 2 with k
    have e := hT (.cpt k.2) _ (sl₂_mem hS hF (x.1 * infGL E a (Unitary.toUnits k.1)))
    change _ = (T (act (.cpt k.2) (sl₂ F (x.1 * infGL E a (Unitary.toUnits k.1))))).1 x.2
    rw [e]
    rfl

theorem ap₂_hecke (hS : PairSlices) {ι : Type} [Fintype ι] (hU : _root_.GlobalTheory.CuspRep.IsStable U₂) (T : Sm E b →ₗ[ℂ] Sm E b)
    (hT : ∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) {f : ι → H E a b → ℂ}
    (hf : ∀ i, f i ∈ pairSpace U₁ U₂) (h : HeckeM E a b ι) (c : ℂ) (hh : heckeAct h f = c • f) :
    heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i) := by
  funext i x
  have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • fun y => f j (y * finH g) := by
    funext y
    simp [heckeAct, Finsupp.sum, Finset.sum_apply]
  have e₁ : ap₂ T (heckeAct h f i) = c • ap₂ T (f i) := by
    rw [hh]
    exact ap₂_smul hS T c (hf i)
  have e₂ : ap₂ T (heckeAct h f i) x = ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := by
    rw [e, ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun j _ =>
      Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g), Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ap₂_sum (U₁ := ⊤) (U₂ := U₂) hS T _ _ fun g _ => Submodule.smul_mem _ _ (rt_mem hU (hf j) g),
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ap₂_smul (U₁ := ⊤) (U₂ := U₂) hS T _ (rt_mem hU (hf j) g), Pi.smul_apply, smul_eq_mul,
      ap₂_rt hS T hT (hf j) g x]
  have e₃ : heckeAct h (fun i => ap₂ T (f i)) i x =
      ∑ j, ∑ g ∈ (h i j).support, h i j g * ap₂ T (f j) (x * finH g) := rfl
  rw [e₃, ← e₂, e₁]
  rfl

end GlobalTheory.CompanionTheory.EGlue.PairT₂

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairStep₂ : PairSlices → PairStep₂ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₂ U₂' T f fd₁ fd₂ hU hT hTU hf hty hne
  refine ⟨?_, fun i => PairT₂.ap₂_mem hS T hTU (hf i), fun i => PairT₂.ap₂_type hS fd₁ fd₂ T hT (hf i) (hty i),
    fun h c hh => PairT₂.ap₂_hecke hS hU T hT hf h c hh⟩
  obtain ⟨i, m, φ, hφ, hTφ⟩ := hne
  intro h0
  apply hTφ
  refine Subtype.ext (funext fun y => ?_)
  have e : sl₂ (f i) m = φ := PairT₂.sl₂_eq hφ
  have h1 : ap₂ T (f i) (m, y) = 0 := congrFun (congrFun h0 i) (m, y)
  change (T (sl₂ (f i) m)).1 y = 0 at h1
  rw [e] at h1
  exact h1

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondColumnsMulBlockDiagonal
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem jn_bl {a r : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (g : Mx D t t) :
    mm (jn hn w v) (bl hn 1 0 0 g) = jn hn w (mm v g) := by
  simp only [jn, bl, mm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem jn_c (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases k with k | k <;> simp [jn, c1, c2]

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c1 hn (jn hn w v) = w := by
  ext i j
  simp [jn, c1]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c2 hn (jn hn w v) = v := by
  ext i j
  simp [jn, c2]

theorem first_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c1 hn (mm U (bl hn 1 0 0 g)) = c1 hn U := by
  conv_lhs => rw [← jn_c hn U, jn_bl, first_columns_join_eq]

theorem second_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c2 hn (mm U (bl hn 1 0 0 g)) = mm (c2 hn U) g := by
  conv_lhs => rw [← jn_c hn U, jn_bl, second_columns_join_eq]

theorem map_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (c : ℝ≥0) (hc0 : c ≠ 0)
    (hc : addEquivAddHaarChar φ = c) : μ.map φ = c⁻¹ • μ := by
  haveI : TopologicalSpace.PseudoMetrizableSpace A := inferInstance
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have h4 := addEquivAddHaarChar_smul_map μ φ
  rw [hc] at h4
  conv_rhs => rw [← h4]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]


set_option maxHeartbeats 1200000 in
theorem map_right (a b : ℕ) (μ : Measure (Mx D a b)) (hμ : μ.IsAddHaarMeasure) (g : GL (Fin b) (AE D)) :
    μ.map (fun y => mm y g.1) =
      ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • μ := by
  haveI := hμ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  haveI : IsTopologicalAddGroup (Mx D a b) := i1
  haveI : LocallyCompactSpace (Mx D a b) := i2
  haveI : SecondCountableTopology (Mx D a b) := i3
  haveI : T2Space (Mx D a b) := i4
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g) = absA D (Matrix.GeneralLinearGroup.det g) ^ a := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a b
      (1 : GL (Fin a) (AE D)) g
    simpa using this
  have hA : absA D (Matrix.GeneralLinearGroup.det g) ≠ 0 := (GlobalTheory.CompanionTheory.IwaAd.absA_pos _).ne'
  have e : (fun y : Mx D a b => mm y g.1) = GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g := by
    funext y
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  rw [e, inv_pow]
  exact map_char μ _ _ (pow_ne_zero _ hA) hc

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
end

