module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.MemLeafListOfAllLeaves
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

section Leaves

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_leafList_of_allLeaves {P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves P → ∀ x ∈ t.leafList, P x.1 x.2
  | _, .leaf V z, h, x, hx => by
    simp only [Tr.leafList, List.mem_singleton] at hx
    subst hx
    exact h
  | _, .node t₁ t₂, h, x, hx => by
    simp only [Tr.leafList, List.mem_append] at hx
    rcases hx with hx | hx
    · exact mem_leafList_of_allLeaves t₁ h.1 x hx
    · exact mem_leafList_of_allLeaves t₂ h.2 x hx

theorem mem_parts_of_treeParts {N : ℕ} {t : Tr E N} {P : Pre E N} {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop}
    (ht : TreeParts t P) (hl : t.AllLeaves Q) : ∀ x ∈ parts P, 0 < x.1 ∧ Q x.1 x.2 := by
  intro x hx
  have hx' : x ∈ t.leafList.filter fun y => 0 < y.1 := by
    rw [← ht]
    exact hx
  rw [List.mem_filter] at hx'
  exact ⟨by simpa using hx'.2, mem_leafList_of_allLeaves t hl x hx'.1⟩

end Leaves

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mulK (N : ℕ) (χ : HChar E) : (Kinf E N → ℂ) →ₗ[ℂ] (Kinf E N → ℂ) where
  toFun f k := (chiDet N χ (infGL E N (Unitary.toUnits k)) : ℂ) * f k
  map_add' f g := by
    funext k
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem hasKType_twist {N : ℕ} (χ : HChar E) {K' : Subgroup (GL (Fin N) (Af E))} {W' : Submodule ℂ (Kinf E N → ℂ)}
    {V : Submodule ℂ (Sm E N)} (h : HasType K' W' V) :
    HasKType (W'.map (mulK N χ)) (V.map (mulChi N χ).toLinearMap) := by
  obtain ⟨φ, hφV, hφ0, -, hT⟩ := h
  refine ⟨mulChi N χ φ, Submodule.mem_map_of_mem hφV, ?_, fun g => ?_⟩
  · exact (LinearEquiv.map_ne_zero_iff (mulChi N χ)).2 hφ0
  · have e : (fun k : Kinf E N => ((mulChi N χ φ : Sm E N) : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) =
        (chiDet N χ g : ℂ) • mulK N χ (fun k : Kinf E N => (φ : GA E N → ℂ) (g * infGL E N (Unitary.toUnits k))) := by
      funext k
      simp only [mulChi_apply, map_mul, Units.val_mul, Pi.smul_apply, smul_eq_mul, mulK, LinearMap.coe_mk,
        AddHom.coe_mk]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (hT g))

theorem HasKType.mono {N : ℕ} {W₁ W₂ : Submodule ℂ (Kinf E N → ℂ)} {V : Submodule ℂ (Sm E N)} (h : W₁ ≤ W₂)
    (hV : HasKType W₁ V) : HasKType W₂ V := by
  obtain ⟨φ, hφ, h0, hW⟩ := hV
  exact ⟨φ, hφ, h0, fun g => h (hW g)⟩

end Twist

theorem joinType : JoinType := by
  intro E _ _ _ n μ Ω hΩ
  have : ∀ M, Finite (Ω M) := fun M => (hΩ M).1.to_subtype
  let W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ) := fun N =>
    ⨆ p : Ω N × Fin (n + 1), (p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))
  have hle : ∀ (N k : ℕ) (W' : Submodule ℂ (Kinf E N → ℂ)), W' ∈ Ω N → k ≤ n → W'.map (mulK N (μ ^ k)) ≤ W N :=
    fun N k W' hW' hk => le_iSup (fun p : Ω N × Fin (n + 1) => (p.1 : Submodule ℂ (Kinf E N → ℂ)).map
      (mulK N (μ ^ (p.2 : ℕ)))) (⟨W', hW'⟩, ⟨k, Nat.lt_succ_of_le hk⟩)
  refine ⟨W, fun N => ?_, ?_⟩
  · have : ∀ p : Ω N × Fin (n + 1), FiniteDimensional ℂ
        ((p.1 : Submodule ℂ (Kinf E N → ℂ)).map (mulK N (μ ^ (p.2 : ℕ)))) := fun p => by
      have := (hΩ N).2 _ p.1.2
      infer_instance
    infer_instance
  intro a b hab s₁ s₂ Pa Pb D hc h₁ h₂ i
  have key : ∀ (k : ℕ), k ≤ n → ∀ x : Σ M : ℕ, Submodule ℂ (Sm E M),
      (0 < x.1 ∧ (x.1 = 0 ∨ ∃ K', ∃ W' ∈ Ω x.1, HasType K' W' x.2)) →
      HasKType (W (twPart (μ ^ k) x).1) (twPart (μ ^ k) x).2 := by
    rintro k hk ⟨M, V⟩ ⟨hM, h0 | ⟨K', W', hW', hT⟩⟩
    · exact absurd h0 (Nat.pos_iff_ne_zero.1 hM)
    · exact HasKType.mono (hle M k W' hW' hk) (hasKType_twist (μ ^ k) hT)
  have hmem : (⟨D.N i, D.V i⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ parts D :=
    List.mem_ofFn.2 ⟨i, rfl⟩
  have hj := hc.join
  unfold IsJoin at hj
  rw [hj, List.mem_append, List.mem_map, List.mem_map] at hmem
  rcases hmem with ⟨x, hx, e⟩ | ⟨x, hx, e⟩
  · have := key b (by omega) x (mem_parts_of_treeParts hc.t₁ h₁ x hx)
    rw [e] at this
    exact this
  · have := key a (by omega) x (mem_parts_of_treeParts hc.t₂ h₂ x hx)
    rw [e] at this
    exact this

end PositivityTheory.Rg.BcB.F.Tail

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PScFin
section
noncomputable section
open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PSc

section Gen

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hk_zero' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) : hk ρ K e 0 = 0 := by
  simp [hk]

theorem hk_supp (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (v : V) :
    Function.HasFiniteSupport fun q : GL ι F ⧸ K => e q.out • ρ q.out v := by
  refine (GlobalTheory.CompanionTheory.DiagAvg.finite_cosets K he.1 e he.2.2.1).subset fun q hq => ?_
  intro h0
  exact hq (by simp [show e q.out = 0 from h0])

theorem hk_add' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (v w : V) :
    hk ρ K e (v + w) = hk ρ K e v + hk ρ K e w := by
  unfold hk
  rw [← finsum_add_distrib (hk_supp ρ K e he v) (hk_supp ρ K e he w)]
  exact finsum_congr fun q => by rw [map_add (f := _), smul_add]

theorem hk_smul' (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (c : ℂ) (v : V) :
    hk ρ K e (c • v) = c • hk ρ K e v := by
  unfold hk
  rw [smul_finsum]
  exact finsum_congr fun q => by rw [map_smul, smul_comm]

def hkEnd (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) :
    Module.End ℂ (fixed ρ K) where
  toFun v := ⟨hk ρ K e v.1, ((PositivityTheory.Rg.BcN.F2.Final.hkAlg F ι) K e e he he).2.2 V ρ v.1 v.2 |>.1⟩
  map_add' v w := Subtype.ext (hk_add' ρ K e he v.1 w.1)
  map_smul' c v := Subtype.ext (hk_smul' ρ K e c v.1)

theorem hkEnd_pow (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e) (k : ℕ) :
    ∀ x : fixed ρ K, ((hkEnd ρ K e he ^ k) x).1 = (hk ρ K e)^[k] x.1 := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
    rfl

theorem hk_iter_zero (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (k : ℕ) :
    (hk ρ K e)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, hk_zero', ih]

theorem nonnil_of_pow (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (he : IsHk K e)
    [FiniteDimensional ℂ (fixed ρ K)] (m : ℕ) (hdim : Module.finrank ℂ (fixed ρ K) ≤ m) (u : V) (hu : u ∈ fixed ρ K)
    (hne : (hk ρ K e)^[m] u ≠ 0) : ∀ r : ℕ, ∃ u ∈ fixed ρ K, (hk ρ K e)^[r] u ≠ 0 := by
  intro r
  rcases le_total r m with hr | hr
  · refine ⟨u, hu, fun h0 => hne ?_⟩
    have : m = (m - r) + r := (Nat.sub_add_cancel hr).symm
    rw [this, Function.iterate_add_apply, h0, hk_iter_zero]
  · by_contra hall
    push_neg at hall
    set T := hkEnd ρ K e he
    have hker : LinearMap.ker (T ^ r) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by rw [hkEnd_pow]; exact hall x.1 x.2)
    have e1 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T) (le_trans hdim hr)
    have e2 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := T) hdim
    have hm : (⟨u, hu⟩ : fixed ρ K) ∈ LinearMap.ker (T ^ m) := by
      rw [e2, ← e1, hker]; trivial
    rw [LinearMap.mem_ker] at hm
    apply hne
    have := congrArg Subtype.val hm
    rw [hkEnd_pow] at this
    exact this

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sub_of_pow {n : ℕ} (D : Pre E n) (w : Pl E) (K' : Subgroup (GLw n w)) (e : GLw n w → ℂ) (he : IsHk K' e)
    (P : SmIrr (GLw n w))
    (hkill : ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0)
    (m : ℕ) (hdim : Module.finrank ℂ (fixed (prodAt D w) K') < m) (u : _) (hu : u ∈ fixed (prodAt D w) K')
    (hne : (hk (prodAt D w) K' e)^[m - 1] u ≠ 0) : GlobalTheory.SmGL.IsSubquotient P.ρ (prodAt D w) := by
  have hsm : GlobalTheory.PRep.IsSmooth (prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : GlobalTheory.SmGL.HasFiniteLength (prodAt D w) :=
    PositivityTheory.Rg.BcN.F2.Final.prodFinLen (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i))
      (GlobalTheory.SmGL.stdBlocks D.N D.h) (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth)
      (fun i => (D.σ i w).irred)
  haveI : FiniteDimensional ℂ (fixed (prodAt D w) K') :=
    GlobalTheory.LeviFactor.finiteDimensional_fixed_of_hasFiniteLength
      (fun Y _ _ π hs hi => GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible (w.adicCompletion E) (Fin n) Y π hs hi)
      hsm hfl K' he.1 he.2.1
  refine PositivityTheory.Rg.BcN.F2.Final.subOfNonNil' (w.adicCompletion E) (Fin n) K' e he P.V P.ρ P.smooth P.irred _
    (prodAt D w) hsm hfl ?_ ?_
  · intro W _ _ τ hs hi hsub hemp v hv
    exact hkill ⟨W, τ, hs, hi⟩ hsub hemp v hv
  · exact nonnil_of_pow (prodAt D w) K' e he (m - 1) (by omega) u hu hne

end PositivityTheory.Rg.BcB.F.Tail.PSc

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ProjAlg
section
noncomputable section

namespace PositivityTheory.Rg.BcB.F.Rd

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

def blockEvaluation (s : ι) : Prod' H d →⋆ₐ[ℂ] (H s →L[ℂ] H s) where
  toFun a := a.1 s
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem projAdjoin (gen : Γ → Prod' H d) (s : ι) (X : H s →L[ℂ] H s) :
    StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X}) =
      StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {X}) := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    rintro y (⟨a, rfl⟩ | hy)
    · have hmem : blockEvaluation (H := H) (d := d) s (a : Prod' H d) ∈
          StarSubalgebra.map (blockEvaluation (H := H) (d := d) s) (StarAlgebra.adjoin ℂ (Set.range gen)) :=
        StarSubalgebra.mem_map.2 ⟨a, a.2, rfl⟩
      rw [StarAlgHom.map_adjoin] at hmem
      have hle : StarAlgebra.adjoin ℂ (⇑(blockEvaluation (H := H) (d := d) s) '' Set.range gen) ≤
          StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {X}) := by
        apply StarAlgebra.adjoin_mono
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        exact Or.inl ⟨x, rfl⟩
      exact hle hmem
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr hy)
  · apply StarAlgebra.adjoin_mono
    rintro y (⟨x, rfl⟩ | hy)
    · exact Or.inl ⟨⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩, rfl⟩
    · exact Or.inr hy

end PositivityTheory.Rg.BcB.F.Rd

end
end

