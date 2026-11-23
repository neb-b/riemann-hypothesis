module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PChainsc
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lefAt_smul {a b : ℕ} [MeasurableSpace (GL (Fin a) ℂ)] [MeasurableSpace (GL (Fin b) ℂ)]
    {ν₁ : Measure (GL (Fin a) ℂ)} {ν₂ : Measure (GL (Fin b) ℂ)} {l₁ : DomWeight a} {l₂ : DomWeight b}
    {val : ℂ} {ψ : GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ} (c : ℂ) (h : LefAt ν₁ ν₂ l₁ l₂ val ψ) :
    LefAt ν₁ ν₂ l₁ l₂ (c * val) (c • ψ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.const_smul c, h2.mono (Function.support_const_smul_subset c ψ), ?_⟩
  intro d₁ d₂ e₁ e₂
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h3 d₁ d₂ e₁ e₂]
  ring

private theorem prod_update_mul {V : Type*} [Fintype V] [DecidableEq V] (g : V → ℂ) (v₀ : V) (c : ℂ) :
    ∏ v, Function.update g v₀ (c * g v₀) v = c * ∏ v, g v := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀),
    ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ v₀), Function.update_self, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun v hv => Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _

private theorem adel_update {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (S : Set (Pl E))
    (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : InfinitePlace E → GL (Fin a) ℂ × GL (Fin b) ℂ → ℂ)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (v₀ : InfinitePlace E) (c : ℂ) :
    adel S u₁ u₂ (Function.update ψ v₀ (c • ψ v₀)) φ₁ φ₂ = c • adel S u₁ u₂ ψ φ₁ φ₂ := by
  funext x
  simp only [adel, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← prod_update_mul (fun v => ψ v (GeneralLinearGroup.map (cV v) x.1, GeneralLinearGroup.map (cV v) x.2)) v₀ c]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v = v₀
  · subst hv
    simp
  · simp [Function.update_of_ne hv]

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.chainsc_pf :
    FBL.EllHom → ChainSc := by
  intro hE E _ _ _ n μ e lam C S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg val ψ hL s z hz
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hL' : ∀ i v, LefAt (C.νC (C.a i)) (C.νC (n - C.a i)) (C.l₁ i v) (C.l₂ i v)
      (Function.update (val i) v₀ (s i * val i v₀) v) (Function.update (ψ i) v₀ (s i • ψ i v₀) v) := by
    intro i v
    by_cases hv : v = v₀
    · subst hv
      simpa using lefAt_smul (s i) (hL i v)
    · simpa [Function.update_of_ne hv] using hL i v
  have hz' : ∀ i, ∏ v, Function.update (val i) v₀ (s i * val i v₀) v = z := fun i => by
    rw [prod_update_mul, hz i]
  have key := C.eq S hS K' f hK hf u₁ u₂ hu φ₁ φ₂ hφ hreg _ _ hL' z hz'
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [adel_update, hE]

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PHuhecke
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.huhecke_pf :
    HuHecke := by
  intro E _ _ _ n d hd w hw k
  have hU : UL n w = ⊤ := if_pos hw.1
  exact GlobalTheory.CompanionTheory.MatchWord.isHecke_hU d hd hU k

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.PPsigen
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fm_of_eqv {E : Type} [Field E] [NumberField E] [IsCMField E] {κ : Pl E → Type} [∀ w, Fintype (κ w)]
    (S : Set (Pl E)) (P : Finset (Pl E)) (B : Block E) (e : B.κ ≃ ∀ w : P, κ w) {L L' : LM κ B.a B.b}
    (h : L.Eqv P L') : fm S P B e L = fm S P B e L' := by
  have hent : ∀ x y, L.ent P x y = L'.ent P x y := by
    intro x y
    funext w
    unfold LM.ent
    split_ifs with hw
    · rw [h.1 w hw]
    · rw [h.2.1 w hw]
  funext x y g
  simp only [fm, hent, h.2.2]

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiGen_of_algebras :
    FmAlg → RtAlg → BlockProductLevels → PsiGen := by
  intro hFm hRt hLev E _ _ _ κ _ S P B e hS hPS u₁ u₂ L₀ t₀ hL₀ hid ht₀ l hl
  have alg := fun L L' (h : L.Ok P) (h' : L'.Ok P) => hFm E κ S P B e hS hPS L L' h h'
  have hrt := (hRt E B u₁ u₂).1
  have key : ∀ l : List (BGen B × LM κ B.a B.b), (∀ x ∈ l, x.2.Ok P ∧ (L₀.mul x.2).Eqv P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = L₀) ∨ ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm S P B e x.2)) →
      ((l.map Prod.snd).foldr LM.mul L₀).Ok P ∧
      (BGen.wd (l.map Prod.fst) t₀).ψ = rt u₁ u₂ (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀)) ∧
      mulF B.ν (fm S P B e L₀) (fm S P B e ((l.map Prod.snd).foldr LM.mul L₀)) =
        fm S P B e ((l.map Prod.snd).foldr LM.mul L₀) := by
    intro l
    induction l with
    | nil =>
      intro _
      refine ⟨hL₀, ht₀, ?_⟩
      simp only [List.map_nil, List.foldr_nil]
      rw [(alg L₀ L₀ hL₀ hL₀).2.2.1]
      exact fm_of_eqv S P B e hid
    | cons x l ih =>
      intro hx
      obtain ⟨hX, hψ, hu⟩ := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      obtain ⟨hxO, hxE, hxc⟩ := hx x List.mem_cons_self
      simp only [List.map_cons, List.foldr_cons]
      set X := (l.map Prod.snd).foldr LM.mul L₀ with hXdef
      have hOk : (x.2.mul X).Ok P := (alg x.2 X hxO hX).2.1
      have hmul : mulF B.ν (fm S P B e x.2) (fm S P B e X) = fm S P B e (x.2.mul X) := (alg x.2 X hxO hX).2.2.1
      have hunit : mulF B.ν (fm S P B e L₀) (fm S P B e (x.2.mul X)) = fm S P B e (x.2.mul X) := by
        rw [← hmul, ← (hLev E B _ _ _ (alg L₀ x.2 hL₀ hxO).1 (alg x.2 X hxO hX).1 (alg X X hX hX).1).2.2.1,
          (alg L₀ x.2 hL₀ hxO).2.2.1, fm_of_eqv S P B e hxE]
      refine ⟨hOk, ?_, hunit⟩
      rcases hxc with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
      · have hwd : BGen.wd (x.1 :: l.map Prod.fst) t₀ = BGen.wd (l.map Prod.fst) t₀ := by
          simp [BGen.wd, h1]
        rw [hwd, hψ, ← hmul, h2, hu]
      · have hwd : BGen.wd (x.1 :: l.map Prod.fst) t₀ = s.mul (BGen.wd (l.map Prod.fst) t₀) := by
          simp [BGen.wd, h1]
        rw [hwd]
        show mulF B.ν s.ψ (BGen.wd (l.map Prod.fst) t₀).ψ = _
        rw [hψ, h2, hrt, hmul]
  exact (key l hl).2.1

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.TmulPf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.tmul_pf :
    TMul := by
  intro E _ _ _ a b κ _ P _ L L' hL hL'
  refine ⟨fun X Y => ?_, FinConv.isTestFunction_mulConvolution hL.2 hL'.2⟩
  have hoff : IsTestP (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w)) :=
    FinConv.isTestFunction_mulConvolution (hL.1 X X) (hL'.1 Y Y)
  refine Fm.isTestFunction_linearCombination (J := Option (Σ i : P, κ i))
    (fun j => j.elim (fun w => mconv (L.ent P X X w) (L'.ent P Y Y w))
      fun q w => mconv (L.ent P X (Function.update X q.1 q.2) w) (L'.ent P (Function.update X q.1 q.2) Y w))
    (fun j => ?_) _ (fun w => ?_) ?_
  · cases j with
    | none => exact hoff
    | some q => exact FinConv.isTestFunction_mulConvolution (hL.1 _ _) (hL'.1 _ _)
  · by_cases hw : w ∈ P
    · exact ⟨κ w, inferInstance, fun z => some ⟨⟨w, hw⟩, z⟩, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
    · exact ⟨Unit, inferInstance, fun _ => none, fun _ => 1, by simp [LM.mul, LM.ent, hw]⟩
  · exact Fm.cof_off P hoff fun w hw => by simp [LM.mul, LM.ent, hw]

end
end

