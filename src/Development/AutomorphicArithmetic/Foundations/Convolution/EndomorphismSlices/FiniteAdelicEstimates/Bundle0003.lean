module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ActHcsSlice
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.FinLevelHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ConvMul
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH finH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem convMul : ConvMul := by
  intro E _ _ _ B f hf
  haveI := B.ha
  haveI := B.hb
  haveI := B.hν
  haveI : BorelSpace (G B.a) := ⟨rfl⟩
  haveI : BorelSpace (G B.b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  refine ⟨fun t t' ht ht' => ?_, fun ψ ψ' hψ hψ' => ?_⟩
  · have hT := PositivityTheory.Rg.BcB.F.Op.test B tensTest t ht
    have hT' := PositivityTheory.Rg.BcB.F.Op.test B tensTest t' ht'
    have hm := (tensMul E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t'.ka t.kb t'.kb t.va t'.va t.vb t'.vb
      t.T t'.T t.ψ t'.ψ B.compat ht.ka ht.kb ht'.ka ht'.kb ht.ψ ht'.ψ).2
    have e : (t.mul t').Φ = mulM B.D.μ t.Φ t'.Φ := hm.symm
    rw [e]
    exact PositivityTheory.Rg.BcB.F.Rd.B.conv_mulM B.D t.Φ t'.Φ hT hT' f hf
  · have hcf : Continuous fun h : Hf E B.a B.b => finH h :=
      ((continuous_finGL' B.a).comp continuous_fst).prodMk ((continuous_finGL' B.b).comp continuous_snd)
    have hF : ∀ i x, Continuous fun h => f i (x * finH h) := fun i x =>
      (hf i).comp (continuous_const.mul hcf)
    have hI : ∀ (φ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)), IsFinM φ → ∀ y z i x,
        Integrable (fun h => φ y z h * f i (x * finH h)) B.ν := fun φ hφ y z i x =>
      ((hφ y z).1.mul (hF i x)).integrable_of_hasCompactSupport (hφ y z).2.mul_right
    refine ⟨PositivityTheory.Rg.BcB.F.R3.convF_mulF_eq_convF_convF B.ν ψ ψ' hψ hψ' f hF, ?_, fun c => ⟨?_, ?_⟩⟩
    · funext i x
      simp only [convF, Pi.add_apply, Matrix.add_apply, add_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact integral_add (hI ψ hψ _ _ _ _) (hI ψ' hψ' _ _ _ _)
    · funext i x
      simp only [convF, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact integral_const_mul _ _
    · funext i x
      simp only [convF, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      show ψ i.2 z h * (c * f (i.1, z) (x * finH h)) = c * (ψ i.2 z h * f (i.1, z) (x * finH h))
      ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

private def lmOf (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : LM (fun _ : Pl E => Unit) a b :=
  ⟨fun w _ _ => φ₁ w, φ₁, φ₂⟩

private def eU : Unit ≃ ∀ _ : (∅ : Finset (Pl E)), Unit := Equiv.ofUnique _ _

private theorem ent_empty (L : LM (fun _ : Pl E => Unit) a b) (x y : ∀ _ : (∅ : Finset (Pl E)), Unit) :
    L.ent ∅ x y = L.s := by
  funext w; simp [LM.ent]

private theorem ff_fm {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b}
    (A : Ar l₁ l₂ D) (S : Set (Pl E)) (L : LM (fun _ : Pl E => Unit) a b) :
    A.ff S L.s L.t = fm S ∅ A.blk eU L := by
  funext x y h
  simp only [Ar.ff, fm, ent_empty]

private theorem ok_lm {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) : (lmOf φ₁ φ₂).Ok ∅ :=
  ⟨fun x y => by rw [ent_empty]; exact h₁, h₂⟩

end

theorem ffAlg : FfAlg := by
  intro E _ _ _ a b l₁ l₂ D A S hS
  refine ⟨(BlockFiniteConvolution.finConv' E A.blk S hS).1, fun φ₁ φ₂ h₁ h₂ => ?_⟩
  have alg := fun (φ₁' φ₂' : ∀ w : Pl E, LF a b w) (h₁' : IsTestP φ₁') (h₂' : IsTestP φ₂') =>
    BlockFiniteConvolution.fmAlg' E (fun _ => Unit) S ∅ A.blk eU hS (by simp) (lmOf φ₁ φ₂) (lmOf φ₁' φ₂') (ok_lm h₁ h₂) (ok_lm h₁' h₂')
  obtain ⟨hf, -, -, -, hadj⟩ := alg φ₁ φ₂ h₁ h₂
  refine ⟨?_, ?_, Fm.isTestFunction_star h₁, Fm.isTestFunction_star h₂, fun φ₁' φ₂' h₁' h₂' => ?_⟩
  · have := ff_fm A S (lmOf φ₁ φ₂)
    exact this ▸ hf
  · exact (congrArg adjF (ff_fm A S (lmOf φ₁ φ₂))).trans (hadj.trans (ff_fm A S (lmOf φ₁ φ₂).adj).symm)
  · obtain ⟨-, -, hmul, -, -⟩ := alg φ₁' φ₂' h₁' h₂'
    have e₁ := ff_fm A S (lmOf φ₁ φ₂)
    have e₂ := ff_fm A S (lmOf φ₁' φ₂')
    have e₃ := ff_fm A S ((lmOf φ₁ φ₂).mul (lmOf φ₁' φ₂'))
    exact (congrArg₂ (mulF A.ν) e₁ e₂).trans (hmul.trans e₃.symm)

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KgFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem mem_Kg {S : Set (Pl E)} {L : ∀ w : Pl E, Subgroup (GLw n w)} {g : GL (Fin n) (Af E)} :
    g ∈ Kg S L ↔ ∀ w ∈ S, Slots.loc n w g ∈ L w ∧ (IsSplitAt w → Slots.loc n w (thF E n g) ∈ L w) := by
  simp only [Kg, Subgroup.mem_iInf, Subgroup.mem_inf]
  refine forall_congr' fun w => forall_congr' fun _ => and_congr_right fun _ => ?_
  by_cases h : IsSplitAt w
  · simp [h, Subgroup.mem_comap]
  · simp [h]

private theorem continuous_thF' : Continuous (thF E n) :=
  GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)

private theorem mem_Kf {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ w, Slots.loc n w g ∈ KGL w (n := n) := by
  simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]

private theorem thF_mem_Kf {g : GL (Fin n) (Af E)} (hg : g ∈ Kf E n) : thF E n g ∈ Kf E n :=
  mem_Kf.2 fun u => Slots.loc_thF_mem u (mem_Kf.1 hg _)

private theorem isOpen_cut (Z : Finset (Pl E)) (L : ∀ w : Pl E, Subgroup (GLw n w))
    (hL : ∀ w, IsOpen (L w : Set (GLw n w))) :
    IsOpen ((Kf E n ⊓ ⨅ w ∈ Z, ((L w).comap (Slots.loc n w) ⊓
      (L w).comap ((Slots.loc n w).comp (thF E n))) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have e : ((Kf E n ⊓ ⨅ w ∈ Z, ((L w).comap (Slots.loc n w) ⊓
      (L w).comap ((Slots.loc n w).comp (thF E n))) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) =
      (Kf E n : Set _) ∩ ⋂ w ∈ Z, (Slots.loc n w ⁻¹' (L w : Set _) ∩ (Slots.loc n w ∘ thF E n) ⁻¹' (L w : Set _)) := by
    ext g
    simp [Subgroup.mem_iInf, Subgroup.mem_inf, Subgroup.mem_comap]
  rw [e]
  refine (PositivityTheory.Rg.BcB.G8.Fin.kfOC_holds E n).1.inter (isOpen_biInter_finset fun w _ => ?_)
  exact ((hL w).preimage (Slots.continuous_loc n w)).inter
    ((hL w).preimage ((Slots.continuous_loc n w).comp continuous_thF'))

theorem kgFacts : KgFacts := by
  intro E _ _ _ n S Z L hS hZ hL hoff
  obtain ⟨-, hcp, -, hsec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  refine ⟨?_, ?_, ?_⟩
  · refine Subgroup.isOpen_mono ?_ (isOpen_cut Z L fun w => (hL w).1)
    intro g hg
    obtain ⟨hgK, hgZ⟩ := Subgroup.mem_inf.1 hg
    refine mem_Kg.2 fun w hw => ?_
    by_cases hwZ : w ∈ Z
    · have h := Subgroup.mem_inf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hgZ w) hwZ)
      exact ⟨h.1, fun _ => h.2⟩
    · rw [hoff w hwZ]
      exact ⟨mem_Kf.1 hgK w, fun _ => mem_Kf.1 (thF_mem_Kf hgK) w⟩
  · intro g hg
    have hg' := mem_Kg.1 hg
    refine mem_Kf.2 fun u => ?_
    rcases (hsec S hS u).1 with hu | hu
    · exact (hL u).2 (hg' u hu).1
    · by_cases hs : IsSplitAt (cPl u)
      · have h1 : Slots.loc n (cPl u) (thF E n g) ∈ KGL (cPl u) (n := n) := (hL _).2 ((hg' _ hu).2 hs)
        have h2 : Slots.loc n u (thF E n (thF E n g)) ∈ KGL u (n := n) := Slots.loc_thF_mem u h1
        rwa [GlobalTheory.EulerTw.Comm.thF_thF] at h2
      · have e1 : cPl (cPl u) = cPl u := by
          by_contra h
          exact hs ((hcp (cPl u)).2.2 h)
        have e : cPl u = u := e1.symm.trans (hcp u).1
        rw [e] at hu
        exact (hL u).2 (hg' u hu).1
  · intro w hw k hk
    refine mem_Kg.2 fun u hu => ⟨?_, fun _ => ?_⟩
    · by_cases e : u = w
      · subst e
        rw [hoff u hw.1]
        have h : Slots.loc n u (locGL E n u k) = k := pLoc_locGL _ _
        rwa [h]
      · have h : Slots.loc n u (locGL E n w k) = 1 := pLoc_locGL_of_ne e k
        rw [h]
        exact one_mem _
    · by_cases e : cPl u = w
      · have hu' : u = cPl w := by rw [← e, (hcp u).1]
        have huZ : u ∉ Z := hu' ▸ hw.2
        rw [hoff u huZ]
        refine Slots.loc_thF_mem u ?_
        subst e
        have h : Slots.loc n (cPl u) (locGL E n (cPl u) k) = k := pLoc_locGL _ _
        show Slots.loc n (cPl u) (locGL E n (cPl u) k) ∈ KGL (cPl u) (n := n)
        rwa [h]
      · have h : Slots.loc n (Slots.cP u) (locGL E n w k) = Slots.loc n (Slots.cP u) 1 := by
          rw [map_one]
          exact pLoc_locGL_of_ne e k
        rw [Slots.loc_thF_congr u h, map_one, map_one]
        exact one_mem _

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem locAlg : LocAlg := by
  intro E _ _ _ a b Z L w
  have hK2 : K2 a b w = (KGL w (n := a)).prod (KGL w (n := b)) := rfl
  have hop : IsOpen (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (L.open₁ w).prod (L.open₂ w)
  have hle : (L.L₁ w).prod (L.L₂ w) ≤ K2 a b w := Subgroup.prod_mono (L.le₁ w) (L.le₂ w)
  have hKop : IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
    rw [hK2, Subgroup.coe_prod]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  have hln : L.ln w = idem ((L.L₁ w).prod (L.L₂ w)) := rfl
  have hKi : idem (K2 a b w) = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
    funext y
    simp only [idem, Subgroup.relIndex_self, Nat.cast_one]
    rfl
  obtain ⟨h1, h2, h3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hop hle
  obtain ⟨-, -, k3⟩ := PositivityTheory.Rg.BcB.F.idemAlg E a b w _ hKop le_rfl
  refine ⟨hln ▸ h1, hln ▸ h2, fun hw => ?_, fun f hf => ?_, fun f hf => ?_⟩
  · obtain ⟨e₁, e₂⟩ := L.off w hw
    rw [hln, e₁, e₂, ← hK2, hKi]
  · rw [hln]
    exact ⟨(h3 f hf).2.1, (h3 f hf).1⟩
  · rw [← hKi]
    exact ⟨(k3 f hf).2.1, (k3 f hf).1, (k3 f hf).2.2⟩

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem herm_chi {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (l : InfinitePlace E → DomWeight n) (v : InfinitePlace E) : IsHerm (chi l v) := by
  refine ⟨Equiv.refl _, fun i => ?_⟩
  simp [chi, infOf, Complex.conj_ofReal, map_sub, map_add (f := _), map_div₀, map_natCast, map_intCast, map_one, map_ofNat]

private theorem mult_of_ker {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n}
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (M.V →L[ℂ] M.V)}
    (hg : IsBump g T) (hk : IsKer μ M w g k) :
    IsMult μ M k (fun χ => zVal w χ * coshT g (cas χ)) T := by
  refine ⟨1, fun _ => 1, fun _ => w, fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, ?_, ?_⟩
  · intro y _
    simp
  · intro χ
    simp

theorem ptOk : PtOk := by
  intro E _ _ _ a b l₁ l₂ D A
  have hsize : ∀ ψ : Matrix Unit Unit (Hf E a b → ℂ), IsFinM ψ →
      0 ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ ∧ ∀ x y g, ψ x y g ≠ 0 →
        logSize (finGL E a g.1) ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ ∧ logSize (finGL E b g.2) ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ := by
    intro ψ hψ
    have h : ∃ r, 0 ≤ r ∧ ∀ x y g, ψ x y g ≠ 0 → logSize (finGL E a g.1) ≤ r ∧ logSize (finGL E b g.2) ≤ r :=
      (PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.rtAlg' E A.blk 1 1).2.2 ψ hψ
    rw [PositivityTheory.Rg.BcB.F.sizeOf, dite_eq_left h]
    exact h.choose_spec
  refine ⟨herm_chi l₁, herm_chi l₂, ?_, ?_, ?_⟩
  · intro wa wb ψ hψ
    exact
      { T := A.T_nonneg
        r := (hsize ψ hψ).1
        ka := fun v => mult_of_ker A.isBump (A.kera (wa v) v)
        kb := fun v => mult_of_ker A.isBump (A.kerb (wb v) v)
        ψ := hψ
        size := (hsize ψ hψ).2 }
  · intro ψ
    have := A.one
    simpa [Ar.ptB, Ar.pt, PT.val, valA, Ar.valW, zVal] using this
  · intro wa wb ψ χa χb
    simp only [Ar.ptB, Ar.pt, PT.val, valA, Ar.valW, Finset.prod_mul_distrib]
    simp only [zVal, List.map_nil, List.prod_nil, one_mul, Finset.prod_const_one]
    ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem repAlg : RepAlg := by
  intro E _ _ _ B χa χb
  have hop := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C ψ R h
    exact PositivityTheory.Rg.BcB.F.blkSum E B.a B.b B.D B.I C.J C.s C.c (fun j => (C.t j).Φ) (fun j => (C.t j).op)
      fun j hj => ⟨(hop _ _ (h j hj).1 (h j hj).1).1, (hop _ _ (h j hj).1 (h j hj).1).2.1⟩
  · intro t ht
    refine ⟨⟨Unit, {()}, fun _ => 1, fun _ => t⟩, ?_, ?_, ?_⟩
    · intro j _
      exact ⟨ht, rfl, le_max_left _ _, le_max_right _ _⟩
    · simp [Cmb.val]
    · simp [Cmb.op]
  · rintro ψ v R R' U h ⟨C, hC, hv, hU⟩
    exact ⟨C, fun j hj => ⟨(hC j hj).1, (hC j hj).2.1, (hC j hj).2.2.1.trans h, (hC j hj).2.2.2.trans h⟩, hv, hU⟩
  · rintro ψ ψ' v v' R R' U U' ⟨C, hC, rfl, rfl⟩ ⟨C', hC', rfl, rfl⟩
    refine ⟨⟨C.J × C'.J, C.s ×ˢ C'.s, fun p => C.c p.1 * C'.c p.2, fun p => (C.t p.1).mul (C'.t p.2)⟩, ?_, ?_, ?_⟩
    · rintro ⟨j, j'⟩ hj
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hj
      obtain ⟨o, e, hT, hr⟩ := hC j h1
      obtain ⟨o', e', hT', hr'⟩ := hC' j' h2
      refine ⟨(hop _ _ o o').2.2.1, ?_, ?_, ?_⟩
      · change mulF B.ν (C.t j).ψ (C'.t j').ψ = _
        rw [e, e']
      · change (C.t j).T + (C'.t j').T ≤ _
        linarith [B.c_nonneg]
      · change (C.t j).r + (C'.t j').r + B.c ≤ _
        linarith
    · simp only [Cmb.val]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
      rw [(hop _ _ (hC j hj).1 (hC' j' hj').1).2.2.2.2.2.2.1 χa χb]
      ring
    · simp only [Cmb.op]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
      rw [(hop _ _ (hC j hj).1 (hC' j' hj').1).2.2.2.1, smul_mul_smul_comm]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SphComm2
section
theorem UpperTheory.Zero.ConvolutionTheory.EB.sphComm2 :
    UpperTheory.Zero.ConvolutionTheory.EB.SphComm2 := by
  intro E _ _ _ a b w f f' hf hf'
  exact PositivityTheory.Rg.BcB.F.sphComm E a b w f f' hf hf'
end

