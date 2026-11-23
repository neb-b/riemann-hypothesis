module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0300
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkOneVal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.UnipLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_one_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ = blk h w 1 (-X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simpa using GlobalTheory.LeviFubini.blk_one_zero h w

theorem blk_one_corner {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (i : Fin a) (j : Fin b) :
    (blk h w 1 X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j)) = X i j := by
  rw [CtLevel.blk_val]
  simp

theorem continuous_blk_one_val {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (blk h w 1 X).val := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  simp only [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · simpa using continuous_const
  · simpa using continuous_id.matrix_elem i j
  · simpa using continuous_const
  · simpa using continuous_const

theorem continuous_blk_one {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => blk h w 1 X := by
  refine Units.continuous_iff.2 ⟨continuous_blk_one_val h w, ?_⟩
  have e : (fun X : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (((blk h w 1 X)⁻¹ : GLw n w)).val) =
      (fun X => (blk h w 1 X).val) ∘ fun X => -X := by
    funext X
    simp [blk_one_inv]
  exact e ▸ (continuous_blk_one_val h w).comp continuous_neg

def intSub (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) where
  carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
  one_mem' := fun i j => by simp
  mul_mem' := fun {X Y} hX hY i j => by
    simpa using (Valued.v.map_add _ _).trans (max_le (hX i j) (hY i j))
  inv_mem' := fun {X} hX i j => by simpa using hX i j

theorem intMat_eq_intSub (a b : ℕ) (w : Pl E) : intMat a b w = intSub a b w := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun X hX => hX) fun X hX => Subgroup.subset_closure hX

theorem isCompact_intSub (a b : ℕ) (w : Pl E) :
    IsCompact (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) := by
  have e : (intSub a b w : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) =
      Multiplicative.toAdd ⁻¹' (Set.pi Set.univ fun _ : Fin a => Set.pi Set.univ
        fun _ : Fin b => ((w.adicCompletionIntegers E : Set (w.adicCompletion E)))) := by
    ext X
    exact ⟨fun hX i _ j _ => hX i j, fun hX i j => hX i trivial j trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers w

theorem unip_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ≤ intMat a b w ∧ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).relIndex (intMat a b w) ≠ 0 := by
  intro E _ _ _ a b n h w K' hK' hKK
  have hmem : ∀ X, X ∈ (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) ↔
      blk h w 1 (Multiplicative.toAdd X) ∈ K' := fun X => Iff.rfl
  refine ⟨fun X hX => ?_, ?_⟩
  · rw [intMat_eq_intSub]
    intro i j
    obtain ⟨u, hu⟩ := hKK ((hmem X).1 hX)
    have h1 : Valued.v ((blk h w 1 (Multiplicative.toAdd X)).val (CtLevel.blkEq h (Sum.inl i))
        (CtLevel.blkEq h (Sum.inr j))) ≤ 1 := by
      rw [← hu]
      exact (u.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))).2
    rwa [blk_one_corner] at h1
  · have hopen : IsOpen (((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) :
        Subgroup _) : Set (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))) :=
      hK'.preimage ((continuous_blk_one h w).comp continuous_toAdd)
    rw [intMat_eq_intSub]
    haveI : CompactSpace (intSub a b w) := isCompact_iff_compactSpace.1 (isCompact_intSub a b w)
    haveI : Finite ((intSub a b w) ⧸ ((K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w)).subgroupOf (intSub a b w)) :=
      Subgroup.quotient_finite_of_isOpen _ (hopen.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.UnipLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.CompIsoProof

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) (a : ℕ) :
    Continuous (GeneralLinearGroup.map f : GL (Fin a) R →* GL (Fin a) S) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) (a : ℕ) :
    Continuous (cornerGL a s) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

variable {E : Type} [Field E] {a : ℕ}

def glOf (y : InfinitePlace E → GL (Fin a) ℂ) : GL (Fin a) (Cinf E) where
  val := Matrix.of fun i j v => (y v).val i j
  inv := Matrix.of fun i j v => (y v).inv i j
  val_inv := by
    ext i j v
    have h := congrFun (congrFun (y v).val_inv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h
  inv_val := by
    ext i j v
    have h := congrFun (congrFun (y v).inv_val i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h

theorem map_eval_glOf (y : InfinitePlace E → GL (Fin a) ℂ) (v : InfinitePlace E) :
    GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (glOf y) = y v := by
  ext i j
  rfl

theorem continuous_glOf : Continuous (glOf : (InfinitePlace E → GL (Fin a) ℂ) → GL (Fin a) (Cinf E)) := by
  have h2 : Continuous fun x : GL (Fin a) ℂ => ((x⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) :=
    (Units.continuous_iff.1 (continuous_id (X := GL (Fin a) ℂ))).2
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => continuous_pi fun v => ?_,
    continuous_matrix fun i j => continuous_pi fun v => ?_⟩
  · exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply v)
  · exact (h2.matrix_elem i j).comp (continuous_apply v)

variable [NumberField E]

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

variable [_root_.NumberField.IsTotallyComplex E]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coordinate (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (continuous_apply v).comp continuous_pInf

theorem map_cV (v : InfinitePlace E) (g : GA E a) :
    GeneralLinearGroup.map (cV v) g =
      GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (GeneralLinearGroup.map (pInf E) g) := by
  ext i j
  rfl

def parts (g : GA E a) : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E) :=
  (fun v => GeneralLinearGroup.map (cV v) g, GeneralLinearGroup.map (pFin E) g)

def glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : GA E a :=
  infGL E a (glOf p.1) * finGL E a p.2

theorem glue_parts (g : GA E a) : glue (parts g) = g := by
  have h : glOf (fun v => GeneralLinearGroup.map (cV v) g) = GeneralLinearGroup.map (pInf E) g := by
    ext i j v
    rfl
  rw [glue, parts]
  simp only [h]
  exact infGL_mul_finGL g

theorem parts_glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : parts (glue p) = p := by
  refine Prod.ext (funext fun v => ?_) ?_
  · change GeneralLinearGroup.map (cV v) (glue p) = p.1 v
    rw [map_cV, glue, map_mul, pInf_infGL, pInf_finGL, mul_one, map_eval_glOf]
  · change GeneralLinearGroup.map (pFin E) (glue p) = p.2
    rw [glue, map_mul, pFin_infGL, pFin_finGL, one_mul]

theorem continuous_parts : Continuous (parts : GA E a → _) :=
  (continuous_pi fun v => continuous_glMap (cV v) (continuous_coordinate v) a).prodMk
    (continuous_glMap (pFin E) continuous_snd a)

theorem continuous_glue : Continuous (glue : _ → GA E a) :=
  ((continuous_cornerGL (sInf E) continuous_sInf a).comp (continuous_glOf.comp continuous_fst)).mul
    ((continuous_cornerGL (sFin E) continuous_sFin a).comp continuous_snd)

theorem compIso : CompIso := by
  intro E _ _ _ a b
  refine ⟨{ toFun := comps
            invFun := fun p => (glue (fun v => (p.1 v).1, p.2.1), glue (fun v => (p.1 v).2, p.2.2))
            left_inv := fun x => Prod.ext (glue_parts x.1) (glue_parts x.2)
            right_inv := fun p => ?_
            map_mul' := fun x y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ => rfl⟩
  · have h1 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))) v
    have h2 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))) v
    have h3 := congrArg Prod.snd (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))
    have h4 := congrArg Prod.snd (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))
    exact Prod.ext (funext fun v => Prod.ext (h1 v) (h2 v)) (Prod.ext h3 h4)
  · refine Prod.ext (funext fun v => Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> exact map_mul _ _ _
  · have p1 : Continuous fun x : GA E a × GA E b => parts x.1 := continuous_parts.comp continuous_fst
    have p2 : Continuous fun x : GA E a × GA E b => parts x.2 := continuous_parts.comp continuous_snd
    exact (continuous_pi fun v => ((continuous_apply v).comp p1.fst).prodMk ((continuous_apply v).comp p2.fst)).prodMk
      (p1.snd.prodMk p2.snd)
  · have q1 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).1, p.2.1) :
        (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).fst).prodMk continuous_snd.fst
    have q2 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).2, p.2.2) :
        (InfinitePlace E → GL (Fin b) ℂ) × GL (Fin b) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).snd).prodMk continuous_snd.snd
    exact (continuous_glue.comp q1).prodMk (continuous_glue.comp q2)

end GlobalTheory.CompanionTheory.CompIsoProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMirabolicEmbedding
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

theorem continuous_glEmbMat_comp {k X : Type} [Field k] [TopologicalSpace k] [TopologicalSpace X] (m : ℕ)
    {f : X → Matrix (Fin m) (Fin m) k} (hf : Continuous f) :
    Continuous fun x => glEmbMat k m (f x) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_last, Fin.lastCases_castSucc] <;>
    first
    | exact continuous_const
    | exact hf.matrix_elem _ _

theorem continuous_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  intro k _ _ _ _ n
  have hemb : Continuous (GlobalTheory.BZMir.glEmb k (n + 1)) :=
    Continuous.units_map _ (GlobalTheory.CompanionTheory.LeibPhi.continuous_glEmbMat_comp (n + 1) continuous_id)
  exact continuous_induced_rng.2 (hemb.comp continuous_subtype_val)

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.AdelCont

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem orbFn_mul_right (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (U : Subgroup (Gf E a b))
    (hU : ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u⁻¹ * y * thP E a b u) = finFn S φ₁ φ₂ y)
    (x u : Gf E a b) (hu : u ∈ U) : orbFn S φ₁ φ₂ δ₁ δ₂ (x * u) = orbFn S φ₁ φ₂ δ₁ δ₂ x := by
  unfold orbFn
  rw [← hU u hu (x⁻¹ * (ratF E a δ₁, ratF E b δ₂) * thP E a b x), map_mul]
  congr 1
  group

theorem continuous_of_right_invariant {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] (f : G → X) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) : Continuous f := by
  have : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hmem : (x⁻¹ * ·) ⁻¹' (U : Set G) ∈ nhds x := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      apply hUo.mem_nhds
      simp [U.one_mem]
    filter_upwards [hmem] with y hy
    have := hf x (x⁻¹ * y) hy
    simpa using this
  exact this.continuous

theorem continuous_twConj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Monoid.End G) (hθ : Continuous θ) (δ : G) : Continuous fun g : G => twConj θ g δ := by
  unfold twConj
  exact (continuous_inv.mul continuous_const).mul hθ

theorem adelContOf : AdelContOf := by
  intro hEq hFin hComp hTopo E _ _ _ hUnr a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ hψ t₁ t₂ d₁ d₂
  obtain ⟨e, he⟩ := hComp E a b
  have hc : Continuous (comps : GA E a × GA E b → Gi E a b × Gf E a b) := by
    have : (comps : GA E a × GA E b → Gi E a b × Gf E a b) = e := funext fun x => (he x).symm
    rw [this]; exact e.continuous
  have hθa : Continuous (thetaR (starRingEnd ℂ) a) := (hTopo E a).2.2.2.2.2
  have hθb : Continuous (thetaR (starRingEnd ℂ) b) := (hTopo E b).2.2.2.2.2
  obtain ⟨U, hUo, hU⟩ := hFin E hUnr a b S φ₁ φ₂ t₁ t₂
  have hfin : Continuous (orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) :=
    continuous_of_right_invariant _ U hUo fun x u hu => orbFn_mul_right S φ₁ φ₂ _ _ U hU x u hu
  have hrw : (fun x : GA E a × GA E b =>
      adel S u₁ u₂ ψ φ₁ φ₂ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))) =
      fun x => (∏ v, ψ v (twConj (thetaR (starRingEnd ℂ) a) ((comps x).1 v).1 (GeneralLinearGroup.map v.embedding d₁),
        twConj (thetaR (starRingEnd ℂ) b) ((comps x).1 v).2 (GeneralLinearGroup.map v.embedding d₂))) *
      orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (comps x).2 :=
    funext fun x => hEq E a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [hrw]
  refine Continuous.mul (continuous_finsetProd _ fun v _ => (hψ v).comp ?_) (hfin.comp (continuous_snd.comp hc))
  have hv : Continuous fun x : GA E a × GA E b => (comps x).1 v :=
    (continuous_apply v).comp (continuous_fst.comp hc)
  exact ((continuous_twConj _ hθa _).comp (continuous_fst.comp hv)).prodMk
    ((continuous_twConj _ hθb _).comp (continuous_snd.comp hv))

end GlobalTheory.CompanionTheory.AdelCont

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotNorm

theorem count_isInvInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSingletonClass G] (H : Subgroup G) : (Measure.count : Measure H).IsInvInvariant := by
  have hinv : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  ext s hs
  rw [Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]
  exact congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)

theorem qIndep : PositivityTheory.Rg.BcB.G8.QIndep := by
  intro G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ
  have := count_isInvInvariant H
  exact quotIntegral_eq (μG := μ) hF hFH hρ

end GlobalTheory.CompanionTheory.QuotNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_support_realised_by_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | exact GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | (intros; apply GlobalTheory.CompanionTheory.GenSupp.hasSupport_std <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGaloisStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_local_galois : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  first | exact @GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | exact GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one | (intros; apply GlobalTheory.CompanionTheory.Dict.isFrob_of_unramifiedDegree_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLowExponentCasimirStatement
section
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_low_exponent_casimir : ∀ {n : ℕ} (m : Fin n × Fin n →₀ ℕ), LowExp m → (∀ i j : Fin n, (j : ℕ) = i + 1 → ∃ p : ℕ, 1 + wt m i - wt m j = (p : ℤ)) → casC (fun k => rhoVec n k + (wt m k : ℂ)) = casC (rhoVec n) → m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | exact GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq | (intros; apply GlobalTheory.CompanionTheory.PresRho.NormIneq.eq_zero_of_casC_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinMapEq
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace GlobalTheory.CompanionTheory.RgCz

theorem exists_fin_map_eq {a : ℕ} (m : Multiset ℂ) (hm : Multiset.card m = a) :
    ∃ χ : Fin a → ℂ, Multiset.map χ Finset.univ.val = m := by
  subst hm
  induction m using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp

theorem charInt_at {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (hr : (CG.mk π).IsRegAlg) (τ : E →+* ℂ) :
    ∃ l : Fin a → ℤ, Function.Injective l ∧
      PositivityTheory.Rg.Cz.HasChar (cx τ (lieOp π)) fun k => (l k : ℂ) := by
  obtain ⟨hnd, hint⟩ := hr τ
  obtain ⟨χ, hχ⟩ := exists_fin_map_eq ((CG.mk π).infChar τ) (CG.card_infChar (CG.mk π) τ)
  have hinf : π.HasInfChar τ (Multiset.map χ Finset.univ.val) := by
    rw [hχ]
    exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ
  have hcap := (GlobalTheory.capelli_cuspSub E a π τ χ hinf).2
  rw [← hχ] at hnd hint
  have hχinj : Function.Injective χ := by
    have h := Multiset.inj_on_of_nodup_map hnd
    intro s t hst
    exact h s (by simp) t (by simp) hst
  have hn : ∀ s, ∃ n : ℤ, χ s = (n : ℂ) + ((a : ℂ) - 1) / 2 := fun s =>
    hint _ (Multiset.mem_map_of_mem χ (by simp))
  choose l hl using hn
  refine ⟨l, fun s t hst => hχinj (by rw [hl, hl, hst]), fun u => ?_⟩
  have h := hcap (u - ((a : ℂ) - 1) / 2)
  rw [sub_add_cancel] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hl k]
  ring

theorem charInt : PositivityTheory.Rg.Cz.CharInt := by
  intro E _ _ _ a π hr
  choose l hl using charInt_at π hr
  exact ⟨l, fun τ => (hl τ).1, fun τ => (hl τ).2⟩

end GlobalTheory.CompanionTheory.RgCz

end
end

