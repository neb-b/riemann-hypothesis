module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfIsFubiniStudyOfRatFnFamily
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem semiPos_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → M.SemiPos D := by
  intro k _ X _ p D M J _ f w hM σ i c y hy ξ
  classical
  obtain ⟨ρ, -, hreg, hφ⟩ := hM
  have hx : under y ∈ M.B.U i := mem_ptsIn.1 hy.2
  obtain ⟨hr, j0, hu⟩ := hreg (under y) i hx
  choose U hU a ha using fun j => (hr j).exists_fnOf
  let G (j : J) (v : V D) : ℂ := (Real.exp (w j) : ℂ) * ev p σ (U j) (a j) (c.e.symm v)
  let S : Set (CxPts p σ) := ptsIn p σ (M.B.U i) ∩ ⋂ j, ptsIn p σ (U j)
  have hSo : IsOpen S := (isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun j => isOpen_ptsIn _)
  have hyS : y ∈ S := ⟨hy.2, Set.mem_iInter.2 fun j => mem_ptsIn.2 (hU j)⟩
  have hO := isOpen_over c.e hSo
  have hmO := mem_over c.e hy.1 hyS

  have hval (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ratVal (f j * (ρ i : X.functionField)) z = ev p σ (U j) (a j) z := by
    rw [← ha j]
    exact ratVal_fnOf (Set.mem_iInter.1 hz.2 j) _ _
  have hterm (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ‖ratVal (f j * (ρ i : X.functionField)) z‖ ^ 2 * Real.exp (2 * w j) =
        Complex.normSq ((Real.exp (w j) : ℂ) * ev p σ (U j) (a j) z) := by
    rw [hval z hz j, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      ← Real.exp_add]
    ring_nf
  have hG (j : J) : ContDiffAt ℂ 2 (G j) (c.e y) := by
    have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (U j))
    have hm := mem_over c.e hy.1 (mem_ptsIn.2 (hU j))
    exact contDiffAt_const.mul ((((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
      (c.holo (U j) (a j))).contDiffAt (ho.mem_nhds hm)).of_le (by norm_cast)))
  let e := Fintype.equivFin J
  let u (b : Fin (Fintype.card J)) (v : V D) : ℝ := Complex.normSq (G (e.symm b) v)
  have hsum (v : V D) : ∑ b, u b v = ∑ j, Complex.normSq (G j v) :=
    Equiv.sum_comp e.symm fun j => Complex.normSq (G j v)
  have hev : (fun v => (((M.φ σ).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((Real.log (∑ b, u b v) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hmO] with v hv
    rw [hφ σ _ i hv.2.1, hsum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => hterm _ hv.2 j
  have hpos : 0 < ∑ b, u b (c.e y) := by
    rw [hsum]
    simp only [G, c.e.left_inv hy.1]
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨j0, Finset.mem_univ _, ?_⟩
    rw [← hterm y hyS j0]
    exact mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2) (Real.exp_pos _)
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr hev]
  exact ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (fun b => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun b => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _)) hpos ξ

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtale
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.Points GlobalTheory.SemiPosBir

namespace GlobalTheory.SemiPosEtale

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

theorem exists_map_eq_of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range j) :
    ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := y.1) v _ hv
  have : JacobsonSpace ↥(pullback j y.1) := LocallyOfFiniteType.jacobsonSpace (pullback.snd j y.1)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback j y.1)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨⟨pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hj, Category.assoc, pullback.condition_assoc, pointOfClosedPoint_comp_assoc]
    exact y.2
  · change (pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1) ≫ j = y.1
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

def img (j : Z ⟶ X) [Etale j] : X.Opens := ⟨Set.range j, j.isOpenMap.isOpen_range⟩

theorem PosOn.of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ (img j)) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq_of_etale j hj (mem_ptsIn.1 hy.2.2)
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

end GlobalTheory.SemiPosEtale

namespace GlobalTheory.SemiPosEtale

theorem semiPos_of_pull_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  intro k _ X Y _ _ p q D hp _ π hπ V hV hE L hL σ i
  have := hp.isDomain
  have := hp.finite
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Etale (V.ι ≫ π) := hE
  have hj : (V.ι ≫ π) ≫ p = V.ι ≫ q := by rw [Category.assoc, hπ]
  have hU : ((img (V.ι ≫ π) : X.Opens) : Set X).Nonempty := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨_, ⟨v, hv⟩, rfl⟩
  change PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))
  refine PosOn.of_inter hσ (isOpen_ptsIn _) (L.cInf σ i) hU (PosOn.of_etale (V.ι ≫ π) hj ?_)
  let J : (L.B.pull π).ι := fun _ => i
  have h₀ : PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J)) := hL σ J
  have e₁ : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i) := Set.ext fun z => by
    rw [Set.mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
  have e₂ : ((L.φ σ).pull π hπ).φ J = fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  rw [e₁, e₂] at h₀
  have h₁ := h₀.pull V.ι (q := V.ι ≫ q) rfl
  have e₃ (w : CxPts (V.ι ≫ q) σ) : PtsOver.map π hπ _ (PtsOver.map V.ι rfl _ w) =
      PtsOver.map (V.ι ≫ π) hj _ w := Subtype.ext (Category.assoc _ _ _)
  simp only [e₃] at h₁
  exact h₁

end GlobalTheory.SemiPosEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistBoundOfShortExact
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem hdim_twist_bound_of_shortExact : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (L : LB X), L.IsLB → ∀ S : ShortComplex X.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₃ → ∀ (i : ℕ) (e : ℕ → ℕ), (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₁ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₃ (lbPow L m)) i ≤ C * e m) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist S.X₂ (lbPow L m)) i ≤ C * e m) := by
  intro k _ _ X _ hX L hL S hS h1 h3 i e hb1 hb3
  obtain ⟨C₁, hC₁⟩ := hb1
  obtain ⟨C₃, hC₃⟩ := hb3
  obtain ⟨hP, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k X)).1 hX
  have hf := algebraMap_eq_strHom k X
  have F₁ : FiniteCohTwists k S.X₁ := IsAmpleLB.finiteCohTwists hf S.X₁ hA
  have F₃ : FiniteCohTwists k S.X₃ := IsAmpleLB.finiteCohTwists hf S.X₃ hA
  refine ⟨C₁ + C₃, fun m => ?_⟩
  have hLm : (lbPow L m).IsLB := isLB_lbPow hL m
  have hT := Twist.shortExact_map hLm hS
  have fin₁ := ((F₁.twist hLm).finiteCoh).finite i
  have fin₃ := ((F₃.twist hLm).finiteCoh).finite i
  have key := hdim₂_le k hT i fin₁ fin₃
  calc hdim k (twist S.X₂ (lbPow L m)) i ≤ hdim k (twist S.X₁ (lbPow L m)) i + hdim k (twist S.X₃ (lbPow L m)) i := key
    _ ≤ C₁ * e m + C₃ * e m := Nat.add_le_add (hC₁ m) (hC₃ m)
    _ = (C₁ + C₃) * e m := (Nat.add_mul C₁ C₃ (e m)).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalities
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

private theorem finiteCohTwists_of_isProjOver' (k : Type) [Field k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) (F : X.Modules) [IsFiniteQC F] : FiniteCohTwists k F := by
  have hp' := hp
  unfold IsProjOver at hp'
  obtain ⟨N, i, hi, hcomp⟩ := hp'
  have hA : IsAmpleLB (ProjSpace.O1 k N) := isAmple_projective_O_one k N
  have hA' : IsAmpleLB ((ProjSpace.O1 k N).pull i) := IsAmpleLB.pull_of_isClosedImmersion hA i
  have hpr : IsProper (strHom k (X := X)) := by
    rw [← hcomp]
    have := isProper_str k N
    infer_instance
  exact IsAmpleLB.finiteCohTwists (f := strHom k X) (fun r => algebraMap_eq_strHom k X r) F hA'

theorem hdim_twist_cut_inequalities :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  intro k _ _ X _ hp F _ B M M' hB hM hM' s hmono hcls
  have hS : (cutComplex F hB s).ShortExact := shortExact_cutComplex F hB s
  have := Twist.preservesFiniteLimits_twistFunctor hM
  have := Twist.preservesFiniteColimits_twistFunctor hM
  have hT := hS.map_of_exact (twistFunctor M)
  have hF : FiniteCohTwists k F := finiteCohTwists_of_isProjOver' k X hp F
  have hC : FiniteCohTwists k (cut F hB s) := FiniteCohTwists.cut (hL := hB) (s := s) (h := hF)
  have hBi : (lbZPow B (-1)).IsLB := isLB_lbZPow hB (-1)
  have hcls' : cls M' hM' = cls (lbZPow B (-1)) hBi + cls M hM := by
    rw [cls_lbZPow hB (-1) hBi, hcls]
    abel
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hBi hM hM' hcls'
  have f1 : ∀ n, Module.Finite k (coh (twist (twist F (lbZPow B (-1))) M) n) :=
    fun n => ((hF.twist hBi) M hM).finite n
  have f2 : ∀ n, Module.Finite k (coh (twist F M) n) := fun n => (hF M hM).finite n
  have f3 : ∀ n, Module.Finite k (coh (twist (cut F hB s) M) n) := fun n => (hC M hM).finite n
  have he : ∀ n, hdim k (twist (twist F (lbZPow B (-1))) M) n = hdim k (twist F M') n :=
    fun n => hdim_congr (k := k) (n := n) e
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h : hdim k (twist F M) i ≤ hdim k (twist (twist F (lbZPow B (-1))) M) i +
        hdim k (twist (cut F hB s) M) i := hdim₂_le k hT i (f1 i) (f3 i)
    rw [he i] at h
    exact h
  · have h : hdim k (twist (twist F (lbZPow B (-1))) M) (i + 1) ≤ hdim k (twist (cut F hB s) M) i +
        hdim k (twist F M) (i + 1) := hdim₁_le k hT i (f3 i) (f2 (i + 1))
    rw [he (i + 1)] at h
    exact h
  · have h0 := hdim₁_zero_le k hT (f2 0)
    have h : hdim k (twist (twist F (lbZPow B (-1))) M) 0 ≤ hdim k (twist F M) 0 := h0
    rw [he 0] at h
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistPushforwardClosedImmersio
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory

theorem hdim_twist_pushforward_lbPow_of_isClosedImmersion : ∀ (k : Type) [Field k] (X Z : Scheme.{0}) [Algebra k Γ(X, ⊤)] (g : Z ⟶ X) [IsClosedImmersion g] (L : LB X), L.IsLB → ∀ (G : Z.Modules) (m i : ℕ), letI := algebraΓAlong k g; hdim k (twist ((Scheme.Modules.pushforward g).obj G) (lbPow L m)) i = hdim k (twist G (lbPow (L.pull g) m)) i := by
  intro k _ X Z _ g _ L hL G m i
  letI := algebraΓAlong k g
  have hf : ∀ r : k, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Z, ⊤) r := fun _ => rfl
  have hP : hdim k ((Scheme.Modules.pushforward g).obj (twist G ((lbPow L m).pull g))) i =
      hdim k (twist G ((lbPow L m).pull g)) i := by
    rw [hdim_def, hdim_def]
    exact (LinearEquiv.ofBijective _
      (cohPushMap_bijective_of_isClosedImmersion k g hf (twist G ((lbPow L m).pull g)) ⊤ i)).finrank_eq
  obtain ⟨e⟩ := nonempty_iso_of_lbIso (F := G) (isLB_lbPow (pull_isLB hL g) m)
    (pull_isLB (isLB_lbPow hL m) g) (lbIso_lbPow_pull hL g m)
  rw [← hdim_congr k i (projIso (lbPow L m) g G), hP, hdim_congr k i e.symm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Meet

theorem val_spMap_pt {F : Type} [Field F] (Y : Var F) {K : Type} [Field K] (σ : Y.Fn →+* K) (x : Y.Fn) :
    (ratOf Y).val (spMap σ ≫ (ratOf Y).pt) x = σ x := by
  have hx : x ∈ (ratOf Y).O ((ratOf Y).pt (IsLocalRing.closedPoint Y.Fn)) := by
    refine (congrArg (fun z => x ∈ (ratOf Y).O z) ((ratOf Y).pt_apply _)).mpr ?_
    rw [RatModel.O_genericPoint]; exact Algebra.mem_top
  have h := RatModel.val_spMap_comp (M := ratOf Y) σ (ratOf Y).pt specializes_rfl ⟨x, hx⟩
  rw [RatModel.valLoc_eq_val] at h
  exact h.trans (congrArg σ (RatModel.val_pt x))


open GlobalTheory.FlagBundle.ClosedPt in
theorem meet : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  intro F _ X Y ι _ m E E' φ f hf B hB A hA τ a b hab K _ V c t ht v₂ e hbear
  have hM := hf.sub _ B hB A hA
  obtain ⟨-, -, -, hsm⟩ := _root_.GlobalTheory.FlagPush.shear_props ι m τ a b hab V t
  obtain ⟨-, -, hs0, -⟩ := _root_.GlobalTheory.FlagPush.shear_props ι m τ a b hab (IsLocalRing.ResidueField V) 0
  have hpt : ∀ (R : Type) [CommRing R] (g : Y.Fn →+* R) (w : Sp R),
      (spMap g ≫ (ratOf Y).pt) w = genericPoint Y.X := fun R _ g w =>
    (Scheme.Hom.comp_apply _ _ _).trans ((ratOf Y).pt_apply _)
  have hf₂ : f (v₂ (IsLocalRing.closedPoint V)) = f (genericPoint Y.X) := by
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [e]
    exact (Scheme.Hom.comp_apply (spMap c ≫ (ratOf Y).pt) f _).trans (congrArg f (hpt _ c _))
  obtain ⟨A₂, hA₂⟩ := E'.nonempty (v₂ (IsLocalRing.closedPoint V))
  have hM₂ := hf.sub _ A₂ hA₂ A ((congrArg (fun z => A ∈ E.S z) hf₂).mpr hA)
  obtain ⟨A₂', hA₂', hpar⟩ := hbear
  have hA₂g : A₂ ∈ E'.S ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hsp₂ := gen_specializes (L := K) v₂ (IsLocalRing.closedPoint K)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring
      (A₂ * (A.map φ)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y) (spMap (algebraMap V K) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint K))
  have hv : ∀ x : ((ratOf Y).O ((spMap (algebraMap V K) ≫ v₂) (IsLocalRing.closedPoint K))).toSubring,
      (ratOf Y).val (spMap (algebraMap V K) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) *
        (A₂ * (A.map φ)⁻¹).map ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y).val (spMap (algebraMap V K) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one, ← mul_assoc] at hL
  rw [map_val (algebraMap V K) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL
  have hN : ∀ (S : Type) [CommRing S] (g : V →+* S),
      (shear τ a b t * (B * (A.map φ)⁻¹).map c).map g =
        shear τ a b (g t) * (B * (A.map φ)⁻¹).map (g.comp c) := fun S _ g => by
    rw [← hsm S g]
    funext σ
    exact Matrix.map_mul
  have hN1 := hN K (algebraMap V K)
  have hN2 := hN _ (IsLocalRing.residue V)
  rw [ht, hs0, one_mul] at hN2
  have hh : Par 0 ⊤ ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c)) :=
    hM.map _ fun _ _ => trivial
  have hk₂ := par_val (IsLocalRing.residue V) v₂ hM₂
  have hD := descend (L := K) (shear τ a b t * (B * (A.map φ)⁻¹).map c)
    (vals v₂ _ (fun τ a b => (hM₂ τ).1 a b)) (by rw [hN2]; exact hh.det_ne)
    (by rw [← map_val]; exact hk₂.det_ne) (by rw [hN1]; exact hL)
  rw [hN2, ← map_val] at hD
  have ec : spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt =
      spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hb₂ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap (IsLocalRing.residue V) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ E'.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  have hb₁ : Bears E' φ A ((B * (A.map φ)⁻¹).map ((IsLocalRing.residue V).comp c))
      (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) := by
    refine ⟨B, (congrArg (fun z => B ∈ E'.S z) (hpt _ _ _)).mpr hB, ?_⟩
    rw [show (ratOf Y).val (spMap ((IsLocalRing.residue V).comp c) ≫ (ratOf Y).pt) =
      ⇑((IsLocalRing.residue V).comp c) from funext (val_spMap_pt Y _), Mat.mul_inv hh.det_ne]
    exact Par.one
  have hAk : A ∈ E.S (((spMap (IsLocalRing.residue V) ≫ v₂) ≫ f)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) := by
    refine (congrArg (fun z => A ∈ E.S z) ?_).mpr hA
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg f (closedPt_comp v₂)).trans hf₂)
  obtain ⟨p, -, hp⟩ := hf.lifts _ _ A hAk _ hh
  refine (ec.trans (hp _ ⟨?_, hb₁⟩)).trans (hp _ ⟨rfl, hb₂⟩).symm
  rw [← ec]
  exact congrArg (spMap (IsLocalRing.residue V) ≫ ·) e.symm

end GlobalTheory.FlagPush.Meet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGeneration
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem shiftA_nu (P : Pair p) (u : ℝ) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u)) := by
  have e : (shiftA P u).nu a b σ y f = ‖ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y‖ *
      Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y +
        b * ((P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y + 2 * u)) / 2) := rfl
  rw [e, Pair.nu, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem shiftA_Bl (P : Pair p) (u : ℝ) (a b : ℤ) (R : ℝ) :
    (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u)) := by
  ext f
  simp only [Pair.Bl, Set.mem_setOf_eq, shiftA_H, shiftA_nu]
  refine and_congr_right fun _ => forall_congr' fun σ => forall_congr' fun y => ?_
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]

theorem genAt_shiftA (P : Pair p) (u : ℝ) (c : ℕ) (h : GenAt P c) : GenAt (shiftA P u) c := by
  obtain ⟨n, v, hv, hg⟩ := h
  refine ⟨n, v, fun i => by rw [shiftA_H]; exact hv i, fun σ y => ?_⟩
  obtain ⟨i, hi⟩ := hg σ y
  exact ⟨i, by rw [shiftA_nu]; exact mul_ne_zero hi (Real.exp_pos _).ne'⟩

theorem shiftA_props : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (u : ℝ), (∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), (shiftA P u).nu a b σ y f = P.nu a b σ y f * Real.exp (-(b * u))) ∧ (∀ (a b : ℤ) (R : ℝ), (shiftA P u).Bl a b R = P.Bl a b (R * Real.exp (b * u))) ∧ (∀ c : ℕ, GenAt P c → GenAt (shiftA P u) c) :=
  fun _ _ _ _ _ P u => ⟨shiftA_nu P u, shiftA_Bl P u, genAt_shiftA P u⟩

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexGermCongrStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeffComplex_germ_congr : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ} {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n}, ρ =ᶠ[𝓝 v] ρ' → G₀ =ᶠ[𝓝 v] G₀' → G₁ =ᶠ[𝓝 v] G₁' → corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  first | exact @GlobalTheory.GoodTop.corrC_germ_congr | exact GlobalTheory.GoodTop.corrC_germ_congr | (intros; apply GlobalTheory.GoodTop.corrC_germ_congr <;> assumption)
end

