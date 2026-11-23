module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.Published

def NefProductNonneg : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (d : ℕ),
    IsProjOver (strHom k (X := X)) → topologicalKrullDim X = d →
    ∀ N : Fin d → LB X, (∀ i, IsNef k (N i)) → 0 ≤ interNum k (structureModule X) N

def NefBigIff : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)]
    (D : ℕ), IsProjOver (strHom k (X := X)) → topologicalKrullDim X = D →
    ∀ N : LB X, IsNef k N → (IsBig k N ↔ 0 < topSelfIntersection k N D)

def NefRiemannRoch : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (D : ℕ),
    IsProjOver (strHom k (X := X)) → topologicalKrullDim X = D →
    ∀ L : LB X, IsNef k L →
      (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
        =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)

def NefNumerics : Prop := NefProductNonneg ∧ NefBigIff ∧ NefRiemannRoch

theorem dim_affineOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) :=
  (topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
    hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U)))

theorem dim_le_of_isIntegralHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsIntegralHom π] :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  refine ⟨(π ⁻¹ᵁ U : Y.Opens), (π ⁻¹ᵁ U).isOpen, hy, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le X (U : Set X))
  rw [dim_affineOpen (hU.preimage π), dim_affineOpen hU]
  letI := (π.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := ⟨IsIntegralHom.isIntegral_app π U hU⟩
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, π ⁻¹ᵁ U)))
    fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h

theorem exists_algClosed_baseChange {k : Type} [Field k] {X : Scheme.{0}} [a : Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) :
    ∃ (X' : Scheme.{0}) (_ : Algebra (AlgebraicClosure k) Γ(X', ⊤)) (π : X' ⟶ X),
      IsProjOver (strHom (AlgebraicClosure k) (X := X')) ∧
      topologicalKrullDim X' = topologicalKrullDim X ∧
      (∀ L : LB X, IsNef k L → IsNef (AlgebraicClosure k) (L.pull π)) ∧
      (∀ L : LB X, L.IsLB → lbH0 (AlgebraicClosure k) (L.pull π) = lbH0 k L) ∧
      ∀ (d : ℕ) (L : Fin d → LB X), (∀ i, (L i).IsLB) →
        interNum (AlgebraicClosure k) (structureModule X') (fun i => (L i).pull π) =
          interNum k (structureModule X) L := by
  obtain ⟨f, rfl⟩ : ∃ f : X ⟶ Sp k, a = algebraΓOfHom f :=
    ⟨strHom k X, Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)⟩
  letI := algebraΓOfHom f
  rw [strHom_eq (f := f) fun _ => rfl] at hp
  have H := IsPullback.of_hasPullback f (spMap (algebraMap k (AlgebraicClosure k)))
  set π := pullback.fst f (spMap (algebraMap k (AlgebraicClosure k)))
  set f' := pullback.snd f (spMap (algebraMap k (AlgebraicClosure k)))
  letI := algebraΓOfHom f'
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hp
  have : IsIntegralHom (spMap (algebraMap k (AlgebraicClosure k))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have : IsIntegralHom π := MorphismProperty.of_isPullback (P := @IsIntegralHom) H.flip this
  have : IsProper (strHom k (X := X)) := by rwa [strHom_eq (f := f) fun _ => rfl]
  refine ⟨_, algebraΓOfHom f', π, ?_, ?_, fun L h => ?_, fun L hL => ?_, fun d L hL => ?_⟩
  · rw [strHom_eq (f := f') fun _ => rfl]
    exact PosBaseChange.isProjOver_of_isPullback H hp
  · exact (dim_le_of_isIntegralHom π).antisymm
      (PosBaseChange.dim_le_of_isClosedMap π.isClosedMap (PosBaseChange.surjective_proj H))
  · exact PosBaseChange.isNef_pull h hA (hA.pull_of_isAffineHom π) π π.isClosedMap
  · exact FieldChangeInter.hdim_pull H hL 0
  · exact FieldChangeInter.interNum_pull H hL

section AnyField

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {D : ℕ}

theorem NefProductNonneg.interNum_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {N : Fin D → LB X} (hN : ∀ i, IsNef k (N i)) :
    0 ≤ interNum k (structureModule X) N := by
  obtain ⟨X', _, π, hp', hd, hn, -, hi⟩ := exists_algClosed_baseChange hp
  rw [← hi D N fun i => (hN i).isLB]
  exact h _ X' D hp' (hd.trans hD) _ fun i => hn _ (hN i)

theorem NefRiemannRoch.isBigO (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1) := by
  obtain ⟨X', _, π, hp', hd, hn, h0, hi⟩ := exists_algClosed_baseChange hp
  have hL' := LB.isLB_pull hL.isLB π
  refine (h _ X' D hp' (hd.trans hD) _ (hn _ hL)).congr_left fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL.1 m) π)
    (by exact (cls_eq_iff _ _).2 (lbIso_lbPow_pull hL.1 π m)),
    h0 _ (isLB_lbPow hL.1 m), topSelf_def, hi D (fun _ => L) fun _ => hL.1, topSelf_def]

theorem NefRiemannRoch.tendsto (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    Tendsto (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) / (m : ℝ) ^ D) atTop
      (nhds ((topSelfIntersection k L D : ℝ) / D.factorial)) := by
  have ho : (fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ D := by
    refine (isLittleO_iff_tendsto' ?_).2 ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_)
    · filter_upwards [eventually_gt_atTop 0] with m hm h0
      exact absurd h0 (by positivity)
    · filter_upwards [eventually_gt_atTop 0] with m hm
      have : (m : ℝ) ≠ 0 := by positivity
      rw [zpow_sub_one₀ this, zpow_natCast]
      field_simp
  have ht := ((h.isBigO hp hD hL).trans_isLittleO ho).tendsto_div_nhds_zero.add_const
    ((topSelfIntersection k L D : ℝ) / D.factorial)
  rw [zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem NefRiemannRoch.topSelf_nonneg (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) : 0 ≤ topSelfIntersection k L D := by
  have h0 := ge_of_tendsto' (h.tendsto hp hD hL) fun m => (by positivity : (0 : ℝ) ≤ _)
  have hf : (0 : ℝ) < D.factorial := by positivity
  exact_mod_cast (div_nonneg_iff.1 h0).elim And.left fun h' => absurd h'.2 hf.not_ge

theorem NefRiemannRoch.isBig_iff (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    IsBig k L ↔ 0 < topSelfIntersection k L D := by
  have ht := h.tendsto hp hD hL
  have hf : (0 : ℝ) < D.factorial := by positivity
  rw [GlobalTheory.isBig_iff (algebraMap_eq_strHom k X) hp hD, ← Int.cast_pos (R := ℝ),
    ← div_pos_iff_of_pos_right hf]
  refine ⟨fun ⟨_, c, hc, hm⟩ => hc.trans_le (ge_of_tendsto_of_frequently ht
    ((hm.and_eventually (eventually_gt_atTop 0)).mono fun m hm => ?_)),
    fun ha => ⟨hL.isLB, _, half_pos ha, Eventually.frequently ?_⟩⟩
  · have := hm.2
    exact (le_div_iff₀ (by positivity)).2 hm.1
  · filter_upwards [ht.eventually_const_le (half_lt_self ha), eventually_gt_atTop 0] with m h₁ h₂
    exact (le_div_iff₀ (by positivity)).1 h₁

end AnyField

theorem NefRiemannRoch.nefBigIff (h : NefRiemannRoch) : NefBigIff :=
  fun _ _ _ _ _ _ _ hp hD _ hL => h.isBig_iff hp hD hL


end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.Published.ChernDegreeComplexModel

variable (Y : Var ℂ)

theorem integrable {L : LB Y.X} (φ : Weight Y.str (RingHom.id ℂ) L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) := by
  have : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  let R := AnRead.all Y.str (RingHom.id ℂ) Y.dim
  have hs : φ.IsSmooth R := (Weight.isCInf_iff_isSmooth R).1 h
  have hm := ReciprocityTheory.AnForm.M.mIntegrableCont R.finAtlas (fun _ => φ.locPot)
    (fun _ => Weight.isPotential_locPot hs) (fun _ => 1) continuous_const
  exact ((Weight.chernInt_eq_mInt R h measurable_const).1).2 hm

end GlobalTheory.Published.ChernDegreeComplexModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k}

theorem refines_pull_pull (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = t)
    (h : (g ≫ f) ≫ p = t) :
    Refines ((L.pull f hf).pull g hg) (L.pull (g ≫ f) h) (fun c => c PUnit.unit) 0 := by
  refine ⟨fun c y hy => mem_iInter.2 fun a => mem_iInter.1 (mem_iInter.1 hy PUnit.unit) a, ?_, ?_⟩
  · intro W r z c c' hc hc'
    have h₁ := mem_iInter.1 hc PUnit.unit
    have h₂ := mem_iInter.1 hc' PUnit.unit
    refine (gm_pull_g _ g r z c c' hc hc').trans ((gm_pull_g _ f (r ≫ g) z _ _ h₁ h₂).trans ?_)
    refine Eq.trans ?_ (gm_pull_g _ (g ≫ f) r z (c PUnit.unit) (c' PUnit.unit)
      (mem_iInter.2 fun a => mem_iInter.1 h₁ a) (mem_iInter.2 fun a => mem_iInter.1 h₂ a)).symm
    rw [Category.assoc]
  · intro σ c y hy
    refine (((L.pull f hf).φ σ).pull_φ g hg c y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
    refine Eq.trans ?_ (((L.φ σ).pull_φ (g ≫ f) h (c PUnit.unit) y).symm.trans (add_zero _).symm)
    exact congrArg _ (Subtype.ext (Category.assoc _ _ _))

theorem refines_pull_comp (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = t)
    (h : (g ≫ f) ≫ p = t) :
    Refines (L.pull (g ≫ f) h) ((L.pull f hf).pull g hg) (fun c _ => c) 0 := by
  refine ⟨fun c y hy => mem_iInter.2 fun _ => mem_iInter.2 fun a => mem_iInter.1 hy a, ?_, ?_⟩
  · intro W r z c c' hc hc'
    have h₁ : (r ≫ g) z ∈ (L.B.pull f).U c := mem_iInter.2 fun a => mem_iInter.1 hc a
    have h₂ : (r ≫ g) z ∈ (L.B.pull f).U c' := mem_iInter.2 fun a => mem_iInter.1 hc' a
    have h₃ : r z ∈ ((L.B.pull f).pull g).U fun _ => c := mem_iInter.2 fun _ => h₁
    have h₄ : r z ∈ ((L.B.pull f).pull g).U fun _ => c' := mem_iInter.2 fun _ => h₂
    have e₁ := gm_pull_g (L.B.pull f) g r z (fun _ => c) (fun _ => c') h₃ h₄
    have e₂ := gm_pull_g L.B f (r ≫ g) z c c' h₁ h₂
    have e₃ := gm_pull_g L.B (g ≫ f) r z c c' hc hc'
    rw [← Category.assoc] at e₃
    exact e₃.trans (e₁.trans e₂).symm
  · intro σ c y hy
    refine ((L.φ σ).pull_φ (g ≫ f) h c y).trans (Eq.symm ((add_zero _).trans ?_))
    refine (((L.pull f hf).φ σ).pull_φ g hg (fun _ => c) y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
    exact congrArg _ (Subtype.ext (Category.assoc _ _ _))

variable {L : HermLB p} {h : X → ℝ} {D : ℕ}

theorem IsArithHeight.restrict (hX : IsArithVar p D) (H : L.IsArithHeight h) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q) : (L.pull i hi).IsArithHeight fun y => h (i y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z j _ _ κ _ _ _ d hd
    exact (H.vertical Z (j ≫ i) κ d hd).trans (congrArg (fun n : ℤ => (n : ℝ) * _)
      (topSelf_congr κ (L.restr (j ≫ i)).isLB ((L.pull i hi).restr j).isLB
        (L.refines_pull_comp i hi j rfl (by rw [Category.assoc, hi])).lbIso d))
  · intro Z j _ _ _ hc hd r hr
    have key (t : Z ⟶ Sp k) (ht : (j ≫ i) ≫ p = t) (r) (hr : IsRatSec (L.pull (j ≫ i) ht).B r) :
        h (i (j (genericPoint Z))) = (L.pull (j ≫ i) ht).curveDeg hr ∧ IsArithVar t 0 := by
      subst ht
      exact ⟨H.point Z (j ≫ i) hc hd r hr, hX.of_isClosedImmersion (j ≫ i) hc hd⟩
    have e : (j ≫ i) ≫ p = j ≫ q := by rw [Category.assoc, hi]
    have h' := L.refines_pull_comp i hi j rfl e
    obtain ⟨h₁, h₂⟩ := key _ e _ (h'.isRatSec hr)
    refine h₁.trans ?_
    rw [HermLB.curveDeg, HermLB.curveDeg, h'.div hr]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h'.logNorm hr (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint h₂ y]
    exact CartierDiv.genericPoint_notMem_supp _
  · intro Z j _ _ _ hc e he hd m r hr
    have key (t : Z ⟶ Sp k) (ht : (j ≫ i) ≫ p = t) (r) (hr : IsRatSec ((L.pull (j ≫ i) ht).pow m).B r) :
        (L.pull (j ≫ i) ht).ArchIntegrable ((L.pull (j ≫ i) ht).pow m) e hr ∧
        m * h (i (j (genericPoint Z))) =
          ∑ᶠ z, ((((L.pull (j ≫ i) ht).pow m).div hr).mult z : ℝ) * h (i (j z)) -
            (L.pull (j ≫ i) ht).archInt ((L.pull (j ≫ i) ht).pow m) e hr := by
      subst ht
      exact H.recursion Z (j ≫ i) hc e he hd m r hr
    have e' : (j ≫ i) ≫ p = j ≫ q := by rw [Category.assoc, hi]
    let N := L.pull (j ≫ i) e'
    let M := (L.pull i hi).restr j
    have h' : Refines N M (fun c _ => c) 0 := L.refines_pull_comp i hi j rfl e'
    have h'' : Refines (N.pow m) (M.pow m) (fun c a _ => c a) 0 := by
      refine ⟨fun c y hy => mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hy a), ?_, ?_⟩
      · intro W s z c c' hc hc'
        rw [gm_pow N m s z c c' hc hc',
          gm_pow M m s z _ _ (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hc a))
            (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hc' a)),
          h'.g W s z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit)]
      · intro σ c y hy
        exact ((N.φ σ).zpow_φ m c y).trans
          ((congrArg _ ((h'.φ σ _ _ (mem_pow_iff.1 hy)).trans (add_zero _))).trans
            (((M.φ σ).zpow_φ m (fun a _ => c a) y).symm.trans (add_zero _).symm))
    obtain ⟨h₁, h₂⟩ := key _ e' _ (h''.isRatSec hr)
    change N.ArchIntegrable (N.pow m) e (h''.isRatSec hr) at h₁
    unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [h'.chernPart] at h₁
    refine ⟨fun σ => Weight.ChernIntegrableOn.congr (h₁ σ) (isOpen_offSupp _).measurableSet
      fun y hy => h''.logNorm hr hy, h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
    rw [h'.chernInt]
    exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h''.logNorm hr hy

theorem IsArithHeight.isSelfInter_restrict (hX : IsArithVar p D) (H : L.IsArithHeight h) [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ p = q) : (L.pull i hi).IsSelfInter (h (i (genericPoint Y))) :=
  ⟨_, H.restrict hX i hi, rfl⟩

end GlobalTheory.HermLB

namespace GlobalTheory.Published

def HeightProjection : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D e : ℕ),
    IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
      topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) →
      π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h →
        (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))

def CycleHeights : Prop := ArExists ∧ ArMix ∧ HeightProjection

theorem residueDegree_of_isClosedImmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have h : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective _, fun a => by
      obtain ⟨b, rfl⟩ := X.residue_surjective x a
      obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
      exact ⟨Y.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩⟩
  exact (LinearEquiv.ofBijective (Algebra.linearMap _ _) h).finrank_eq.symm.trans (CommSemiring.finrank_self _)

theorem heightProjection_of_arProj (H : ArProj) : HeightProjection := by
  intro k _ X Y _ p q D e hX hY π hπ hd hm L h hh
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (π (genericPoint Y))
  have hr : range i = closure {π (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ Z, g ≫ i = π := ⟨inv (Limits.pullback.snd i π) ≫ Limits.pullback.fst i π, by
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint Z := i.isClosedEmbedding.injective hi.symm
  have hdeg : (g ≫ i).residueDegree (genericPoint Y) = g.residueDegree (genericPoint Y) := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion i, one_mul]
  have hc : CharZero Γ(Z, ⊤) := have := hY.charZero; g.appTop.hom.charZero
  have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc
    ((topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr).symm.trans hd)
  have hq : g ≫ i ≫ p = q := (Category.assoc _ _ _).symm.trans hπ
  obtain ⟨f, hf, e₁⟩ := (H k Z Y (i ≫ p) q e hZ hY g hq hg (hdeg ▸ hm)).1 _ _ (hh.isSelfInter_restrict hX i rfl)
  refine ⟨f, ?_, by rw [e₁, hdeg, hi]⟩
  let N := (L.pull i rfl).pull g hq
  let M := L.pull (g ≫ i) hπ
  have hRef : Refines N M (fun c => c PUnit.unit) 0 := L.refines_pull_pull i rfl g hq hπ
  have pullRefines (W : Scheme.{0}) (j : W ⟶ Y) :
      Refines (N.restr j) (M.restr j) (fun c a => c a PUnit.unit) 0 := by
    refine ⟨fun c y hy => mem_iInter.2 fun a => hRef.le _ (mem_iInter.1 hy a), ?_, ?_⟩
    · intro V s z c c' hc hc'
      refine (gm_pull_g _ j s z c c' hc hc').trans ((hRef.g V (s ≫ j) z _ _
        (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit)).trans ?_)
      exact (gm_pull_g M.B j s z (fun a => c a PUnit.unit) (fun a => c' a PUnit.unit)
        (mem_iInter.2 fun a => hRef.le _ (mem_iInter.1 hc a))
        (mem_iInter.2 fun a => hRef.le _ (mem_iInter.1 hc' a))).symm
    · intro σ c y hy
      refine ((N.φ σ).pull_φ j rfl c y).trans ((hRef.φ σ _ _
        (mem_of_mem_linComb (m := fun _ => Points.PtsOver.map j rfl _ y) (fun _ => rfl) hy PUnit.unit)).trans ?_)
      exact congrArg (· + _) ((M.φ σ).pull_φ j rfl (fun a => c a PUnit.unit) y).symm
  change M.IsArithHeight f
  refine ⟨?_, ?_, ?_⟩
  · intro W j _ _ κ _ _ _ d hd
    exact (hf.vertical W j κ d hd).trans (congrArg (fun n : ℤ => (n : ℝ) * _)
      (topSelf_congr κ (N.restr j).isLB (M.restr j).isLB (pullRefines W j).lbIso d))
  · intro W j _ _ _ hc hd r hr
    have h' := pullRefines W j
    rw [hf.point W j hc hd _ (h'.isRatSec hr), HermLB.curveDeg, HermLB.curveDeg, h'.div hr]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h'.logNorm hr (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint (hY.of_isClosedImmersion j hc hd) y]
    exact CartierDiv.genericPoint_notMem_supp _
  · intro W j _ _ _ hc d hd hdim m r hr
    have h' := pullRefines W j
    have h'' : Refines ((N.restr j).pow m) ((M.restr j).pow m) (fun c a b => c a b PUnit.unit) 0 := by
      refine ⟨fun c y hy => mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hy a), ?_, ?_⟩
      · intro V s z c c' hs hs'
        rw [gm_pow (N.restr j) m s z c c' hs hs',
          gm_pow (M.restr j) m s z _ _ (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hs a))
            (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hs' a)),
          h'.g V s z _ _ (mem_iInter.1 hs PUnit.unit) (mem_iInter.1 hs' PUnit.unit)]
      · intro σ c y hy
        exact (((N.restr j).φ σ).zpow_φ m c y).trans
          ((congrArg _ ((h'.φ σ _ _ (mem_pow_iff.1 hy)).trans (add_zero _))).trans
            ((((M.restr j).φ σ).zpow_φ m (fun a b => c a b PUnit.unit) y).symm.trans (add_zero _).symm))
    obtain ⟨h₁, h₂⟩ := hf.recursion W j hc d hd hdim m _ (h''.isRatSec hr)
    change (N.restr j).ArchIntegrable ((N.restr j).pow m) d (h''.isRatSec hr) at h₁
    unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [h'.chernPart] at h₁
    refine ⟨fun σ => Weight.ChernIntegrableOn.congr (h₁ σ) (isOpen_offSupp _).measurableSet
      fun y hy => h''.logNorm hr hy, h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
    rw [h'.chernInt]
    exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h''.logNorm hr hy

theorem cycleHeights_of_arCalc (H : ArCalc) : CycleHeights :=
  ⟨H.arExists, H.arMix, heightProjection_of_arProj H.arProj⟩

namespace CycleHeights

theorem heightProjection (H : CycleHeights) : HeightProjection := H.2.2

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D e : ℕ}

theorem existsUnique (H : CycleHeights) (hX : IsArithVar p D) (L : HermLB p) : ∃! h, L.IsArithHeight h :=
  have := hX.isIntegral
  have ⟨h, hh⟩ := (H.1 k X p D hX).1 L
  ⟨h, hh, fun _ h' => h'.unique hX hh⟩

end CycleHeights

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def WeilEisensteinSiegelConvergence : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → 2 * n < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ Φ : schwartzA θ V.rank n, Eis.CosetConv (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def WeilSiegelFormula : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → 2 * n < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∀ Φ : schwartzA θ V.rank n,
    Eis.cosetSum (P D n) (GF D n) (fun γ => (ω γ Φ).1 0) 1 =
      ⨍ q, AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν

end GlobalTheory.Published

end
end

