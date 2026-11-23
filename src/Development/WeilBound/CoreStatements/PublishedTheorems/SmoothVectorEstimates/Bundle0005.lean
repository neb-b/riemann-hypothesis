module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.GlobalFields.Adele.WeakApproxUnits

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerGLContinuity
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace CornerGLContinuity

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem glmap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (x : GL (Fin a) R) :
    GeneralLinearGroup.map (g.comp f) x = GeneralLinearGroup.map g (GeneralLinearGroup.map f x) := by
  ext i j; rfl

theorem cornerGL_blkU {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (k : ℕ) (y : UnipotentBlockColumnIndex a k k → R) :
    cornerGL a s (blkU y) = blkU fun t => s (y t) := by
  apply Units.ext
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) +
    s ((1 + posM Subtype.val y) i j) = (1 + posM Subtype.val fun t => s (y t)) i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [posM, Matrix.add_apply, Matrix.sum_apply, map_add (f := _), map_sum, Matrix.single_apply,
    apply_ite s, map_zero]
  abel

theorem cLoc_eq (w : Pl E) (x : GA E a) :
    cLoc w x = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) :=
  glmap_comp _ _ x

theorem gf_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun w => ?_)
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x i j) (H w)

theorem locGL_mul_comm {v : Pl E} (h : GL (Fin a) (v.adicCompletion E)) {k : GL (Fin a) (Af E)}
    (hk : GeneralLinearGroup.map (pLoc E v) k = 1) : locGL E a v h * k = k * locGL E a v h := by
  refine gf_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw
    rw [hk, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hw, mul_one, one_mul]

open Classical in
theorem map_pLoc_prod (g : GA E a) (v : Pl E) : ∀ l : List (Pl E), l.Nodup →
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E a w (cLoc w g)).prod =
      if v ∈ l then cLoc v g else 1
  | [], _ => by simp
  | w :: l, h => by
    rw [List.map_cons, List.prod_cons, map_mul, map_pLoc_prod g v l (List.nodup_cons.1 h).2]
    by_cases hv : v = w
    · subst hv
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 h).1, mul_one]
      simp
    · rw [pLoc_locGL_of_ne hv, one_mul]
      simp [hv]

theorem continuous_glmap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (p : R →+* S) (hp : Continuous p) :
    Continuous (GeneralLinearGroup.map (n := Fin a) p) := by
  refine Continuous.units_map _ ?_
  exact continuous_pi fun i => continuous_pi fun j => hp.comp ((continuous_apply j).comp (continuous_apply i))

theorem continuous_cornerGL' {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) :
    Continuous (cornerGL a s) := by
  refine Continuous.units_map _ ?_
  change Continuous fun x : Matrix (Fin a) (Fin a) R => 1 - matN a s 1 + matN a s x
  refine continuous_const.add ?_
  exact continuous_pi fun i => continuous_pi fun j => hs.comp ((continuous_apply j).comp (continuous_apply i))

end CornerGLContinuity

open CornerGLContinuity in
theorem standard_stabiliser_bound : G0 := by
  intro E _ _ _ a
  have hpInf : Continuous (pInf E) :=
    (continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        (continuous_apply w)).comp continuous_fst
  have hpLoc : ∀ w : Pl E, Continuous (pLoc E w) := fun w =>
    RestrictedProduct.continuous_eval (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) w
  have hfin : Continuous (finGL E a) :=
    continuous_cornerGL' _ (continuous_const.prodMk continuous_id :
      Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  have hinf : Continuous (infGL E a) :=
    continuous_cornerGL' _ ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine ⟨fun y => pInf_infGL y, fun w y => ?_, fun w u => pInf_finGL _, fun w u => ?_,
    fun w v u hvw => ?_, fun g h h1 h2 => ?_, fun g hg y => ?_, fun w g hg u => ?_,
    fun k y => cornerGL_blkU _ k y, fun w k y => ?_, fun S g => ?_, ?_, fun w => ?_, fun w => ?_, hinf⟩
  · rw [cLoc_eq, pFin_infGL, map_one]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL]
  · rw [cLoc_eq, fl, MonoidHom.comp_apply, pFin_finGL, pLoc_locGL_of_ne hvw]
  · exact ga_ext h1 (gf_ext fun w => by rw [← cLoc_eq, ← cLoc_eq]; exact h2 w)
  · have hg' : GeneralLinearGroup.map (pInf E) g = 1 := hg
    exact ga_ext (by rw [map_mul, map_mul, hg', pInf_infGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, pFin_infGL, one_mul, mul_one])
  · have hg' : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) = 1 := by
      rw [← cLoc_eq]; exact hg
    exact ga_ext (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pInf_finGL, one_mul, mul_one])
      (by rw [map_mul, map_mul, fl, MonoidHom.comp_apply, pFin_finGL]; exact (locGL_mul_comm u hg').symm)
  · rw [fl, MonoidHom.comp_apply, locGL, cornerGL_blkU, finGL, cornerGL_blkU]
  · refine ⟨infGL E a (cInf g) * finGL E a (S.toList.map fun w => locGL E a w (cLoc w g)).prod, ?_, ?_, ?_⟩
    · change GeneralLinearGroup.map (pInf E) _ = _
      rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_pos (Finset.mem_toList.2 hw)]
    · intro w hw
      rw [cLoc_eq, map_mul, map_mul, pFin_infGL, pFin_finGL, map_one, one_mul,
        map_pLoc_prod g w _ S.nodup_toList, if_neg (fun h => hw (Finset.mem_toList.1 h))]
  · exact continuous_glmap _ hpInf
  · exact continuous_glmap _ ((hpLoc w).comp continuous_snd)
  · exact hfin.comp (continuous_cornerGL' _ (CuspSub.continuous_sLoc w))

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace FiniteInfinitePlaceProduct

open Neutral.B1

variable {L : Type} [Field L] [NumberField L]

theorem loc_eq_one_of_val {ν : HChar L} {v : HeightOneSpectrum (𝓞 L)} (hu : ν.UnrAt v) (hv : ν.val v = 1)
    (x : (v.adicCompletion L)ˣ) : ν.loc v x = 1 := by
  set π := atFin v (unif v) with hπ
  have hπv : Valued.v (π : v.adicCompletion L) = WithZero.exp (-1) := unif_spec v
  have hπ1 : ν.loc v π = 1 := by rw [HChar.val_eq ν hu π (unif_spec v)]; exact hv
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n := WithZero.log (Valued.v (x : v.adicCompletion L))
  have hxv : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hy : IsUnitAt v (x * π ^ n) := by
    show Valued.v ((x * π ^ n : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπv, hxv,
      ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
    simp
  have h2 := hu _ hy
  rw [map_mul, map_zpow, hπ1, _root_.one_zpow, mul_one] at h2
  exact h2

theorem inf_eq_prod (ν : HChar L) (k : Lˣ) :
    ν.inf k = ∏ w ∈ (Finset.univ : Finset (InfinitePlace L)), ν.locInf w (atInf w k) := by
  classical
  simp only [HChar.inf, HChar.locInf, infDiag, MonoidHom.comp_apply]
  have hp : ∀ (s : Finset (InfinitePlace L)) (f : InfinitePlace L → Lˣ →* Ideles L),
      (∏ w ∈ s, f w) k = ∏ w ∈ s, f w k := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih, MonoidHom.mul_apply]
  rw [hp, map_prod]
  rfl


set_option maxHeartbeats 400000 in
theorem eq_one (ν : HChar L) (h : ∀ᶠ w in cofinite, ν.val w = 1) : ν = 1 := by
  classical
  have hνc : Continuous (ν : Ideles L →* ℂˣ) := ν.2.1
  have hfin := (GlobalTheory.Mem.UnrAe.finite_ramified ν).union (Filter.eventually_cofinite.mp h)
  set S := hfin.toFinset with hSdef
  have hS : ∀ v ∉ S, ν.UnrAt v ∧ ν.val v = 1 := by
    intro v hv
    simpa [S, not_or] using hv
  have hgood : ∀ v ∉ S, ∀ x, ν.loc v x = 1 := fun v hv x =>
    loc_eq_one_of_val (hS v hv).1 (hS v hv).2 x
  have hprod : ∀ k : Lˣ, ν.inf k * ∏ v ∈ S, ν.locK v k = 1 := by
    intro k
    have h0 : (ν.inf k * ∏ v ∈ S, ν.locK v k) *
        ∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), ν.val v ^ GlobalTheory.Mem.Chr.ordF v k = 1 :=
      GlobalTheory.Mem.Chr.CharModel.productRule (ν : GlobalTheory.Mem.Chr.HChar L) S (fun v hv => (hS v hv).1) k
    have hf : ∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), ν.val v ^ GlobalTheory.Mem.Chr.ordF v k = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      rw [finprod_eq_if]
      by_cases hv : v ∈ S
      · rw [if_neg (not_not.mpr hv)]
      · rw [if_pos hv, (hS v hv).2, _root_.one_zpow]
    rw [hf, mul_one] at h0
    exact h0
  have key : ∀ p : ((v : S) → (v.1.adicCompletion L)ˣ) ×
      ((w : (Finset.univ : Finset (InfinitePlace L))) → (w.1.Completion)ˣ),
      (∏ v : S, ν.loc v.1 (p.1 v)) *
        ∏ w : (Finset.univ : Finset (InfinitePlace L)), ν.locInf w.1 (p.2 w) = 1 := by
    have hc : Continuous fun p : ((v : S) → (v.1.adicCompletion L)ˣ) ×
        ((w : (Finset.univ : Finset (InfinitePlace L))) → (w.1.Completion)ˣ) =>
        (∏ v : S, ν.loc v.1 (p.1 v)) *
          ∏ w : (Finset.univ : Finset (InfinitePlace L)), ν.locInf w.1 (p.2 w) := by
      apply Continuous.mul
      · apply continuous_finsetProd
        intro v _
        exact (hνc.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele v.1)).comp
          ((continuous_apply v).comp continuous_fst)
      · apply continuous_finsetProd
        intro w _
        exact (hνc.comp (GlobalTheory.InfTypeLocal.continuous_infIdele L w.1)).comp
          ((continuous_apply w).comp continuous_snd)
    have hd := GroundTheory.Global.denseRange_units_prod_pi S (Finset.univ : Finset (InfinitePlace L))
    intro p
    refine hd.induction_on p (isClosed_eq hc continuous_const) (fun k => ?_)
    beta_reduce
    have e1 : (∏ v : S, ν.loc v.1 (Units.map ↑(algebraMap L (v.1.adicCompletion L)) k)) =
        ∏ v ∈ S, ν.locK v k := Finset.prod_coe_sort S (fun v => ν.locK v k)
    have e2 : (∏ w : (Finset.univ : Finset (InfinitePlace L)),
        ν.locInf w.1 (Units.map ↑(algebraMap L w.1.Completion) k)) = ν.inf k := by
      rw [inf_eq_prod]
      exact Finset.prod_coe_sort _ (fun w => ν.locInf w (atInf w k))
    exact (congrArg₂ (· * ·) e1 e2).trans (by rw [mul_comm]; exact hprod k)
  have hlocS : ∀ v ∈ S, ∀ x, ν.loc v x = 1 := by
    intro v hv x
    have h0 := key (Pi.mulSingle ⟨v, hv⟩ x, 1)
    dsimp only at h0
    rw [Fintype.prod_eq_single ⟨v, hv⟩ (fun v' hne => by rw [Pi.mulSingle_eq_of_ne hne, map_one]),
      Pi.mulSingle_eq_same] at h0
    simpa using h0
  have hinf : ∀ w x, ν.locInf w x = 1 := by
    intro w x
    have h0 := key (1, Pi.mulSingle ⟨w, Finset.mem_univ w⟩ x)
    dsimp only at h0
    rw [Fintype.prod_eq_single (⟨w, Finset.mem_univ w⟩ : (Finset.univ : Finset (InfinitePlace L)))
      (fun w' hne => by rw [Pi.mulSingle_eq_of_ne hne, map_one]), Pi.mulSingle_eq_same] at h0
    simpa using h0
  have hall := GlobalTheory.Mem.Chr.Determ.eq_one_of_components (ψ := (ν : Ideles L →* ℂˣ)) hνc
    (fun v k => by
      by_cases hv : v ∈ S
      · exact hlocS v hv _
      · exact hgood v hv _)
    (fun k => by
      have h0 := inf_eq_prod ν k
      rw [Finset.prod_eq_one (fun w _ => hinf w _)] at h0
      exact h0)
  exact Subtype.ext (MonoidHom.ext fun a => by rw [hall a]; rfl)

end FiniteInfinitePlaceProduct

theorem finite_infinite_product_eq_one : HeckeCharacterRigidity := by
  intro E _ _ _ ω ω' h
  have h1 := FiniteInfinitePlaceProduct.eq_one (ω * ω'⁻¹) (h.mono fun w hw => by
    rw [HChar.val_mul, HChar.val_inv, hw, mul_inv_cancel])
  exact mul_inv_eq_one.1 h1

end PositivityTheory.jumpWindows

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GeneralLinearEntryConvergence
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace GeneralLinearEntryConvergence

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem tendsto_af {ι : Type} {l : Filter ι} (x : Af E) (z : ι → Af E)
    (h1 : ∀ w : Pl E, ∀ᶠ t in l, z t w = x w)
    (h2 : ∀ᶠ t in l, ∀ w : Pl E, z t w - x w ∈ w.adicCompletionIntegers E) :
    Tendsto z l (𝓝 x) := by
  classical
  let A : ∀ w : Pl E, Set (w.adicCompletion E) := fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))
  let sm : (∀ w : Pl E, A w) → Af E := fun y =>
    RestrictedProduct.structureMap (fun w : Pl E => w.adicCompletion E) A cofinite y
  have hsm : Continuous sm :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun w : Pl E => w.adicCompletion E) (A := A)
      (𝓕 := cofinite)).continuous
  let u0 : ∀ w : Pl E, A w := fun w => ⟨0, zero_mem (w.adicCompletionIntegers E)⟩
  let u : ι → ∀ w : Pl E, A w := fun t w =>
    if h : z t w - x w ∈ w.adicCompletionIntegers E then ⟨_, h⟩ else u0 w
  have hu : Tendsto u l (𝓝 u0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1 w] with t ht
    have h0 : z t w - x w ∈ w.adicCompletionIntegers E := by
      rw [ht, sub_self]; exact zero_mem _
    simp only [u, dif_pos h0]
    apply Subtype.ext
    change (0 : w.adicCompletion E) = z t w - x w
    rw [ht, sub_self]
  have hv : Tendsto (fun t => sm (u t)) l (𝓝 (sm u0)) := (hsm.tendsto u0).comp hu
  have e0 : sm u0 = 0 := by
    ext w
    rfl
  rw [e0] at hv
  have hv' : Tendsto (fun t => z t - x) l (𝓝 0) := by
    refine hv.congr' ?_
    filter_upwards [h2] with t ht
    apply Subtype.ext
    funext w
    change (u t w : w.adicCompletion E) = z t w - x w
    simp only [u, dif_pos (ht w)]
  have := (tendsto_const_nhds (x := x)).add hv'
  simpa using this

theorem tendsto_ad {ι : Type} {l : Filter ι} (y : Ad E) (z : ι → Ad E) (h1 : ∀ t, (z t).1 = y.1)
    (h2 : Tendsto (fun t => (z t).2) l (𝓝 y.2)) : Tendsto z l (𝓝 y) := by
  refine (Prod.tendsto_iff _ _).2 ⟨?_, h2⟩
  simp only [h1]
  exact tendsto_const_nhds

theorem tendsto_gl {ι : Type} {l : Filter ι} (x : GA E a) (z : ι → GA E a)
    (h1 : ∀ i j, Tendsto (fun t => (z t).val i j) l (𝓝 (x.val i j)))
    (h2 : ∀ i j, Tendsto (fun t => (z t)⁻¹.val i j) l (𝓝 (x⁻¹.val i j))) : Tendsto z l (𝓝 x) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine Tendsto.prodMk_nhds ?_ ?_
  · exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h1 i j
  · exact (MulOpposite.continuous_op.tendsto _).comp
      (tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => h2 i j)

variable [_root_.NumberField.IsTotallyComplex E]

theorem tendsto_entry (S : Finset (Pl E)) (x : GA E a) (z : Finset (Pl E) → GA E a)
    (hinf : ∀ T, cInf (z T) = cInf x) (hloc : ∀ T w, (w ∈ S ∨ w ∈ T) → cLoc w (z T) = cLoc w x)
    (hone : ∀ T w, w ∉ S → w ∉ T → cLoc w (z T) = 1) (i j : Fin a) :
    Tendsto (fun T => (z T).val i j) atTop (𝓝 (x.val i j)) := by
  classical
  refine tendsto_ad _ _ (fun T => ?_) (tendsto_af _ _ (fun w => ?_) ?_)
  · have h := congrArg (fun m : GL (Fin a) (Cinf E) => m.val i j) (hinf T)
    exact (infEq E).symm.injective h
  · filter_upwards [eventually_ge_atTop {w}] with T hT
    exact congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j)
      (hloc T w (Or.inr (hT (Finset.mem_singleton_self w))))
  · have hx : ∀ᶠ w in cofinite, (x.val i j).2 w ∈ w.adicCompletionIntegers E := (x.val i j).2.2
    set F := (Filter.eventually_cofinite.1 hx).toFinset
    filter_upwards [eventually_ge_atTop F] with T hT w
    by_cases hw : w ∈ S ∨ w ∈ T
    · have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hloc T w hw)
      change ((z T).val i j).2 w = (x.val i j).2 w at h
      rw [h, sub_self]
      exact zero_mem _
    · rw [not_or] at hw
      have h := congrArg (fun m : GL (Fin a) (w.adicCompletion E) => m.val i j) (hone T w hw.1 hw.2)
      change ((z T).val i j).2 w = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j at h
      have hwF : w ∉ F := fun h' => hw.2 (hT h')
      have hxw : (x.val i j).2 w ∈ w.adicCompletionIntegers E := by
        by_contra hc
        exact hwF ((Filter.eventually_cofinite.1 hx).mem_toFinset.2 hc)
      refine sub_mem ?_ hxw
      rw [h, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _

theorem step1 (hG : G0) (S : Finset (Pl E)) (f : GA E a → ℂ)
    (hf : ∀ w, w ∉ S → ∀ h, cLoc w h = 1 → f h = 0 → ∀ u, f (h * fl a w u) = 0)
    (g g₀ : GA E a) (hinf : cInf g₀ = cInf g) (hS : ∀ w ∈ S, cLoc w g₀ = cLoc w g) (hIn : InS S g₀)
    (h0 : f g₀ = 0) (T : Finset (Pl E)) :
    ∃ h : GA E a, f h = 0 ∧ cInf h = cInf g ∧ (∀ w, (w ∈ S ∨ w ∈ T) → cLoc w h = cLoc w g) ∧
      (∀ w, w ∉ S → w ∉ T → cLoc w h = 1) := by
  classical
  obtain ⟨-, -, h3, h4, h5, -⟩ := hG E a
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨g₀, h0, hinf, fun w hw => ?_, fun w hw _ => hIn w hw⟩
    rcases hw with hw | hw
    · exact hS w hw
    · simp at hw
  | insert w T hwT ih =>
    obtain ⟨h, hf0, hi, hl, ho⟩ := ih
    by_cases hwS : w ∈ S
    · refine ⟨h, hf0, hi, fun v hv => ?_, fun v hv hv' => ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')⟩
      rcases hv with hv | hv
      · exact hl v (Or.inl hv)
      · rcases Finset.mem_insert.1 hv with rfl | hv
        · exact hl v (Or.inl hwS)
        · exact hl v (Or.inr hv)
    · refine ⟨h * fl a w (cLoc w g), hf w hwS h (ho w hwS hwT) hf0 _, ?_, fun v hv => ?_, fun v hv hv' => ?_⟩
      · rw [map_mul, h3, mul_one, hi]
      · rw [map_mul]
        by_cases hvw : v = w
        · subst hvw
          rw [h4, ho v hwS hwT, one_mul]
        · rw [h5 _ _ _ hvw, mul_one]
          rcases hv with hv | hv
          · exact hl v (Or.inl hv)
          · exact hl v (Or.inr ((Finset.mem_insert.1 hv).resolve_left hvw))
      · have hvw : v ≠ w := fun e => hv' (e ▸ Finset.mem_insert_self w T)
        rw [map_mul, h5 _ _ _ hvw, mul_one]
        exact ho v hv fun h' => hv' (Finset.mem_insert_of_mem h')

end GeneralLinearEntryConvergence

open GeneralLinearEntryConvergence in
theorem convergence_entries_general_linear : G0 → PlacewiseToOutsideS := by
  intro hG E _ _ _ a S f hfc hf g g₀ hinf hS hIn h0
  choose H hH using step1 hG S f hf g g₀ hinf hS hIn h0
  have hT : Tendsto H atTop (𝓝 g) := by
    refine tendsto_gl g H (tendsto_entry S g H (fun T => (hH T).2.1) (fun T => (hH T).2.2.1)
      (fun T => (hH T).2.2.2)) (tendsto_entry S g⁻¹ (fun T => (H T)⁻¹) (fun T => ?_) (fun T w hw => ?_)
      (fun T w hw hw' => ?_))
    · rw [map_inv, map_inv, (hH T).2.1]
    · rw [map_inv, map_inv, (hH T).2.2.1 w hw]
    · rw [map_inv, (hH T).2.2.2 w hw hw', inv_one]
  have h1 := (hfc.tendsto g).comp hT
  have h2 : Tendsto (f ∘ H) atTop (𝓝 0) := by
    have e : f ∘ H = fun _ => 0 := funext fun T => (hH T).1
    rw [e]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end PositivityTheory.jumpWindows

end
end

