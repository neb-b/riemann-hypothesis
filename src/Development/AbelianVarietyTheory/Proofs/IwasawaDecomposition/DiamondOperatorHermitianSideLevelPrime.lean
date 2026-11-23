module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Dil

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem exists_of_cls_eq (S : StepLevel F E σ J T f bad) (y y' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (h : (Quotient.mk'' y' : Cls S) = Quotient.mk'' (y * δ)) :
    ∃ γ : UJ (σ : E →+* E) J, ∃ κ : S.U,
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 * y'.1 = y.1 * δ.1 * κ.1 := by
  obtain ⟨g, hg, k, hk, e⟩ := (@DoubleCoset.eq _ _ _ _ y' (y * δ)).1 h
  obtain ⟨γ, hγ, eγ⟩ := Subgroup.mem_subgroupOf.1 hg
  refine ⟨⟨γ, hγ⟩, ⟨k.1, Subgroup.mem_subgroupOf.1 hk⟩⁻¹, ?_⟩
  have e' : y.1 * δ.1 = g.1 * y'.1 * k.1 := congrArg Subtype.val e
  show bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * (k.1)⁻¹
  rw [e', eγ, mul_inv_cancel_right]

theorem dia_mul_stab (S : StepLevel F E σ J T f bad) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (hδ : IsDia S v hv k δ) (κ : S.U) :
    δ.1 * κ.1 ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb) := by
  haveI := S.Lb_fin
  refine (GlobalTheory.LatticeStabLocal.mem_stabGL_adele_iff S.Lb _).2 fun w => ?_
  rw [map_mul]
  refine mul_mem ?_ (Subgroup.mem_inf.1 (S.Uloc_lev w (((S.U_eq _).1 κ.2).2 w))).2
  by_cases hw : w = v
  · subst hw
    exact (Subgroup.mem_inf.1 hδ.2.1).2
  · rw [hδ.1 w hw]
    exact one_mem _

theorem lat_eq_of_move (S : StepLevel F E σ J T f bad) (L L' : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L')
    (y y' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      ((y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (hy' : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔
      ((y'.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : ℤ) (hδ : IsDia S v hv k δ)
    (γ : GL (Fin n) E) (κ : S.U)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * κ.1) :
    Formalism.L2.Forms.mulLat γ.1 L' = L := by
  let 𝒜 := E ⊗[F] FiniteAdeleRing (𝓞 F) F
  let 𝒮 := tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
  let ι := inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  have latS_mono_fin {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (h : Λ ≤ Λ') :
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ ≤ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ' :=
    Submodule.span_mono (Set.image_mono h)

  have latS_functional (Λ : Submodule (𝓞 E) (Fin n → E)) (f : Module.Dual E (Fin n → E))
      (hf : ∀ y ∈ Λ, f y = 0) (x : Fin n → E)
      (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : f x = 0 := by
    set c : Fin n → E := fun i => f (Pi.single i 1)
    have hfc : ∀ y : Fin n → E, f y = ∑ i, c i * y i := by
      intro y
      have hy : y = ∑ i, y i • (Pi.single i 1 : Fin n → E) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hy]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have key : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∑ i, ι (c i) * u i = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨y, hy, rfl⟩ := hu
        change ∑ i, ι (c i) * ι (y i) = 0
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [← map_mul, ← map_sum]
        rw [← hfc, hf y hy, map_zero]
      | zero => simp
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [hu, hw, add_zero]
      | smul a u _ hu =>
        have h : ∑ i, ι (c i) * (a • u) i = (a : 𝒜) * ∑ i, ι (c i) * u i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply]
          show _ * ((a : 𝒜) * u i) = _
          ring
        rw [h, hu, mul_zero]
    have h1 := key _ hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_mul, ← map_sum] at h1
    rw [← hfc] at h1
    haveI : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
      let v : HeightOneSpectrum (𝓞 F) :=
        ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)⟩
      refine ⟨⟨0, 1, fun h => ?_⟩⟩
      have h' := congrArg (evalV F v) h
      rw [map_zero, map_one] at h'
      exact zero_ne_one h'
    exact Formalism.UG.P.inclE_injective F E (FiniteAdeleRing (𝓞 F) F) (by rw [h1, map_zero])

  have latS_mem_span (Λ : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E)
      (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
      x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
    by_contra hxV
    obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxV inferInstance
    refine hfx (latS_functional Λ f (fun y hy => ?_) x hx)
    have h2 : f y ∈ (Submodule.span E (Λ : Set (Fin n → E))).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span hy)
    rw [hf] at h2
    exact (Submodule.mem_bot E).1 h2

  have latLocGlob_main (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
      (x : Fin n → E)
      (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : x ∈ Λ := by
    have hxV := latS_mem_span Λ x hx
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span E (Λ : Set (Fin n → E)))
    let b := Module.finBasis E C
    let W : Submodule (𝓞 E) (Fin n → E) :=
      Submodule.span (𝓞 E) (Set.range fun i => (b i : Fin n → E))
    let Λ' : Submodule (𝓞 E) (Fin n → E) := Λ ⊔ W
    have hfin' : Module.Finite (𝓞 E) Λ' :=
      Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp hfin).sup (Submodule.fg_span (Set.finite_range _)))
    have hV' : Submodule.span E (Λ : Set (Fin n → E)) ≤ Submodule.span E (Λ' : Set (Fin n → E)) :=
      Submodule.span_mono (fun y hy => Submodule.mem_sup_left hy)
    have hC' : C ≤ Submodule.span E (Λ' : Set (Fin n → E)) := by
      intro c hc
      have h := congrArg Subtype.val (b.sum_repr ⟨c, hc⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      rw [← h]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    have hspan' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤ := by
      rw [eq_top_iff, ← hC.sup_eq_top]
      exact sup_le hV' hC'
    have hx' : x ∈ Λ' := by
      have h := Formalism.UG.P.csGlob_one (F := F) Formalism.UG.P.csGlob_intAdApprox Λ' hfin' hspan'
      rw [← h]
      show ((1⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ι (x i)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ'
      rw [inv_one, Units.val_one, one_mulVec]
      exact latS_mono_fin le_sup_left hx
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    have hwC : w ∈ C :=
      (Submodule.span_le (p := C.restrictScalars (𝓞 E))).2 (by rintro _ ⟨i, rfl⟩; exact (b i).2) hw
    have hwV : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by
      have e : w = (y + w) - y := by abel
      rw [e]
      exact sub_mem hxV (Submodule.subset_span hy)
    have hw0 : w = 0 := Submodule.disjoint_def.1 hC.disjoint w hwV hwC
    rw [hw0, add_zero]
    exact hy

  have e1 : L = Formalism.UG.CS.globLat y.1 S.Lb :=
    by
      ext x
      change x ∈ L ↔ ((y.1)⁻¹).1 *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb
      rw [← hy]
      exact ⟨fun hx => Submodule.subset_span ⟨x, hx, rfl⟩,
        fun hx => latLocGlob_main L (Module.Finite.iff_fg.2 hL.fg) x hx⟩
  have e2 : L' = Formalism.UG.CS.globLat y'.1 S.Lb :=
    by
      ext x
      change x ∈ L' ↔ ((y'.1)⁻¹).1 *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb
      rw [← hy']
      exact ⟨fun hx => Submodule.subset_span ⟨x, hx, rfl⟩,
        fun hx => latLocGlob_main L' (Module.Finite.iff_fg.2 hL'.fg) x hx⟩
  have e3 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) S.Lb γ y'.1 (δ.1 * κ.1)⁻¹
    (inv_mem (dia_mul_stab S δ v hv k hδ κ))
  rw [he, mul_assoc y.1, mul_inv_cancel_right, ← e1, ← e2] at e3
  rw [e3]
  rfl

theorem dual_mem_loc (hJ : IsUnit J.det) (S : StepLevel F E σ J T f bad) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      ((y.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb)
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → E)
    (hz : z ∈ Formalism.L2.Forms.dualL (σ : E →+* E) J L) :
    ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
  have hG := Formalism.UG.P.csGlob_lattice (F := F) S.Lb S.Lb_fin S.Lb_span y.1
  have hLfull : Submodule.IsFullLattice E L :=
    { toIsLattice := hL
      span_eq_top := by
        rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
        intro x hx
        exact Formalism.L2.GlobalTheoryTheory.Br.latS_mem_span (F := F) L x ((hy _).2 hx) }
  have hLbfull : Submodule.IsFullLattice E S.Lb :=
    { toIsLattice := (Submodule.IsLattice.iff_fg E).mpr (Module.Finite.iff_fg.1 S.Lb_fin)
      span_eq_top := S.Lb_span }
  refine (GlobalTheory.DualCompletion.dual_move F E σ n J v L S.Lb (bc (prV (E := E) v) y.1) hJ hLfull
    hLbfull (Formalism.UG.P.afsplit_bc_mem _ _ _ _ y.2) (fun x => ?_) _).1
    (Submodule.subset_span ⟨z, hz, rfl⟩)
  rw [← map_inv]
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.rlv_yloc v y.1 hy x

theorem mulsF_dia_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (k : ℤ) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hδ : IsDia S v hv k δ) (κ : S.U) :
    GlobalTheory.LevelHecke.MulsF S v hv k (bc (prV (E := E) v) (δ.1 * κ.1)) := by
  obtain ⟨hg, hf⟩ := hδ.2.2
  have hk := ((S.U_eq _).1 κ.2).2 v
  rw [S.UlocAlt v hv] at hk
  obtain ⟨hg', hf'⟩ := (Subgroup.mem_inf.1 hk).2
  rw [map_mul]
  refine ⟨mul_mem hg hg', fun x => ?_⟩
  rw [← hf' x, ← hf ⟨_, (hg' x.1).1 x.2⟩]
  congr 2
  exact Subtype.ext (by simp only [Units.val_mul, Matrix.mulVec_mulVec])

theorem fT_move (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (k : ℤ) (y y' δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hδ : IsDia S v hv k δ)
    (γ : GL (Fin n) E) (κ : S.U)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = y.1 * δ.1 * κ.1) (z : Fin n → E)
    {R : Type} [Ring R] (φ : S.fM v hv ≃+ R)
    (hz' : ((bc (prV (E := E) v) y'.1)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hz : ((bc (prV (E := E) v) y.1)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    φ (S.fT v hv ⟨_, hz'⟩) = (k : R) * φ (S.fT v hv ⟨_, hz⟩) := by
  have e : y.1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y'.1 = δ.1 * κ.1 := by
    rw [mul_assoc, he, mul_assoc, inv_mul_cancel_left]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec v y.1 y'.1 γ z
  rw [e] at hm
  exact (GlobalTheory.LevelHecke.MovePair.mulsF_apply S v hv k _ (mulsF_dia_mul S v hv k δ hδ κ) φ _ _ hm).2 hz' hz

end Gen

section Steps

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem move_end (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a)
    (δ : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia (T.cls i hi h).lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      AdC T i hi c ((D.fm u).dil i v a c) γ.1 (T.atT.eV v).1 ∧
      Formalism.L2.Forms.mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).dil i v a c)) = clsCrd D u i hi c ∧
      ∀ (z : Formalism.L2.Forms.Ld D u i hi ((D.fm u).dil i v a c)) (z' : Formalism.L2.Forms.Ld D u i hi c), z'.1 = γ.1.1 *ᵥ z.1 →
        (D.fm u).fv i v _ ((T.lv i hi).pr v _ z) =
          (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((T.lv i hi).pr v c z') := by
  obtain ⟨γ, κ, he⟩ := exists_of_cls_eq (T.cls i hi h).lev _ _ δ ((T.val i hi h).dil v a k hk c δ hδ)
  refine ⟨γ, ⟨fun _ => ⟨κ.1, κ.2, δ.1, δ.2, hδ.1, he⟩, fun h1 h2 => by omega⟩, ?_, ?_⟩
  · exact lat_eq_of_move (T.cls i hi h).lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi c)
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ _ δ ((T.cls i hi h).y_lat c) ((T.cls i hi h).y_lat _)
      _ _ k hδ γ.1 κ he
  · rintro z ⟨w, hw⟩ e
    obtain rfl : w = γ.1.1 *ᵥ z.1 := e
    have m1 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (T.cls i hi h).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ ((T.cls i hi h).y_lat ((D.fm u).dil i v a c)) (T.atT.eV v).1 z.1 z.2
    have m2 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (T.cls i hi h).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i hi _) _ ((T.cls i hi h).y_lat c) (T.atT.eV v).1 _ hw
    have e1 := T.fv i hi h v _ z m1
    have e2 := T.fv i hi h v c ⟨_, hw⟩ m2
    have e3 := fT_move (T.cls i hi h).lev _ _ k _ _ δ hδ γ.1 κ he z.1 (T.fMe i hi h v) m1 m2
    rw [← hk]
    exact e1.trans (e3.trans (congrArg (fun t => (k : (D.mem u).A.Fv v) * t) e2.symm))


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem move_mid (T : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a)
    (δ : UPts (sigD D) (gramN D i (le_of_succ_m h2)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia (T.ch i h1 h2 (chOf i c)).lev (T.atT.eV v).1 (T.atT.eV v).2 k δ) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (le_of_succ_m h2)),
      AdC T i (le_of_succ_m h2) c ((D.fm u).dil i v a c) γ.1 (T.atT.eV v).1 ∧
      Formalism.L2.Forms.mulLat γ.1.1 (clsCrd D u i (le_of_succ_m h2) ((D.fm u).dil i v a c)) =
        clsCrd D u i (le_of_succ_m h2) c ∧
      ∀ (z : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) ((D.fm u).dil i v a c))
        (z' : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) c), z'.1 = γ.1.1 *ᵥ z.1 →
        (D.fm u).fv i v _ ((T.lvC i h1 h2).pr v _ z) =
          (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((T.lvC i h1 h2).pr v c z') := by
  have hβ : chOf i ((D.fm u).dil i v a c) = chOf i c := (T.dilC i h1 h2).ch v a c
  obtain ⟨γ, κ, he⟩ := exists_of_cls_eq (T.ch i h1 h2 (chOf i c)).lev ((T.ch i h1 h2 (chOf i c)).y ⟨c, rfl⟩)
    ((T.ch i h1 h2 (chOf i c)).y ⟨_, hβ⟩) δ ((T.dilC i h1 h2).dil v a k hk (chOf i c) ⟨c, rfl⟩ δ hδ)
  refine ⟨γ, ⟨fun h => by omega, fun _ _ => ⟨hβ, κ.1, κ.2, δ.1, δ.2, hδ.1, he⟩⟩, ?_, ?_⟩
  · exact lat_eq_of_move (T.ch i h1 h2 (chOf i c)).lev _ _ (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ c)
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ _ δ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩)
      ((T.ch i h1 h2 (chOf i c)).y_lat ⟨_, hβ⟩) _ _ k hδ γ.1 κ he
  · rintro z ⟨w, hw⟩ e
    obtain rfl : w = γ.1.1 *ᵥ z.1 := e
    have m1 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i _) (T.ch i h1 h2 (chOf i c)).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨_, hβ⟩) (T.atT.eV v).1 z.1 z.2
    have m2 := dual_mem_loc (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i _) (T.ch i h1 h2 (chOf i c)).lev _
      (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_clsCrd_lat D u i _ _) _ ((T.ch i h1 h2 (chOf i c)).y_lat ⟨c, rfl⟩) (T.atT.eV v).1 _ hw
    have e1 := T.fvC i h1 h2 v (chOf i c) ⟨_, hβ⟩ z m1
    have e2 := T.fvC i h1 h2 v (chOf i c) ⟨c, rfl⟩ ⟨_, hw⟩ m2
    have e3 := fT_move (T.ch i h1 h2 (chOf i c)).lev _ _ k _ _ δ hδ γ.1 κ he z.1 (T.fMeC i h1 h2 (chOf i c) v) m1 m2
    rw [← hk]
    exact e1.trans (e3.trans (congrArg (fun t => (k : (D.mem u).A.Fv v) * t) e2.symm))


set_option maxHeartbeats 2000000 in
theorem dilCl_of_crd (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi) (i : ℕ) (hi : i ≤ D.R.m)
    (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hl : Formalism.L2.Forms.mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).dil i v a c)) = clsCrd D u i hi c)
    (hv : ∀ (z : Formalism.L2.Forms.Ld D u i hi ((D.fm u).dil i v a c)) (z' : Formalism.L2.Forms.Ld D u i hi c), z'.1 = γ.1.1 *ᵥ z.1 →
        (D.fm u).fv i v _ ((P i hi).pr v _ z) = (a : (D.mem u).A.Fv v) * (D.fm u).fv i v c ((P i hi).pr v c z'))
    (ho : ∀ v', v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld D u i hi c) (z' : Formalism.L2.Forms.Ld D u i hi ((D.fm u).dil i v a c)),
        z.1 = γ.1.1 *ᵥ z'.1 → (D.fm u).fv i v' _ ((P i hi).pr v' _ z') = (D.fm u).fv i v' c ((P i hi).pr v' c z)) :
    DilCl A P i v a c (gx i hi γ) := by
  refine ⟨?_, fun z hz => ?_, fun v' hv' z hz => ?_⟩
  · refine Submodule.map_injective_of_injective
      (f := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E)))
      (crdN D i hi).injective ?_
    exact (lc_gmap i hi γ _).trans hl
  · rw [prH_eq A P hi, prH_eq A P hi]
    exact hv _ _ (crdN_gx i hi γ z.1)
  · rw [prH_eq A P hi, prH_eq A P hi]
    exact ho v' hv' _ _ (crdN_gx i hi γ z.1)

end Steps


set_option maxHeartbeats 4000000 in
theorem diamond_on_hermitian_side : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ) (c : ((I.rec7 l Z).mem u).C.cls i), ∃ γ, i ≤ (I.rec7 l Z).R.m → DilCl (F u).atT (F u).lv i v a c γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dil i v a c) γ v := by
  intro B X I hOk hP l Z H F hF hC u i v a c
  by_cases hi : i ≤ (I.rec7 l Z).R.m
  swap
  · exact ⟨1, fun h => absurd h hi⟩
  obtain ⟨k, hk, hE, hM⟩ := _root_.GlobalTheory.Mem.Col2.HAt.exists_isDia_steps I hOk hP l Z H F hF hC u i hi v a
  have core : ∃ γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi),
      AdC (F u) i hi c (((I.rec7 l Z).fm u).dil i v a c) γ.1 ((F u).atT.eV v).1 ∧
      Formalism.L2.Forms.mulLat γ.1.1 (clsCrd (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dil i v a c)) =
        clsCrd (I.rec7 l Z) u i hi c ∧
      ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dil i v a c))
        (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c), z'.1 = γ.1.1 *ᵥ z.1 →
        ((I.rec7 l Z).fm u).fv i v _ (((F u).lv i hi).pr v _ z) =
          (a : ((I.rec7 l Z).mem u).A.Fv v) * ((I.rec7 l Z).fm u).fv i v c (((F u).lv i hi).pr v c z') := by
    by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
    · obtain ⟨δ, hδ⟩ := hE h
      exact move_end (F u) i hi h v a c k hk δ hδ
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
      obtain ⟨δ, hδ⟩ := hM h1 h2 (H.chOf u i c)
      obtain ⟨γ, g1, g2, g3⟩ := move_mid (F u) i h1 h2 v a c k hk δ hδ
      refine ⟨γ, g1, g2, fun z z' e => ?_⟩
      have e1 := (_root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hOk hP l Z H F hF hC u i h1 h2 v _).1 z z rfl
      have e2 := (_root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hOk hP l Z H F hF hC u i h1 h2 v c).1 z' z' rfl
      have e3 := g3 z z' e
      rw [e1, e2] at e3
      exact e3
  obtain ⟨γ, g1, g2, g3⟩ := core
  exact ⟨gx i hi γ, fun _ => ⟨dilCl_of_crd (F u).atT (F u).lv i hi v a c γ g2 g3
    (fun v' hv' z z' e => _root_.GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC I hOk hP l Z H F hF hC u i hi v v' c _ γ.1 g1 hv' z z' e),
    _root_.GlobalTheory.Mem.Col2.HAt.adOf_of_adC I hOk hP l Z H F hF hC u i hi v c _ γ g1⟩⟩

end GlobalTheory.Mem.Col2.HAt.Dil
