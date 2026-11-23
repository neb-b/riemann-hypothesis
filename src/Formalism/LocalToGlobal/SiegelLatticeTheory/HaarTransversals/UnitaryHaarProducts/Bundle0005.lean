module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondStd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter

namespace Formalism.L2.SG.Pf.CondStd

variable {F : Type} [Field F] [NumberField F]

theorem fin_approx (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma m hm
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - algebraMap F (Af F) ((β : F) / m)) = (m : Af F) * y := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    ring
  rw [hu.mul_left_cancel e1]
  exact hy

theorem dense_F : DenseRange (algebraMap F (Af F)) := by
  intro a
  rw [mem_closure_iff_nhds]
  intro t ht
  have hV : (fun w => a - w) ⁻¹' t ∈ 𝓝 (0 : Af F) := by
    refine (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using ht
  obtain ⟨N, hN, hNV⟩ := Formalism.L2.SG.Pf.top_nhds_basis F _ hV
  obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a
  obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma (m * N) (Nat.mul_pos hm hN)
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hcast : ((m : ℕ) : Af F) = algebraMap F (Af F) (m : F) := (map_natCast _ m).symm
  have hu : IsUnit ((m : ℕ) : Af F) := by
    rw [hcast]
    exact (isUnit_iff_ne_zero.2 hmF).map _
  have e1 : ((m : ℕ) : Af F) * (a - (N : Af F) * y) = ((m : ℕ) : Af F) * algebraMap F (Af F) ((β : F) / m) := by
    rw [mul_sub, hβ, hcast, ← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    push_cast
    ring
  have e2 := hu.mul_left_cancel e1
  refine ⟨algebraMap F (Af F) ((β : F) / m), ?_, ⟨_, rfl⟩⟩
  rw [← e2]
  exact hNV y hy

variable [IsTotallyReal F]


open Formalism.L2.SG.Pf.StdChar in
theorem eq_psiStd (ψ : AddChar (AF F) ℂ) (h1 : IsCharAF F ψ) (h2 : Formalism.L2.SG.LocVol.IsStdChar ψ) (x : AF F) :
    ψ x = psiStd F x := by
  obtain ⟨hcont, -, htriv, -⟩ := h1
  have hinf : ∀ y : Ainf F, ψ (pairA F y 0) = psiA F y := fun y => h2 y
  have hA : ∀ a : F, psiA F (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ)) := by
    intro a
    have hw : ∀ w : InfinitePlace F, InfinitePlace.Completion.extensionEmbedding w
        ((algebraMap F (Ainf F) a) w) = w.embedding a := by
      intro w
      first
        | exact InfinitePlace.Completion.extensionEmbedding_coe w a
        | exact InfinitePlace.Completion.extensionEmbedding_coe a
        | simp [InfiniteAdeleRing, AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    simp only [psiA, hw]
    first
      | rfl
      | simp [trR]
  have hsplit : ∀ z : AF F, z = pairA F z.1 0 + pairA F 0 z.2 := by
    intro z
    first
      | exact Prod.ext (add_zero _).symm (zero_add _).symm
      | (show z = (z.1 + 0, 0 + z.2); rw [add_zero, zero_add]; rfl)
      | (simp [pairA]; done)
  have hF : ∀ a : F, ψ (pairA F 0 (algebraMap F (Af F) a)) = psiFin F (algebraMap F (Af F) a) := by
    intro a
    have e2 : algebraMap F (AF F) a =
        pairA F (algebraMap F (Ainf F) a) 0 + pairA F 0 (algebraMap F (Af F) a) := by
      first
        | exact hsplit _
        | (rw [hsplit (algebraMap F (AF F) a)]; rfl)
        | simp [pairA]
    have h3 : psiA F (algebraMap F (Ainf F) a) * ψ (pairA F 0 (algebraMap F (Af F) a)) = 1 := by
      rw [← hinf, ← AddChar.map_add_eq_mul, ← e2]
      exact htriv a
    rw [psiFin_alg, Complex.exp_neg, ← hA a]
    exact eq_inv_of_mul_eq_one_right h3
  have hp : Continuous (fun z : Af F => pairA F 0 z) := by
    first
      | exact continuous_const.prodMk continuous_id
      | exact continuous_const.prod_mk continuous_id
      | (unfold pairA; fun_prop)
  have hc : Continuous (fun z : Af F => ψ (pairA F 0 z)) := hcont.comp hp
  have hcf : Continuous (psiFin F) := by
    first
      | exact continuous_psiFin F
      | exact continuous_psiFin
      | exact continuous_psiFin (F := F)
  have hfin : (fun z : Af F => ψ (pairA F 0 z)) = psiFin F :=
    (dense_F (F := F)).equalizer hc hcf (funext fun a => hF a)
  calc ψ x = ψ (pairA F x.1 0 + pairA F 0 x.2) := by rw [← hsplit x]
    _ = ψ (pairA F x.1 0) * ψ (pairA F 0 x.2) := AddChar.map_add_eq_mul ψ _ _
    _ = psiA F x.1 * psiFin F x.2 := by rw [hinf, ← congrFun hfin x.2]
    _ = psiStd F x := rfl

end Formalism.L2.SG.Pf.CondStd

namespace Formalism.L2.SG.Pf.CondStd

def LocTrDual : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v),
    (∀ y ∈ v.adicCompletionIntegers F, ∀ q : F,
        singleV F v (x * y) - algebraMap F (Af F) q ∈ Formalism.UG.intAd F → ∃ n : ℤ, Algebra.trace ℚ F q = n) ↔
      Formalism.L2.SG.LocVol.dV v * x ∈ v.adicCompletionIntegers F


open Formalism.L2.SG.Pf.StdChar in
theorem condAllTR_of (hL : LocTrDual) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (ψ : AddChar (AF F) ℂ) (h1 : IsCharAF F ψ) (h2 : Formalism.L2.SG.LocVol.IsStdChar ψ)
    (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔
      Formalism.L2.SG.LocVol.dV v * x ∈ v.adicCompletionIntegers F := by

  have htr : ∀ q : F, trR F q = ((Algebra.trace ℚ F q : ℚ) : ℝ) := by
    intro q
    have hsum : ((Algebra.trace ℚ F q : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ q := by
      have h : algebraMap ℚ ℂ (Algebra.trace ℚ F q) = ∑ σ : F →ₐ[ℚ] ℂ, σ q := by
        first
          | exact trace_eq_sum_embeddings ℂ (x := q)
          | exact trace_eq_sum_embeddings (E := ℂ) (x := q)
          | exact trace_eq_sum_embeddings ℂ q
          | exact trace_eq_sum_embeddings (L := F) ℂ
      rw [← h]
      first
        | rfl
        | (simp; done)
        | exact (eq_ratCast _ _).symm
    have hbij : Function.Bijective (fun w : InfinitePlace F => w.embedding.toRatAlgHom) := by
      constructor
      · intro w w' h
        have h' : w.embedding = w'.embedding := by
          ext z
          exact DFunLike.congr_fun h z
        rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h']
      · intro σ
        refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
        have hr : ComplexEmbedding.IsReal (InfinitePlace.mk σ.toRingHom).embedding :=
          InfinitePlace.isReal_iff.mp (IsTotallyReal.isReal _)
        have he : (InfinitePlace.mk σ.toRingHom).embedding = σ.toRingHom := by
          rcases InfinitePlace.embedding_mk_eq σ.toRingHom with h | h
          · exact h
          · rw [h] at hr ⊢
            have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ.toRingHom) =
                ComplexEmbedding.conjugate σ.toRingHom := hr
            first
              | exact ComplexEmbedding.isReal_conjugate_iff.mp hr
              | (simp only [ComplexEmbedding.conjugate, star_star] at h2; exact h2.symm)
              | (rw [star_star] at h2; exact h2.symm)
              | (have h3 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ.toRingHom) =
                    σ.toRingHom := RingHom.ext fun z => by simp [ComplexEmbedding.conjugate_coe_eq]
                 rw [h3] at h2
                 exact h2.symm)
        apply AlgHom.ext
        intro z
        show (InfinitePlace.mk σ.toRingHom).embedding z = σ z
        rw [he]
        rfl
    have hs : ∑ w : InfinitePlace F, w.embedding q = ∑ σ : F →ₐ[ℚ] ℂ, σ q :=
      Fintype.sum_bijective _ hbij _ _ (fun w => rfl)
    have hre : trR F q = (∑ w : InfinitePlace F, w.embedding q).re := by
      rw [Complex.re_sum]
      rfl
    rw [hre, hs, ← hsum]
    first
      | simp
      | exact Complex.ratCast_re _
  have hψ : ∀ z, ψ z = psiStd F z := fun z => eq_psiStd ψ h1 h2 z
  have hV : ∀ y : Fv F v, psiV F ψ v y = psiFin F (singleV F v y) := by
    intro y
    show ψ (pairA F 0 (singleV F v y)) = _
    rw [hψ]
    show psiA F 0 * psiFin F (singleV F v y) = _
    rw [psiA_zero, one_mul]
  have hint : ∀ c ∈ Formalism.UG.intAd F, psiFin F c = 1 := by
    intro c hc
    show ((AddCircle.toCircle (-((exists_psiF F).choose c)) : Circle) : ℂ) = 1
    rw [(exists_psiF F).choose_spec.1 c hc, neg_zero]
    first
      | simp
      | rw [AddCircle.toCircle_zero, Circle.coe_one]
  have hshift : ∀ (s : Af F) (q : F), s - algebraMap F (Af F) q ∈ Formalism.UG.intAd F →
      psiFin F s = Complex.exp (-(2 * Real.pi * Complex.I * ((trR F q : ℝ) : ℂ))) := by
    intro s q hq
    rw [← sub_add_cancel s (algebraMap F (Af F) q), psiFin_add, hint _ hq, one_mul, psiFin_alg]
  have hexp : ∀ t : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) = 1 ↔ ∃ n : ℤ, t = n := by
    intro t
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        first
          | exact Complex.two_pi_I_ne_zero
          | simp [Real.pi_ne_zero]
      have ht : (t : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ h2pi
        push_cast
        linear_combination -hn
      exact_mod_cast ht
    · rintro ⟨n, rfl⟩
      exact ⟨-n, by push_cast; ring⟩
  constructor
  · intro hall
    apply (hL F v x).mp
    intro y hy q hq
    have h := hall y hy
    rw [hV, hshift _ q hq, hexp] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    rw [htr] at hn
    exact_mod_cast hn
  · intro hd y hy
    rw [hV]
    obtain ⟨q, hq⟩ := fin_approx (singleV F v (x * y))
    rw [hshift _ q hq, hexp]
    obtain ⟨n, hn⟩ := (hL F v x).mpr hd y hy q hq
    exact ⟨n, by rw [htr, hn]; norm_cast⟩

end Formalism.L2.SG.Pf.CondStd
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuDefs
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def piG (v : VA X.B.I) : VA X.B.I :=
  v - ∑ a, hA X.B.I (X.f0 a) v • X.e0 a - ∑ a, hA X.B.I (X.e0 a) v • X.f0 a + hA X.B.I X.z0 v • X.z0
    - ∑ i, hA X.B.I (X.bwd i) v • X.bw i - ∑ i, hA X.B.I (X.bw i) v • X.bwd i

def ProjModG : Prop := ∀ v ∈ X.B.I.Lf, piG X v ∈ mL X.B.I X.B.g

def UnipCore : Prop :=
  ∀ κ : X.B.I.Gf, κ ∈ X.K2 → κ⁻¹ ∈ X.K2 →
  ∀ Y : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I), Y ≤ X.B.I.Lf →
    (∀ v ∈ Y, X.B.I.fmat κ *ᵥ v ∈ Y) →
    (∀ v ∈ Y, (∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v) ∧ ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) v)) ∧
      ZMod' X.B.I X.B.g (hA X.B.I X.z0 v)) →
    ∀ v ∈ Y, ((X.B.I.fmat κ - 1) ^ D.R.k) *ᵥ v ∈ mL X.B.I X.B.g

def CoreOfProj : Prop := ProjModG X → UnipCore X

def GlobalCondition (hK : X.LevelSubgroupCharacter) : Prop := LatOfLattice X u → UnipCore X → GamUnipKu X u hK

theorem gamUnipKu_of_projModG (hK : X.LevelSubgroupCharacter) (hP : ProjModG X) (hC : CoreOfProj X) (hG : GlobalCondition X u hK)
    (hL : LatOfLattice X u) : GamUnipKu X u hK :=
  hG hL (hC hP)

end Formalism.L2.SG.PoincareInHH.Cut.GU
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf
open Matrix NumberField
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatticeCoordinateLemmas

variable {D : D7} (X : HidaSetting D)

def gv (v : Fin X.B.I.n → X.B.I.E) : (VS D).V := X.bas.equivFun.symm (fun i => X.ιE (v i))

theorem crd_gv (v : Fin X.B.I.n → X.B.I.E) : X.crd (gv X v) = v := by
  funext i
  show X.ιE.symm (X.bas.repr (X.bas.equivFun.symm (fun i => X.ιE (v i))) i) = v i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]

theorem gv_crd (y : (VS D).V) : gv X (X.crd y) = y := by
  show X.bas.equivFun.symm (fun i => X.ιE (X.ιE.symm (X.bas.repr y i))) = y
  simp only [RingEquiv.apply_symm_apply, ← Module.Basis.equivFun_apply]
  exact X.bas.equivFun.symm_apply_apply y

abbrev sO' : 𝓞 X.B.I.E →+* 𝓞 D.host.E := (RingOfIntegers.mapRingEquiv X.ιE : 𝓞 X.B.I.E →+* 𝓞 D.host.E)

abbrev sE : X.B.I.E →+* D.host.E := (X.ιE : X.B.I.E →+* D.host.E)

def gvO : (Fin X.B.I.n → X.B.I.E) →ₛₗ[sO' X] (VS D).V where
  toFun := gv X
  map_add' v w := by
    show X.bas.equivFun.symm (fun i => X.ιE ((v + w) i)) =
      X.bas.equivFun.symm (fun i => X.ιE (v i)) + X.bas.equivFun.symm (fun i => X.ιE (w i))
    rw [← map_add (f := _)]
    congr 1
    funext i
    simp [map_add (f := _)]
  map_smul' c v := by
    show X.bas.equivFun.symm (fun i => X.ιE ((c • v) i)) = (sO' X c) • X.bas.equivFun.symm (fun i => X.ιE (v i))
    have hc : (sO' X c) • X.bas.equivFun.symm (fun i => X.ιE (v i)) =
        ((sO' X c : 𝓞 D.host.E) : D.host.E) • X.bas.equivFun.symm (fun i => X.ιE (v i)) :=
      (algebraMap_smul D.host.E (sO' X c) _).symm
    rw [hc, ← map_smul]
    congr 1
    funext i
    change X.ιE ((c : X.B.I.E) * v i) = X.ιE (c : X.B.I.E) * X.ιE (v i)
    exact map_mul X.ιE _ _

def gvE : (Fin X.B.I.n → X.B.I.E) →ₛₗ[sE X] (VS D).V where
  toFun := gv X
  map_add' v w := by
    show X.bas.equivFun.symm (fun i => X.ιE ((v + w) i)) =
      X.bas.equivFun.symm (fun i => X.ιE (v i)) + X.bas.equivFun.symm (fun i => X.ιE (w i))
    rw [← map_add (f := _)]
    congr 1
    funext i
    simp [map_add (f := _)]
  map_smul' c v := by
    show X.bas.equivFun.symm (fun i => X.ιE ((c • v) i)) = (sE X c) • X.bas.equivFun.symm (fun i => X.ιE (v i))
    rw [← map_smul]
    congr 1
    funext i
    change X.ιE (c * v i) = X.ιE c * X.ιE (v i)
    exact map_mul X.ιE _ _

end LatticeCoordinateLemmas


open LatticeCoordinateLemmas in
theorem latOfLattice_holds {D : D7} (X : HidaSetting D) (u : D.what₂.Word) : LatOfLattice X u := by
  intro h
  have : RingHomSurjective (sO' X) := ⟨(RingOfIntegers.mapRingEquiv X.ιE).surjective⟩
  have : RingHomSurjective (sE X) := ⟨X.ιE.surjective⟩
  let L := PIW.AdelClassFin.abelian₂ X.B.I ((h : X.B.I.Gf) * X.xu u)
  have ⟨hfg, hspan⟩ := PIW.AdelClassFin.lattice_m_is_lattice X.B.I ((h : X.B.I.Gf) * X.xu u)
  have : Submodule.IsFullLattice D.host.E (L.map (gvO X)) := by
    refine
      { toIsLattice := Submodule.IsLattice.of_fg D.host.E (hfg.map (gvO X))
        span_eq_top := ?_ }
    rw [Submodule.map_coe]
    change Submodule.span D.host.E (gvE X '' (L : Set _)) = ⊤
    rw [← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨X.crd y, gv_crd X y⟩
  refine ⟨L.map (gvO X), ?_, inferInstance⟩
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    show X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd (gv X v)) ∈ X.B.I.Lf
    rw [crd_gv]
    exact hv
  · intro hy
    exact ⟨X.crd y, hy, gv_crd X y⟩

end Formalism.L2.SG.PoincareInHH.Cut
end
end

